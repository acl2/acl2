(in-package "DM")

(local (include-book "rtl/rel11/lib/top" :dir :system))

(include-book "groups")
(include-book "sym")

;; Informally, if g is a group and d is a dlist, an action of g on d is a function a: g x d -> d such that
;; for s in d and x and y in g,
;;   (1) a((e g), s) = s
;;   (2) a(x, a(y, s)) = a((op x y g), s).
;; Formally, we shall define an action to be a table, similar to the operation table of a group.  Thus,
;; a is a matrix of dimensions (order g) x (len d), with (car a) = d.

(defmacro dom (a) `(car ,a))

;; a(x, s) is computed by a table look-up:

(defund act (x s a g)
  (nth (ind s a)
       (nth (ind x g) a)))

;; The first property above is automatic:

(defthm action-identity
  (implies (member-equal s (dom a))
           (equal (act (e g) s a g)
	          s))
  :hints (("Goal" :in-theory (enable e act))))

;; Closure is established by checking every pair of group elements:

(defun acy (x l a g)
  (if (consp l)
      (if (member-equal (act x (car l) a g) (dom a))
	  (acy x (cdr l) a g)
	(list (car l)))
    ()))

(defun acxy (l a g)
  (if (consp l)
      (let ((acy (acy (car l) (dom a) a g)))
        (if acy
	    (cons (car l) acy)
	  (acxy (cdr l) a g)))
    ()))

(defun aclosedp-cex (a g) (acxy (elts g) a g))

(defun aclosedp (a g) (null (aclosedp-cex a g)))

;; Associativity is established by checking every triple of group elements:

(defun aaz (x y l a g)
  (if (consp l)
      (if (equal (act x (act y (car l) a g) a g)
                 (act (op x y g) (car l) a g))
	  (aaz x y (cdr l) a g)
	(list (car l)))
    ()))

(defun aayz (x l a g)
  (if (consp l)
      (let ((aaz (aaz x (car l) (dom a) a g)))
        (if aaz
	    (cons (car l) aaz)
	  (aayz x (cdr l) a g)))
    ()))

(defun aaxyz (l a g)
  (if (consp l)
      (let ((aayz (aayz (car l) (elts g) a g)))
        (if aayz
	    (cons (car l) aayz)
	  (aaxyz (cdr l) a g)))
    ()))

(defun aassocp-cex (a g) (aaxyz (elts g) a g))

(defun aassocp (a g) (null (aassocp-cex a g)))

(defund actionp (a g)
  (and (groupp g)
       (dlistp (dom a))
       (consp (dom a))
       (matrixp a (order g) (len (dom a)))
       (aclosedp a g)
       (aassocp a g)))

(defthm actionp-groupp
  (implies (actionp a g)
           (groupp g))
  :hints (("Goal" :in-theory (enable actionp))))

(defthm actionp-dlistp
  (implies (actionp a g)
           (dlistp (dom a)))
  :hints (("Goal" :in-theory (enable actionp))))

(defthm actionp-consp
  (implies (actionp a g)
           (consp (dom a)))
  :hints (("Goal" :in-theory (enable actionp))))

(defthm ordp-a
  (implies (actionp a g)
           (ordp (dom a) a))
  :hints (("Goal" :in-theory (enable actionp))))

;; Closure:

(local-defthm acy-0
  (implies (acy x l a g)
           (member (car (acy x l a g)) l)))

(local-defthm acy-1
  (implies (and (dlistp l)
                (acy x l a g))
           (and (member-equal (car (acy x l a g)) l)
	        (not (member-equal (act x (car (acy x l a g)) a g) (dom a))))))

(local-defthm acy-2
  (implies (and (null (acy x l a g))
                (member s l))
	   (member-equal (act x s a g) (dom a))))

(local-defthm acxy-1
  (let* ((cex (acxy l a g))
         (x (car cex))
	 (s (cadr cex)))
    (implies (and (dlistp l)
                  (dlistp (dom a))
		  cex)
            (and (member-equal x l)
	         (member-equal s (dom a))
		 (not (member-equal (act x s a g) (dom a)))))))

(local-defthm acxy-2
  (implies (and (not (acxy l a g))
                (member-equal x l)
		(member-equal s (dom a)))
	   (member-equal (act x s a g) (dom a))))

(local-defthm aclosedp-no-cex
  (implies (and (dlistp (dom a))
                (aclosedp a g)
                (in x g)
		(member-equal s (dom a)))
	   (member-equal (act x s a g) (dom a))))

(defthm action-closure
  (implies (and (actionp a g)
                (in x g)
		(member-equal s (dom a)))
	   (member-equal (act x s a g) (dom a)))
  :hints (("Goal" :in-theory (enable actionp))))

;; Converse of action-closure:

(defthmd not-aclosedp-cex
  (implies (and (dlistp (elts g))
                (dlistp (dom a))
                (not (aclosedp a g)))
           (let* ((cex (aclosedp-cex a g))
                  (x (car cex))
	          (s (cadr cex)))
             (and (in x g)
	          (member-equal s (dom a))
	          (not (member-equal (act x s a g) (dom a)))))))

(in-theory (disable aclosedp-cex))

;; Associativity:

(local-defthm aaz-0
  (implies (aaz x y l a g)
           (member-equal (car (aaz x y l a g)) l)))

(local-defthm aaz-1
  (implies (and (dlistp l)
                (aaz x y l a g))
           (and (member-equal (car (aaz x y l a g)) l)
	        (not (equal (act x (act y (car (aaz x y l a g)) a g) a g)
		            (act (op x y g) (car (aaz x y l a g)) a g))))))

(local-defthm aaz-2
  (implies (and (null (aaz x y l a g))
                (member-equal z l))
	   (equal (act x (act y z a g) a g)
		  (act (op x y g) z a g))))

(local-defthm aayz-1
  (let* ((aayz (aayz x l a g))
         (y (car aayz))
	 (s (cadr aayz)))
    (implies (and (dlistp l)
                  (sublistp l (elts g))
                  (dlistp (elts g))
                  (dlistp (dom a))
		  aayz)
             (and (member-equal y l)
	          (in s a)
		  (not (equal (act x (act y s a g) a g)
		              (act (op x y g) s a g)))))))

(local-defthm aayz-2
  (implies (and (null (aayz x l a g))
                (member-equal y l)
		(in s a))
	   (equal (act x (act y s a g) a g)
		  (act (op x y g) s a g))))

(local-defthm aaxyz-1
  (let* ((aaxyz (aaxyz l a g))
         (x (car aaxyz))
         (y (cadr aaxyz))
	 (s (caddr aaxyz)))
    (implies (and (dlistp l)
                  (dlistp (dom a))
                  (dlistp (elts g))
		  aaxyz)
            (and (member-equal x l)
	         (in y g)
	         (in s a)
		 (not (equal (act x (act y s a g) a g)
		             (act (op x y g) s a g)))))))

(local-defthm aaxyz-2
  (implies (and (dlistp l)
                (null (aaxyz l a g))
                (member-equal x l)
		(in y g)
		(in s a))
	   (equal (act x (act y s a g) a g)
		  (act (op x y g) s a g))))

(local-defthm aassocp-no-cex
  (implies (and (dlistp (elts g))
                (dlistp (dom a))
                (aassocp a g)
                (in x g)
		(in y g)
		(in s a))
	   (equal (act x (act y s a g) a g)
		  (act (op x y g) s a g))))

(defthmd action-aassoc
  (implies (and (actionp a g)                
                (in x g)
		(in y g)
		(in s a))
	   (equal (act x (act y s a g) a g)
		  (act (op x y g) s a g)))
  :hints (("Goal" :in-theory (enable actionp groupp)))) 

;; Converse of action-aassoc:

(defthmd not-aassocp-cex
  (implies (and (dlistp (elts g))
                (dlistp (dom a))
                (not (aassocp a g)))
           (let* ((cex (aassocp-cex a g))
                  (x (car cex))
	          (y (cadr cex))
	          (s (caddr cex)))
	     (and (in x g)
	          (in y g)
	          (in s a)
		  (not (equal (act x (act y s a g) a g)
		              (act (op x y g) s a g)))))))

(in-theory (disable aassocp-cex))

(defthm action-cancel
  (implies (and (actionp a g)                
                (in x g)
		(in r a)
		(in s a)
		(equal (act x r a g) (act x s a g)))
	   (equal r s))
  :rule-classes ()
  :hints (("Goal" :use ((:instance action-aassoc (x (inv x g)) (y x))
			(:instance action-aassoc (x (inv x g)) (y x) (s r))))))

;; Any group is an action of itself on its element list:

(defthm group-act
  (implies (and (groupp g)
                (in x g)
		(in s g))
	   (equal (act x s g g)
	          (op x s g)))
  :hints (("Goal" :in-theory (enable act op))))

(defthmd actionp-group
  (implies (groupp g)
	   (actionp g g))
  :hints (("Goal" :in-theory (enable groupp group-assoc actionp)
                  :use ((:instance not-aclosedp-cex (a g))
		        (:instance not-aassocp-cex (a g))))))






(encapsulate (((agrp) => *) ((aelts) => *) ((aact * *) => *))
  (local (defun agrp () '((0))))
  (local (defun aelts () (list 0)))
  (local (defun aact (x y) (+ x y)))
  (defthm groupp-grp (groupp (agrp)))
  (defthm consp-aelts (consp (aelts)))
  (defthm dlistp-aelts (dlistp (aelts)))
  ;(defthm a-non-nil (not (member-equal () (aelts))))
  (defthm a-identity
    (implies (member-equal s (aelts))
             (equal (aact (e (agrp)) s) s)))
  (defthm a-closed
    (implies (and (in x (agrp))
                  (member-equal s (aelts)))
	     (member-equal (aact x s) (aelts))))
  (defthm a-assoc
    (implies (and (in x (agrp))
                  (in y (agrp))
		  (member-equal s (aelts)))
	     (equal (aact x (aact y s))
	            (aact (op x y (agrp)) s)))))

(defun a-row (x m)
  (if (consp m)
      (cons (aact x (car m))
            (a-row x (cdr m)))
    ()))

(defun a-aux (l m)
  (if (consp l)
      (cons (a-row (car l) m)
            (a-aux (cdr l) m))
    ()))

(defun a () (a-aux (elts (agrp)) (aelts)))

(local-defthm a-row-1
  (and (true-listp (a-row x m))
       (equal (len (a-row c m)) (len m))))

(local-defthm a-row-2
  (implies (and (true-listp m)
                (sublistp m (aelts)))
           (equal (a-row (e (agrp)) m)
	          m)))

(local-defthm a-row-3
  (implies (and (natp j)
                (< j (len m)))
	   (equal (nth j (a-row x m))
	          (aact x (nth j m)))))

(local-defthm a-aux-1
  (matrixp (a-aux l m) (len l) (len m)))

(local-defthm a-aux-2
  (implies (consp l)
           (equal (car (a-aux l m))
	          (a-row (car l) m))))

(local-defthm a-aux-3
  (implies (and (natp i)
                (< i (len l)))
	   (equal (nth i (a-aux l m))
	          (a-row (nth i l) m))))

(local-defthm matrixp-a
  (matrixp (a) (order (agrp)) (len (aelts))))

(defthm aelts-elts
  (equal (dom (a))
         (aelts))
  :hints (("Goal" :use ((:instance e (g (agrp)))))))                  
	 
(defthm act-a-rewrite
  (implies (and (in x (agrp))
		(in s (a)))
           (equal (act x s (a) (agrp))
	          (aact x s)))		  
  :hints (("Goal" :in-theory (enable act)  
                  :use ((:instance e (g (agrp)))))))

(in-theory (disable a (a)))

(local-defthm aclosedp-a
  (aclosedp (a) (agrp))
  :hints (("Goal" :use ((:instance not-aclosedp-cex (a (a)) (g (agrp)))))))

(local-defthm aassocp-a
  (aassocp (a) (agrp))
  :hints (("Goal" :use ((:instance not-aassocp-cex (a (a)) (g (agrp)))))))

(defthm actionp-a
  (actionp (a) (agrp))
  :hints (("Goal" :in-theory (enable actionp)  
	   :use (matrixp-a))))

(in-theory (enable a))

(defmacro defaction (name args grp cond elts act)
  (let ((act-name (intern$ (concatenate 'string "ACT-" (symbol-name name)) "DM"))
        (name-row (intern$ (concatenate 'string (symbol-name name) "-ROW") "DM"))
	(name-aux (intern$ (concatenate 'string (symbol-name name) "-AUX") "DM"))
	(actionp-name (intern$ (concatenate 'string "ACTIONP-" (symbol-name name)) "DM"))
	(name-dom (intern$ (concatenate 'string (symbol-name name) "-DOM") "DM"))
	(name-act-rewrite (intern$ (concatenate 'string (symbol-name name) "-ACT-REWRITE") "DM"))
	(cond (if (symbolp grp) `(and (groupp ,grp) ,cond) cond))
	(args (if (symbolp grp) (append args (list grp)) args)))
    `(encapsulate ()
       (set-ignore-ok t)
       (set-irrelevant-formals-ok t)
       (defun ,act-name (x s ,@args) ,act)
       (defun ,name-row (x m ,@args)
         (if (consp m)
             (cons (,act-name x (car m) ,@args)
	           (,name-row x (cdr m) ,@args))
	   ()))
       (defun ,name-aux (l m ,@args)
         (if (consp l)
             (cons (,name-row (car l) m ,@args)
	           (,name-aux (cdr l) m ,@args))
           ()))
       (defun ,name ,args
         (,name-aux (elts ,grp) ,elts ,@args))
       (defthm ,actionp-name
         (implies ,cond (actionp (,name ,@args) ,grp))
	 :hints (("Goal" :use ((:functional-instance actionp-a
	                         (agrp (lambda () (if ,cond ,grp (agrp))))
	                         (aelts (lambda () (if ,cond ,elts (aelts))))
			         (aact (lambda (x s) (if ,cond ,act (aact x s))))
			         (a-row (lambda (x m) (if ,cond (,name-row x m ,@args) (a-row x m))))
			         (a-aux (lambda (l m) (if ,cond (,name-aux l m ,@args) (a-aux l m))))
			         (a (lambda () (if ,cond (,name ,@args) (a)))))))))
       (defthm ,name-dom
         (implies ,cond
	          (equal (dom (,name ,@args))
	                 ,elts))
	 :hints (("Goal" :use ((:functional-instance aelts-elts
	                         (agrp (lambda () (if ,cond ,grp (agrp))))
	                         (aelts (lambda () (if ,cond ,elts (aelts))))
			         (aact (lambda (x s) (if ,cond ,act (aact x s))))
			         (a-row (lambda (x m) (if ,cond (,name-row x m ,@args) (a-row x m))))
			         (a-aux (lambda (l m) (if ,cond (,name-aux l m ,@args) (a-aux l m))))
			         (a (lambda () (if ,cond (,name ,@args) (a)))))))))
       (defthm ,name-act-rewrite
         (implies (and ,cond
	               (in x ,grp)
	       	       (in s (,name ,@args)))
                  (equal (act x s (,name ,@args) ,grp)
	                 ,act))
	 :hints (("Goal" :use ((:functional-instance act-a-rewrite
	                         (agrp (lambda () (if ,cond ,grp (agrp))))
	                         (aelts (lambda () (if ,cond ,elts (aelts))))
			         (aact (lambda (x s) (if ,cond ,act (aact x s))))
			         (a-row (lambda (x m) (if ,cond (,name-row x m ,@args) (a-row x m))))
			         (a-aux (lambda (l m) (if ,cond (,name-aux l m ,@args) (a-aux l m))))
			         (a (lambda () (if ,cond (,name ,@args) (a)))))))))
      (in-theory (disable ,name)))))

;; Conjugation is another example of an action of a group on its element list: 

(defaction conjugacy () g t (elts g) (conj s x g))

;;  The above form generates 3 lemmas:

(DEFTHM ACTIONP-CONJUGACY
  (IMPLIES (AND (GROUPP G) T)
           (ACTIONP (CONJUGACY G) G)))

(DEFTHM CONJUGACY-DOM
  (IMPLIES (AND (GROUPP G) T)
           (EQUAL (DOM (CONJUGACY G))
                  (ELTS G))))

(DEFTHM CONJUGACY-ACT-REWRITE
  (IMPLIES (AND (AND (GROUPP G) T)
                (IN X G)
                (IN S (CONJUGACY G)))
           (EQUAL (ACT X S (CONJUGACY G) G)
                  (CONJ S X G))))

;; If h is a subgroup of g, then g acts on the left cosets of h:

(defthm consp-lsosets
  (implies (subgroupp h g)
           (consp (lcosets h g)))
  :hints (("Goal" :use ((:instance member-lcoset-cosets (x (e g)))))))

(defthmd equal-lcosets-iff
  (implies (and (subgroupp h g)
                (in x g)
		(in y g))
           (iff (equal (lcoset x h g) (lcoset y h g))
	        (in (op (inv x g) y g) h)))
  :hints (("Goal" :use (member-lcoset-iff equal-lcoset
                        (:instance member-self-lcoset (x y))))))

(defthm act-lcosets-e
  (implies (and (subgroupp h g)
                (member-equal s (lcosets h g)))
           (equal (lcoset (op (e g) (car s) g) h g)
                  s))
  :hints (("goal" :in-theory (enable lcosets-cars))))


(defthm act-lcosets-closed
  (implies (and (subgroupp h g)
                (in x g)
		(member-equal s (lcosets h g)))
	   (member (lcoset (op x (car s) g) h g)
	           (lcosets h g)))
  :hints (("Goal" :use ((:instance member-lcoset-cosets (x (op x (car s) g)))
                        (:instance lcosets-cars (c s))))))

(defthmd act-lcoselt-assoc-1
  (implies (and (subgroupp h g)
                (in x g)
		(in y g))
	   (equal (lcoset (op x (car (lcoset y h g)) g) h g)
	          (lcoset (op x y g) h g)))
  :hints (("Goal" :in-theory (enable lcoset-car)
                  :use ((:instance equal-lcosets-cancel (z (car (lcoset y h g))))))))

(defthm act-lcosets-assoc
  (implies (and (subgroupp h g)
                (in x g)
		(in y g)
		(member-equal s (lcosets h g)))
	   (equal (lcoset (op x (car (lcoset (op y (car s) g) h g)) g) h g)
	          (lcoset (op (op x y g) (car s) g) h g)))
  :hints (("Goal" :in-theory (enable lcosets-cars)
                  :use ((:instance act-lcoselt-assoc-1 (y (op y (car s) g)))
		        (:instance group-assoc (z (car s)))))))
                        
(defaction act-lcosets (h) g
  (subgroupp h g)
  (lcosets h g)
  (lcoset (op x (car s) g) h g))

;; (sym n) acts on (ninit n):

(defthm nth-comp-perm-rewrite
  (implies (and (posp n) (natp k) (< k n))
           (equal (nth k (comp-perm x y n))
	          (nth (nth k y) x))))

(in-theory (enable member-ninit))

;; (defaction permute (n) (sym n) (posp n) (ninit n) (nth s x))

;; Given s in the domain of an action a, the orbit of s is the ordered list of all s' in (dom a) such that
;; s' = (act x s a g) for some x in g:

(defun orbit-aux (s a g l)
  (if (consp l)
      (let ((val (act (car l) s a g))
            (res (orbit-aux s a g (cdr l))))
        (if (member-equal val res)
	    res
	  (insert val res a)))
    ()))
    
(defund orbit (s a g)
  (orbit-aux s a g (elts g)))

;; Every orbit is an ordered sublist of the domain:

(local-defthm ordp-orbit-aux
  (implies (and (actionp a g)
                (in s a)
		(sublistp l (elts g)))
	   (ordp (orbit-aux s a g l) a)))

(defthm ordp-orbit
  (implies (and (actionp a g)
                (in s a))
	   (ordp (orbit s a g) a))
  :hints (("Goal" :in-theory (enable orbit))))

(local-defthm sublistp-orbit-aux
  (implies (and (actionp a g)
		(sublistp l (elts g))
                (member-equal s (dom a)))
	   (sublistp (orbit-aux s a g l) (dom a))))

(defthm sublistp-orbit
  (implies (and (actionp a g)
                (member-equal s (dom a)))
	   (sublistp (orbit s a g) (dom a)))
  :hints (("Goal" :in-theory (enable orbit))))

;; Every orbit is a dlist:

(local-defthm dlistp-orbit-aux
  (implies (dlistp l)
	   (dlistp (orbit-aux s a g l))))

(defthm dlistp-orbit
  (implies (groupp g)
           (dlistp (orbit s a g)))
  :hints (("Goal" :in-theory (enable orbit))))

;; Every element of the domain belongs to its own orbit:

(local-defthm member-self-orbit-aux
  (implies (and (actionp a g)
                (member-equal (e g) l)
                (member-equal s (dom a)))
	   (member-equal s (orbit-aux s a g l))))

(defthm member-self-orbit
  (implies (and (actionp a g)
                (member-equal s (dom a)))
	   (member-equal s (orbit s a g)))
  :hints (("Goal" :in-theory (enable orbit))))

(local-defthm member-act-orbit-aux
  (implies (and (actionp a g)
                (member-equal x l))
	   (member-equal (act x s a g) (orbit-aux s a g l))))

(defthmd member-act-orbit
  (implies (and (actionp a g)
                (in x g))
	   (member-equal (act x s a g) (orbit s a g)))
  :hints (("Goal" :in-theory (enable orbit))))

;; If r is in the orbit of s, then for some x, (act x s a g) = r:

(defun actor-aux (r s a g l)
  (if (consp l)
      (if (equal (act (car l) s a g) r)
          (car l)
	(actor-aux r s a g (cdr l)))
    ()))

(local-defthm actor-aux-acts
  (implies (and (actionp a g)
                (member-equal r (orbit-aux s a g l)))
	   (let ((x (actor-aux r s a g l)))
	     (and (member-equal x l)
	          (equal (act x s a g) r)))))

(defund actor (r s a g)
  (actor-aux r s a g (elts g)))

(defthmd actor-acts
  (implies (and (actionp a g)
                (member-equal r (orbit s a g)))
	   (let ((x (actor r s a g)))
	     (and (in x g)
	          (equal (act x s a g) r))))
  :hints (("Goal" :in-theory (enable orbit actor))))

;; If r is in the orbit of s, then the orbit of r is a permutation of the orbit of s:

(local-defthm permp-orbit-1
  (implies (and (actionp a g)
                (member-equal s (dom a))
                (member-equal r (orbit s a g))
		(member-equal q (orbit r a g)))
	   (member-equal q (orbit s a g)))
  :hints (("Goal" :use (actor-acts
                        (:instance actor-acts (r q) (s r))
			(:instance action-aassoc (x (actor q r a g)) (y (actor r s a g)))
			(:instance member-act-orbit (x (op (actor q r a g) (actor r s a g) g)))))))

(local-defthm permp-orbit-2
  (implies (and (actionp a g)
                (member-equal s (dom a))
                (member-equal r (orbit s a g))
		(member-equal q (orbit s a g)))
	   (member-equal q (orbit r a g)))
  :hints (("Goal" :use (actor-acts
                        (:instance actor-acts (r q))
			(:instance action-aassoc (x (inv (actor r s a g) g)) (y (actor r s a g)))
			(:instance action-aassoc (x (actor q s a g)) (y (inv (actor r s a g) g)) (s r))
			(:instance member-act-orbit (x (op (actor q s a g) (inv (actor r s a g) g) g)) (s r))))))

(local-defthm permp-orbit-3
  (implies (and (actionp a g)
                (member-equal s (dom a))
                (member-equal r (dom a))
                (member-equal q (orbit s a g))
		(member-equal q (orbit r a g)))
	   (member-equal r (orbit s a g)))
  :hints (("Goal" :in-theory (disable MEMBER-ACT-ORBIT MEMBER-SELF-ORBIT)
                  :use ((:instance actor-acts (r q) (s r))
                        (:instance actor-acts (r q))
			(:instance action-aassoc (x (inv (actor q r a g) g)) (y (actor q r a g)) (s r))
			(:instance action-aassoc (x (inv (actor q r a g) g)) (y (actor q s a g)))
			(:instance member-act-orbit (x (op (inv (actor q r a g) g) (actor q s a g) g)))))))

(local-defthm permp-orbit-4
  (implies (and (actionp a g)
                (member-equal s (dom a))
                (member-equal r (orbit s a g))
		(sublistp l (orbit r a g)))
	   (sublistp l (orbit s a g))))

(local-defthm permp-orbit-5
  (implies (and (actionp a g)
                (member-equal s (dom a))
                (member-equal r (orbit s a g))
		(sublistp l (orbit s a g)))
	   (sublistp l (orbit r a g))))

(local-defthmd permp-orbit-orbit
  (implies (and (actionp a g)
                (member-equal s (dom a))
                (member-equal r (orbit s a g)))
	   (permp (orbit r a g) (orbit s a g)))
  :hints (("Goal" :in-theory (enable permp))))

;; If r is in the orbit of s, then the orbits of r and s are equal:

(defthmd equal-orbits
  (implies (and (actionp a g)
                (member-equal s (dom a))
                (member-equal r (orbit s a g)))
	   (equal (orbit r a g) (orbit s a g)))
  :hints (("Goal" :in-theory (enable permp)
                  :use (permp-orbit-orbit (:instance ordp-equal (g a) (x (orbit r a g)) (y (orbit s a g)))))))

(in-theory (disable common-member-shared))

(defthmd disjointp-orbits
  (implies (and (actionp a g)
                (member-equal s (dom a))
                (member-equal r (dom a))
		(not (equal (orbit r a g) (orbit s a g))))
	   (disjointp (orbit r a g) (orbit s a g)))
  :hints (("Goal" :use (equal-orbits
                        (:instance common-member-shared (l (orbit s a g)) (m (orbit r a g)))
                        (:instance disjointp-symmetric (l (orbit s a g)) (m (orbit r a g)))))))

;; a list of the orbits of an action:

(defun orbits-aux (a g l)
  (if (consp l)
      (let ((res (orbits-aux a g (cdr l))))
	(if (member-list (car l) res)
	    res
	  (cons (orbit (car l) a g) res)))
    ()))

(defund orbits (a g)
  (orbits-aux a g (dom a)))

(local-defthm dlistp-orbits-aux
  (implies (and (actionp a g)
                (sublistp l (dom a)))
           (dlistp (orbits-aux a g l))))

(defthm dlistp-orbits
  (implies (actionp a g)
           (dlistp (orbits a g)))
  :hints (("Goal" :in-theory (enable orbits))))

(local-defthm member-list-orbits-aux
  (implies (and (actionp a g)
                (sublistp l (dom a))
		(member-equal x l))
           (member-list x (orbits-aux a g l))))

(defthm member-list-orbits
  (implies (and (actionp a g)
		(in x a))
           (member-list x (orbits a g)))
  :hints (("Goal" :in-theory (enable orbits))))

(defthmd member-orbits-aux-orbit
  (implies (and (actionp a g)
                (sublistp l (dom a))
		(member-equal x (orbits-aux a g l)))
	   (and (in (car x) a)
	        (equal (orbit (car x) a g) x)))
  :hints (("Subgoal *1/2" :in-theory (disable sublistp-orbit)
                          :use ((:instance equal-orbits (s (car l)) (r (car (orbit (car l) a g))))
			        (:instance member-self-orbit (s (car l)))
                                (:instance sublistp-orbit (s (car l)))))))

(defthmd member-orbits-orbit
  (implies (and (actionp a g)
		(member-equal x (orbits a g)))
	   (and (in (car x) a)
	        (equal (orbit (car x) a g) x)))
  :hints (("Goal" :in-theory (enable orbits)
                  :use ((:instance member-orbits-aux-orbit (l (dom a)))))))

;; Appending the orbits yields a permutation of the domain:

(local-defthm orbits-pairwise-disjoint-1
  (implies (and (actionp a g)
		(in s a)
		(sublistp l (dom a))
		(not (member-list s (orbits-aux a g l))))
	   (disjointp-list (orbit s a g) (orbits-aux a g l)))	   
  :hints (("Subgoal *1/2" :use ((:instance disjointp-orbits (r s) (s (car l)))))))

(local-defthm orbits-aux-pairwise-disjoint
  (implies (and (actionp a g)
		(sublistp l (dom a)))
	   (disjointp-pairwise (orbits-aux a g l))))

(defthm orbits-pairwise-disjoint
  (implies (actionp a g)
	   (disjointp-pairwise (orbits a g)))
  :hints (("Goal" :in-theory (enable orbits))))

(local-defthm dlistp-list-orbits-aux
  (implies (and (actionp a g)
		(sublistp l (dom a)))
	   (dlistp-list (orbits-aux a g l))))

(defthm dlistp-list-orbits
  (implies (actionp a g)
	   (dlistp-list (orbits a g)))
  :hints (("Goal" :in-theory (enable orbits))))
  
(defthm dlistp-append-list-orbits
  (implies (actionp a g)
	   (dlistp (append-list (orbits a g)))))

(local-defthm sublistp-sublist-append-list-orbits
  (implies (and (actionp a g)
		(sublistp l (dom a)))
	   (sublistp l (append-list (orbits-aux a g l)))))

(local-defthm sublistp-dom-append-list-orbits
  (implies (actionp a g)
	   (sublistp (dom a) (append-list (orbits a g))))
  :hints (("Goal" :in-theory (enable orbits))))

(local-defthm sublistp-append-list-orbits-aux-dom
  (implies (and (actionp a g)
		(sublistp l (dom a)))
	   (sublistp (append-list (orbits-aux a g l)) (dom a))))

(local-defthm sublistp-append-list-orbits-dom
  (implies (actionp a g)
	   (sublistp (append-list (orbits a g)) (dom a)))
  :hints (("Goal" :in-theory (enable orbits))))

(defthmd append-list-orbits
  (implies (actionp a g)
	   (permp (append-list (orbits a g))
		  (dom a)))
  :hints (("Goal" :in-theory (enable actionp permp))))

;; Note that the conjugacy class of x is the orbit of x under the conjugacy action:

(local-defthm conjs-orbit-1
  (implies (and (groupp g)
		(in x g)
		(member-equal y (conjs x g)))
	   (member-equal y (orbit x (conjugacy g) g)))
  :hints (("Goal" :use (conjs-conjer
			(:instance member-act-orbit (x (conjer y x g)) (s x) (a (conjugacy g)))))))

(local-defthm conjs-orbit-2
  (implies (and (groupp g)
		(in x g)
		(member-equal y (orbit x (conjugacy g) g)))
	   (member-equal y (conjs x g)))
  :hints (("Goal" :use ((:instance actor-acts (r y) (s x) (a (conjugacy g)))
			(:instance conj-in-conjs (a (actor y x (conjugacy g) g)))))))

(local-defthm conjs-orbit-3
  (implies (and (groupp g)
		(in x g)
		(sublistp l (conjs x g)))
	   (sublistp l (orbit x (conjugacy g) g))))

(local-defthm conjs-orbit-4
  (implies (and (groupp g)
		(in x g)
		(sublistp l (orbit x (conjugacy g) g)))
	   (sublistp l (conjs x g))))

(local-defthm conjs-orbit-5
  (implies (and (groupp g)
	        (ordp l (conjugacy g)))
	   (ordp l g))
  :hints (("Goal" :in-theory (enable ordp))))

(defthmd conjs-orbit
  (implies (and (groupp g)
	        (in x g))
	   (equal (conjs x g)
		  (orbit x (conjugacy g) g)))
  :hints (("Goal" :use ((:instance ordp-equal (x (conjs x g)) (y (orbit x (conjugacy g) g)))))))

;; Since (center g) consists of all orbits of length 1 and (conjs-list g) consists of all obits of
;; length > 1, the class equation could be derived from append-list orbits and conjs-orbit:

;; (defthmd class-equation
;;   (implies (groupp g)
;;            (equal (len (append (elts (center g))
;;                                (append-list (conjs-list g))))
;;                   (order g))))

;; The stabilizer of s is the ordered subgroup of g comprising all x such that (act x s a g) = s:

(defun stab-elts-aux (s a g l)
  (if (consp l)
      (if (equal (act (car l) s a g) s)
          (cons (car l) (stab-elts-aux s a g (cdr l)))
	(stab-elts-aux s a g (cdr l)))
    ()))

(defund stab-elts (s a g)
  (stab-elts-aux s a g (elts g)))

(local-defthm sublistp-stab-elts-aux
  (implies (actionp a g)
	   (sublistp (stab-elts-aux s a g l) l)))

(local-defthm ordp-stab-elts-aux
  (implies (and (groupp g)
                (ordp l g))
	   (and (ordp (stab-elts-aux s a g l) g)
	        (implies (consp (stab-elts-aux s a g l))
		         (<= (ind (car l) g)
			     (ind (car (stab-elts-aux s a g l)) g))))))

(defthm sublistp-stab-elts
  (implies (actionp a g)
	   (sublistp (stab-elts s a g) (elts g)))
  :hints (("Goal" :in-theory (enable stab-elts))))

(defthm ordp-stab-elts
  (implies (actionp a g)
	   (ordp (stab-elts s a g) g))
  :hints (("Goal" :in-theory (enable stab-elts))))

(defthm dlistp-stab-elts
  (implies (actionp a g)
	   (dlistp (stab-elts s a g)))
  :hints (("Goal" :in-theory (disable ordp-stab-elts):use (ordp-stab-elts))))

(local-defthm member-stab-elts-aux
  (implies (and (actionp a g)
		(member-equal x l))
	   (iff (member-equal x (stab-elts-aux s a g l))
	        (equal (act x s a g) s))))

(defthmd member-stab-elts
  (implies (and (actionp a g)
		(in x g))
	   (iff (member-equal x (stab-elts s a g))
	        (equal (act x s a g) s)))
  :hints (("Goal" :in-theory (enable stab-elts))))

(defthm stab-elts-closed
  (implies (and (actionp a g)
		(in s a)
		(in x g)
		(in y g)
		(member-equal x (stab-elts s a g))
		(member-equal y (stab-elts s a g)))
	   (member-equal (op x y g) (stab-elts s a g)))
  :hints (("Goal" :use (action-aassoc member-stab-elts
		        (:instance member-stab-elts (x (op x y g)))
		        (:instance member-stab-elts (x y))))))

(defthm stab-elts-inv
  (implies (and (actionp a g)
		(in s a)
		(in x g)
		(member-equal x (stab-elts s a g)))
	   (member-equal (inv x g) (stab-elts s a g)))
  :hints (("Goal" :use (action-aassoc member-stab-elts
		        (:instance member-stab-elts (x (inv x g)))
		        (:instance action-aassoc (x (inv x g)) (y x))))))

(defthm car-stab-elts
  (implies (and (actionp a g)
		(in s a))
	   (equal (car (stab-elts s a g))
	          (e g)))
  :hints (("Goal" :in-theory (enable stab-elts e)
                  :expand ((STAB-ELTS-AUX S A G (CAR G))
		           (STAB-ELTS-AUX S A G (CDR (CAR G))))
                  :use (action-identity))))

(defthm consp-stab-elts
  (implies (and (actionp a g)
		(in s a))
	   (consp (stab-elts s a g)))
  :hints (("Goal" :in-theory (enable actionp groupp e)
                  :use (car-stab-elts))))

(defsubgroup stabilizer (s a) g
  (and (actionp a g)
       (member-equal s (dom a)))
  (stab-elts s a g))

;; We shall define a bijection from (lcosets (stabilizer s a g) g) to (orbit s a g),
;; and conclude that the 2 lists have the same length:

(defund lcosets2orbit (c s a g)
  (act (car c) s a g))

;; Inverse bijection:

(defund orbit2lcosets (r s a g)
  (lcoset (actor r s a g) (stabilizer s a g) g))

(local-defthm lcosets2orbit-1
  (implies (and (actionp a g)
		(in s a)
		(member-equal c (lcosets (stabilizer s a g) g)))
           (member-equal (lcosets2orbit c s a g) (orbit s a g)))
  :hints (("Goal" :in-theory (enable lcosets2orbit)
                  :use ((:instance lcosets-cars (h (stabilizer s a g)))
		        (:instance member-act-orbit (x (car c)))))))

(local-defthm lcosets2orbit-2
  (implies (and (actionp a g)
		(in s a)
		(member-equal c (lcosets (stabilizer s a g) g)))
           (equal (act (inv (actor (act (car c) s a g) s a g) g) (act (car c) s a g) a g)
	          s))
  :hints (("Goal" :in-theory (enable lcosets2orbit)
                  :use (lcosets2orbit-1
		        (:instance actor-acts (r (act (car c) s a g)))
		        (:instance action-aassoc (x (inv (actor (act (car c) s a g) s a g) g))
			                         (y (actor (act (car c) s a g) s a g)))))))

(local-defthm lcosets2orbit-3
  (implies (and (actionp a g)
		(in s a)
		(member-equal c (lcosets (stabilizer s a g) g)))
	   (and (in (car c) g)
	        (equal (lcoset (car c) (stabilizer s a g) g) c)
	        (in (actor (act (car c) s a g) s a g) g)
                (in (op (inv (actor (act (car c) s a g) s a g) g) (car c) g)
	            (stabilizer s a g))))
  :hints (("Goal" :in-theory (enable member-stab-elts lcosets2orbit)
                  :use (lcosets2orbit-1 lcosets2orbit-2
		        (:instance lcosets-cars (h (stabilizer s a g)))
		        (:instance actor-acts (r (act (car c) s a g)))
			(:instance action-aassoc (x (inv (actor (act (car c) s a g) s a g) g))
			                         (y (car c)))))))

(defthm lcosets2orbit-1-1
  (implies (and (actionp a g)
		(in s a)
		(member-equal c (lcosets (stabilizer s a g) g)))
           (and (member-equal (lcosets2orbit c s a g) (orbit s a g))
	        (equal (orbit2lcosets (lcosets2orbit c s a g) s a g)
		       c)))
  :hints (("Goal" :in-theory (enable lcosets2orbit orbit2lcosets)
                  :use (lcosets2orbit-1 lcosets2orbit-3
		        (:instance member-lcoset-iff (x (actor (act (car c) s a g) s a g))
			                             (y (car c))
						     (h (stabilizer s a g)))
			(:instance equal-lcoset (x (actor (act (car c) s a g) s a g))
			                        (y (car c))
					        (h (stabilizer s a g)))))))

(local-defthm orbit2lcosets-1
  (implies (and (actionp a g)
		(in s a)
		(member-equal r (orbit s a g)))
           (member-equal (orbit2lcosets r s a g) (lcosets (stabilizer s a g) g)))
  :hints (("Goal" :in-theory (enable orbit2lcosets)
                  :use (actor-acts))))

(local-defthm orbit2lcosets-2
  (implies (and (actionp a g)
		(in s a)
		(member-equal r (orbit s a g)))
           (equal (act (op (inv (actor r s a g) g) (car (lcoset (actor r s a g) (stabilizer s a g) g)) g)
	               s a g)
	          s))
  :hints (("Goal" :in-theory (enable member-stab-elts orbit2lcosets)
                  :use (orbit2lcosets-1 actor-acts
		        (:instance member-lcoset-iff (x (actor r s a g))
			                             (y (car (lcoset (actor r s a g) (stabilizer s a g) g)))
						     (h (stabilizer s a g)))))))

(defthm orbit2lcosets-1-1
  (implies (and (actionp a g)
		(in s a)
		(member-equal r (orbit s a g)))
           (and (member-equal (orbit2lcosets r s a g) (lcosets (stabilizer s a g) g))
	        (equal (lcosets2orbit (orbit2lcosets r s a g) s a g)
		       r)))
  :hints (("Goal" :in-theory (enable member-stab-elts lcosets2orbit orbit2lcosets)
                  :use (orbit2lcosets-1 orbit2lcosets-2 actor-acts
		        (:instance action-aassoc (x (inv (actor r s a g) g))
			                         (y (car (lcoset (actor r s a g) (stabilizer s a g) g))))
			(:instance action-aassoc (y (inv (actor r s a g) g))
			                         (x (actor r s a g))
						 (s (act (car (lcoset (actor r s a g) (stabilizer s a g) g)) s a g)))))))

(defthm len-orbit-lcosets
  (implies (and (actionp a g)
		(in s a))
	   (equal (len (orbit s a g))
	          (len (lcosets (stabilizer s a g) g))))
  :hints (("Goal" :use ((:functional-instance len-1-1-equal
                         (x (lambda () (if (and (groupp g) (actionp a g) (in s a)) (orbit s a g) (x))))
                         (y (lambda () (if (and (groupp g) (actionp a g) (in s a)) (lcosets (stabilizer s a g) g) (y))))
			 (xy (lambda (r) (if (and (groupp g) (actionp a g) (in s a)) (orbit2lcosets r s a g) (xy r))))
			 (yx (lambda (c) (if (and (groupp g) (actionp a g) (in s a)) (lcosets2orbit c s a g) (yx c)))))))))

;; The following is a consequence of Lagrange's Theorem:

(defthmd stabilizer-orbit
  (implies (and (actionp a g)
		(in s a))
	   (equal (* (order (stabilizer s a g))
		     (len (orbit s a g)))
		  (order g)))
  :hints (("Goal" :use (len-orbit-lcosets
                       (:instance lagrange (h (stabilizer s a g)))))))

(defthmd len-orbit-divides
  (implies (and (actionp a g)
		(in s a))
	   (divides (len (orbit s a g))
		    (order g)))
  :hints (("Goal" :in-theory (enable divides)
                  :use (stabilizer-orbit order-pos))))

;; Note that the centralizer of x is its stabilizer under the conjugacy action:

(defthm centralizer-stabilizer-1
  (implies (and (groupp g)
		(in x g)
		(member-equal y (stab-elts x (conjugacy g) g)))
	   (member y (centizer-elts x g)))
  :hints (("Goal" :use ((:instance member-stab-elts (a (conjugacy g)) (x y) (s x))
			(:instance centralizer-conj-iff (a x) (x y))))))

(defthm centralizer-stabilizer-2
  (implies (and (groupp g)
		(in x g)
		(member-equal y (centizer-elts x g)))
	   (member y (stab-elts x (conjugacy g) g)))
  :hints (("Goal" :use ((:instance member-stab-elts (a (conjugacy g)) (x y) (s x))
			(:instance centralizer-conj-iff (a x) (x y))))))

(local-defthm centralizer-stabilizer-3
  (implies (and (groupp g)
		(in x g)
		(sublistp l (centizer-elts x g)))
	   (sublistp l (stab-elts x (conjugacy g) g))))

(local-defthm centralizer-stabilizer-4
  (implies (and (groupp g)
		(in x g)
		(sublistp l (stab-elts x (conjugacy g) g)))
	   (sublistp l (centizer-elts x g)))
  :hints (("Goal" :induct (len l))))

(local-defthmd centralizer-stabilizer-5
  (implies (and (groupp g)
		(in x g))
	    (equal (stab-elts x (conjugacy g) g)
	           (centizer-elts x g)))
  :hints (("Goal" :use ((:instance ordp-equal (x (stab-elts x (conjugacy g) g))
				              (y (centizer-elts x g)))))))

(defthmd centralizer-stabilizer
  (implies (and (groupp g)
		(in x g))
	   (equal (centralizer x g)
		  (stabilizer x (conjugacy g) g)))
  :hints (("Goal" :use (centralizer-stabilizer-5
			(:instance subgroups-equal-elts (h (centralizer x g)) (k (stabilizer x (conjugacy g) g)))))))

;; Consequently, the lemma len-conjs-cosets could be derived from conjs-orbit and stabilizer-orbit:

;; (defthm len-conjs-cosets
;;   (implies (and (groupp g) (in x g))
;;            (equal (len (conjs x g))
;; 	          (subgroup-index (centralizer x g) g))))

;; Furthermore, the class equation could be derived from 

;; A group action of g induces an action by any subgroup of g:

(encapsulate ()

(local (in-theory (enable action-aassoc)))

(defaction subaction (a g) h
  (and (actionp a g)
       (subgroupp h g))
  (dom a)
  (act x s a g))
)

(defthmd stabilizer-subaction
  (implies (and (actionp a g)
		(subgroupp h g)
		(in s a)
		(in x h))
	   (iff (in x (stabilizer s (subaction a g h) h))
	        (in x (stabilizer s a g))))
  :hints (("Goal" :use (member-stab-elts
			(:instance member-stab-elts (a (subaction a g h)) (g h))))))

;; The conjugate of a subgroup h of g by an element a of g is a subgroup comprising all conjugates
;; of elements of h by a.  We define this subgroup to have an ordered element list with respect to g,
;; so that element lists of distinct conjugate subgroups cannot be permutations of one another:

(defun conj-sub-list-aux (l a g)
  (if (consp l)
      (insert (conj (car l) a g)
              (conj-sub-list-aux (cdr l) a g)
	      g)
    ()))

(defund conj-sub-list (h a g)
  (conj-sub-list-aux (elts h) a g))

(local-defthm ordp-conj-sub-list-aux
  (implies (and (groupp g)
                (sublistp l (elts g))
		(in a g))
	   (ordp (conj-sub-list-aux l a g) g)))

(local-defthm sublistp-conj-sub-list-aux
  (implies (and (groupp g)
                (sublistp l (elts g))
		(in a g))
	   (sublistp (conj-sub-list-aux l a g) (elts g))))

(local-defthm member-conj-sub-list-aux
  (implies (and (groupp g)
                (sublistp l (elts g))
		(in a g)
		(in x g))
	   (iff (member-equal x (conj-sub-list-aux l a g))
	        (member-equal (conj x (inv a g) g) l))))

(defthm ordp-conj-sub-list
  (implies (and (subgroupp h g)
		(in a g))
	   (ordp (conj-sub-list h a g) g))
  :hints (("Goal" :in-theory (enable conj-sub-list))))

(defthm sublistp-conj-sub-list
  (implies (and (subgroupp h g)
		(in a g))
	   (sublistp (conj-sub-list h a g) (elts g)))
  :hints (("Goal" :in-theory (enable conj-sub-list))))

(defthm conj-sub-list-non-nil
  (implies (and (subgroupp h g)
		(in a g))
	   (not (member-equal () (conj-sub-list h a g))))
  :hints (("Goal" :in-theory (e/d (subgroupp groupp) (sublistp-conj-sub-list))
                  :use (sublistp-conj-sub-list))))

(defthmd member-conj-sub-list
  (implies (and (subgroupp h g)
		(in a g)
		(in x g))
	   (iff (member-equal x (conj-sub-list h a g))
	        (in (conj x (inv a g) g) h)))
  :hints (("Goal" :in-theory (enable conj-sub-list))))

(defthm dlistp-conj-sub-list
  (implies (and (subgroupp h g)
		(in a g))
	   (dlistp (conj-sub-list h a g)))
  :hints (("Goal" :in-theory (disable ordp-conj-sub-list) :use (ordp-conj-sub-list))))

(defthmd e-in-conj-sub-list
  (implies (and (subgroupp h g)
		(in a g))
	   (member-equal (e g) (conj-sub-list h a g)))	   
  :hints (("Goal" :in-theory (enable member-conj-sub-list conj))
          ("Goal'" :in-theory (enable subgroupp e) :use (subgroup-e))))

(defthm car-conj-sub-list
  (implies (and (subgroupp h g)
		(in a g))
	   (equal (car (conj-sub-list h a g))
	          (e g)))
  :hints (("Goal" :in-theory (enable e)
                  :use (e-in-conj-sub-list (:instance car-ordp-minimal (x (e g)) (l (conj-sub-list h a g)))))))

(defthm consp-conj-sub-list
  (implies (and (subgroupp h g)
		(in a g))
	   (consp (conj-sub-list h a g)))	   
  :hints (("Goal" :in-theory (disable e-in-conj-sub-list)
                  :use (e-in-conj-sub-list))))

(defthm conj-sub-list-closed
  (implies (and (subgroupp h g)
		(in a g)
		(member-equal x (conj-sub-list h a g))
		(member-equal y (conj-sub-list h a g)))
           (member-equal (op x y g) (conj-sub-list h a g)))
  :hints (("Goal" :use (member-conj-sub-list
                        (:instance member-conj-sub-list (x y))
			(:instance member-conj-sub-list (x (op x y g)))
			(:instance conj-op (a (inv a g)))
			(:instance group-closure (g h) (x (conj x (inv a g) g)) (y (conj y (inv a g) g)))))))

(defthm conj-sub-list-inv
  (implies (and (subgroupp h g)
		(in a g)
		(member-equal x (conj-sub-list h a g)))
           (member-equal (inv x g) (conj-sub-list h a g)))
  :hints (("Goal" :use (member-conj-sub-list
                        (:instance member-conj-sub-list (x (inv x g)))
			(:instance inv-conj (a (inv a g)))			
			(:instance group-left-inverse (g h) (x (conj x (inv a g) g)))))))

(defsubgroup conj-sub (h a) g
  (and (subgroupp h g)
       (in a g))
  (conj-sub-list h a g))

;; Conjugate subgroups have the same order:

(local-defthm len-conj-sub-list-aux
  (implies (and (subgroupp h g)
                (dlistp l)
		(sublistp l (elts g))
		(in a g))
	   (equal (len (conj-sub-list-aux l a g))
	          (len l))))

(defthm order-conj-sub
  (implies (and (subgroupp h g)
		(in a g))
	   (equal (order (conj-sub h a g))
	          (order h)))
  :hints (("Goal" :in-theory (enable sublistp-sublistp subgroupp conj-sub-list)
                  :use ((:instance len-conj-sub-list-aux (l (elts h)))))))

;; (conj-sub h (e g) g) is the unique element of (conjs-sub h g) whose element list is a permutation of (elts h):

(local-defthm conj-sub-list-aux-e
  (implies (and (subgroupp h g)
		(sublistp l (elts g)))
	   (sublistp (conj-sub-list-aux l (e g) g) l)))

(local-defthmd conj-sub-list-e
  (implies (subgroupp h g)
	   (sublistp (conj-sub-list h (e g) g) (elts h)))
  :hints (("Goal" :in-theory (enable conj-sub-list))))

(defthmd permp-conj-sub-e
  (implies (subgroupp h g)
	   (permp (elts (conj-sub h (e g) g)) (elts h)))
  :hints (("Goal" :use (conj-sub-list-e
                        (:instance order-conj-sub (a (e g)))
                        (:instance permp-eq-len (l (conj-sub-list h (e g) g)) (m (elts h)))))))

(defthm member-conj-sub-e
  (implies (and (subgroupp h g)
                (in x g))
	   (iff (in x (conj-sub h (e g) g))
	        (in x h)))
  :hints (("Goal" :in-theory (enable permp)
	   :use (permp-conj-sub-e))))

(defthmd subgroupp-conj-sub-e
  (implies (subgroupp h g)
	   (subgroupp h (conj-sub h (e g) g)))
  :hints (("Goal" :in-theory (enable permp)
                  :use (permp-conj-sub-e
                        (:instance subgroup-subgroup (k (conj-sub h (e g) g)))))))

(defthmd orpd-h-conj-sub
  (implies (and (subgroupp h g)
		(ordp (elts h) g))
	   (equal (conj-sub h (e g) g)
	          h))
  :hints (("Goal" :in-theory (enable permp)
                  :use (permp-conj-sub-e
                        (:instance ordp-equal (x (elts h)) (y (elts (conj-sub h (e g) g))))
			(:instance subgroups-equal-elts (k (conj-sub h (e g) g)))))))

(local-defthmd permp-conj-sub-1
  (implies (and (subgroupp h g)
		(in a g)
		(in b g)
		(in x g))
	   (iff (member-equal x (conj-sub-list h (op a b g) g))
	        (in (conj x (op (inv b g) (inv a g) g) g) h)))
  :hints (("Goal" :use ((:instance member-conj-sub-list (a (op a b g)))
                        (:instance prod-inv (x a) (y b))))))

(local-defthmd permp-conj-sub-2
  (implies (and (subgroupp h g)
		(in a g)
		(in b g)
		(in x g))
	   (iff (member-equal x (conj-sub-list (conj-sub h b g) a g))
	        (in (conj x (inv a g) g) (conj-sub h b g))))
  :hints (("Goal" :use ((:instance member-conj-sub-list (h (conj-sub h b g)))))))

(local-defthmd permp-conj-sub-3
  (implies (and (subgroupp h g)
		(in a g)
		(in b g)
		(in x g))
	   (iff (member-equal (conj x (inv a g) g) (conj-sub-list h b g))
	        (in (conj x (op (inv b g) (inv a g) g) g) h)))	        
  :hints (("Goal" :use ((:instance member-conj-sub-list (a b) (x (conj x (inv a g) g)))))))

(local-defthmd permp-conj-sub-4
  (implies (and (subgroupp h g)
		(in a g)
		(in b g)
		(in x g))
	   (iff (in x (conj-sub h (op a b g) g))
	        (in x (conj-sub (conj-sub h b g) a g))))
  :hints (("Goal" :use (permp-conj-sub-1 permp-conj-sub-2 permp-conj-sub-3))))

(local-defthmd permp-conj-sub-5
  (implies (and (subgroupp h g)
		(in a g)
		(in b g)
		(sublistp l (elts g))
	        (sublistp l (elts (conj-sub h (op a b g) g))))
	   (sublistp l (elts (conj-sub (conj-sub h b g) a g))))
  :hints (("Subgoal *1/2" :use ((:instance permp-conj-sub-4 (x (car l)))))))

(local-defthmd permp-conj-sub-6
  (implies (and (subgroupp h g)
		(in a g)
		(in b g))
	   (sublistp (elts (conj-sub h (op a b g) g))
	             (elts (conj-sub (conj-sub h b g) a g))))
  :hints (("Goal" :use ((:instance permp-conj-sub-5 (l (elts (conj-sub h (op a b g) g))))))))

(local-defthmd permp-conj-sub-7
  (implies (and (subgroupp h g)
		(in a g)
		(in b g)
		(sublistp l (elts g))
	        (sublistp l (elts (conj-sub (conj-sub h b g) a g))))
	   (sublistp l (elts (conj-sub h (op a b g) g))))
  :hints (("Subgoal *1/2" :use ((:instance permp-conj-sub-4 (x (car l)))))))

(local-defthmd permp-conj-sub-8
  (implies (and (subgroupp h g)
		(in a g)
		(in b g))
	   (sublistp (elts (conj-sub (conj-sub h b g) a g))
	             (elts (conj-sub h (op a b g) g))))
  :hints (("Goal" :use ((:instance permp-conj-sub-7 (l (elts (conj-sub (conj-sub h b g) a g))))))))

(defthmd equal-conj-sub-a-b
  (implies (and (subgroupp h g)
		(in a g)
		(in b g))
	   (equal (conj-sub (conj-sub h b g) a g)
	          (conj-sub h (op a b g) g)))
  :hints (("Goal" :use (permp-conj-sub-6 permp-conj-sub-8
                        (:instance subgroups-equal-elts (h (conj-sub (conj-sub h b g) a g))
			                            (k (conj-sub h (op a b g) g)))
                        (:instance ordp-equal (x (elts (conj-sub (conj-sub h b g) a g)))
			                      (y (elts (conj-sub h (op a b g) g))))))))

;; If one conjugate of h is a subgroup of another, then they are equal:

(defthmd conj-subgroup-equal
  (implies (and (subgroupp h g)
		(in a g)
		(in b g)
                (subgroupp (conj-sub h a g) (conj-sub h b g)))
	   (equal (conj-sub h a g) (conj-sub h b g)))
  :hints (("Goal" :in-theory (enable permp)
                  :use (order-conj-sub
			(:instance order-conj-sub (a b))
			(:instance ordp-equal (x (conj-sub-list h a g)) (y (conj-sub-list h b g)))
		        (:instance permp-eq-len (l (conj-sub-list h a g)) (m (conj-sub-list h b g)))
                        (:instance subgroupp-sublistp (h (conj-sub h a g)) (g (conj-sub h b g)))
                        (:instance subgroups-equal-elts (h (conj-sub h a g)) (k (conj-sub h b g)))))))

;; Therefore, (conj-sub h (e g) g) is the only conjugate of h that includes h:

(defthmd conj-sub-subgroup-e
  (implies (and (subgroupp h g)
                (in a g)
		(subgroupp h (conj-sub h a g)))
	   (equal (conj-sub h a g)
	          (conj-sub h (e g) g)))
  :hints (("Goal" :in-theory (enable permp)
                  :use (permp-conj-sub-e
		        (:instance subgroupp-sublistp (g (conj-sub h a g)))
			(:instance subgroup-subgroup (h (conj-sub h (e g) g)) (k (conj-sub h a g)))
			(:instance sublistp-sublistp (n (conj-sub-list h a g)) (m (elts h)) (l (conj-sub-list h (e g) g)))
			(:instance conj-subgroup-equal (a (e g)) (b a))))))

;; The stabilizer of an element of the orbit of s is a conjugate of the stabilizer of s:

(local-defthmd conj-stabilizer-1
  (implies (and (actionp a g)
		(member-equal s (dom a))
		(in x g))
	   (iff (in y (stabilizer (act x s a g) a g))
	        (in y (conj-sub (stabilizer s a g) x g))))
  :hints (("Goal" :use ((:instance member-stab-elts (x y) (s (act x s a g)))
			(:instance member-stab-elts (x (conj y (inv x g) g)))
			(:instance member-conj-sub-list (x y) (a x) (h (stabilizer s a g)))
			(:instance action-cancel (x (inv x g)) (r (act (op y x g) s a g)) (s (act x s a g)))
			(:instance action-aassoc (x y) (y x))
			(:instance action-aassoc (x (inv x g)) (y x))
			(:instance action-aassoc (x (inv x g)) (y (op y x g)))
			(:instance group-assoc (x (inv x g)) (z x)))
	   :in-theory (enable conj))))

(defthmd conj-stabilizer
  (implies (and (actionp a g)
		(in s a)
		(in x g))
	   (equal (stabilizer (act x s a g) a g)
	          (conj-sub (stabilizer s a g) x g)))
  :hints (("Goal" :use ((:instance scex1-lemma (l (elts (stabilizer (act x s a g) a g))) (m (elts (conj-sub (stabilizer s a g) x g))))
			(:instance scex1-lemma (m (elts (stabilizer (act x s a g) a g))) (l (elts (conj-sub (stabilizer s a g) x g))))
			(:instance conj-stabilizer-1 (y (scex1 (elts (stabilizer (act x s a g) a g)) (elts (conj-sub (stabilizer s a g) x g)))))
			(:instance conj-stabilizer-1 (y (scex1 (elts (conj-sub (stabilizer s a g) x g)) (elts (stabilizer (act x s a g) a g)))))
			(:instance ordp-equal (x (elts (stabilizer (act x s a g) a g))) (y (elts (conj-sub (stabilizer s a g) x g))))
			(:instance subgroups-equal-elts (h (stabilizer (act x s a g) a g)) (k (conj-sub (stabilizer s a g) x g)))))))  

;; Subgroup conjugation is an important example of a group action, the domain of which is a list 
;; of all conjugates of a given subgroup h of g:

(defun conjs-sub-aux (h g l)
  (if (consp l)
      (let ((c (conj-sub h (car l) g))
            (res (conjs-sub-aux h g (cdr l))))
	(if (member-equal c res)
	    res
	  (cons c res)))
    ()))
        
(defund conjs-sub (h g)
  (conjs-sub-aux h g (elts g)))

(local-defthm dlistp-conjs-sub-aux
  (dlistp (conjs-sub-aux h g l)))

(defthm dlistp-conjs-sub
  (dlistp (conjs-sub h g))
  :hints (("Goal" :in-theory (enable conjs-sub))))

(local-defthm consp-conjs-sub-aux
  (implies (consp l)
           (consp (conjs-sub-aux h g l))))

(defthm consp-conjs-sub
  (implies (groupp g)
           (consp (conjs-sub h g)))
  :hints (("Goal" :in-theory (enable conjs-sub))))

;; (conjs-sub h g) contains every conjugate of h:

(local-defthm member-conjs-sub-aux
  (implies (and (subgroupp h g)
                (sublistp l (elts g))
		(member-equal x l))
           (member-equal (conj-sub h x g)
	                 (conjs-sub-aux h g l))))

(defthm member-conjs-sub
  (implies (and (subgroupp h g)
                (in x g))
           (member-equal (conj-sub h x g)
	                 (conjs-sub h g)))
  :hints (("Goal" :in-theory (enable conjs-sub))))

;; (conjs-sub h g) contains only conjugates of h:

(defun conjer-sub-aux (k h g l)
  (if (consp l)
      (if (equal k (conj-sub h (car l) g))
          (car l)
	(conjer-sub-aux k h g (cdr l)))
    ()))

(defund conjer-sub (k h g)
  (conjer-sub-aux k h g (elts g)))

(local-defthm conjs-sub-aux-conjer
  (implies (and (subgroupp h g)
                (sublistp l (elts g))
		(member-equal k (conjs-sub-aux h g l)))
           (equal (conj-sub h (conjer-sub-aux k h g l) g)
	          k)))

(local-defthm conjs-sub-aux-in-l
  (implies (and (subgroupp h g)
                (sublistp l (elts g))
		(member-equal k (conjs-sub-aux h g l)))
           (member-equal (conjer-sub-aux k h g l) l)))

(defthmd conjs-sub-conjer
  (implies (and (subgroupp h g)
		(member-equal k (conjs-sub h g)))
	   (and (in (conjer-sub k h g) g)
	        (equal (conj-sub h (conjer-sub k h g) g)
	               k)))
  :hints (("Goal" :in-theory (enable conjer-sub conjs-sub))))

(defthm subgroupp-conjs-sub
  (implies (and (subgroupp h g)
		(member-equal k (conjs-sub h g)))
	   (subgroupp k g))
  :hints (("Goal" :use (conjs-sub-conjer (:instance subgroupp-conj-sub (a (conjer-sub k h g)))))))

;; h is a subgroup of exactly one member of (conjs-sub h g):

(defthmd conjs-sub-subgroup
  (implies (and (subgroupp h g)
		(member-equal k (conjs-sub h g)))
           (iff (subgroupp h k)
	        (equal k (conj-sub h (e g) g))))
  :hints (("Goal" :use (subgroupp-conj-sub-e conjs-sub-conjer
                        (:instance conj-sub-subgroup-e (a (conjer-sub k h g)))))))

(defthm conjs-sub-identity
  (implies (and (subgroupp h g)
                (member-equal s (conjs-sub h g)))
	   (equal (conj-sub s (e g) g) s))
  :hints (("Goal" :use ((:instance conjs-sub-conjer (k s))
                        (:instance equal-conj-sub-a-b (a (e g)) (b (conjer-sub s h g)))))))

(defthm conjs-sub-assoc
  (implies (and (subgroupp h g)
                (member-equal s (conjs-sub h g))
		(in x g)
		(in y g))
	   (equal (conj-sub s (op x y g) g)
	          (conj-sub (conj-sub s y g) x g)))
  :hints (("Goal" :use ((:instance equal-conj-sub-a-b (h s) (a x) (b y))))))

(defthmd conj-sub-conj-sub-e
  (implies (and (subgroupp h g)
		(in x g))
	   (equal (conj-sub (conj-sub h (e g) g) x g)
	          (conj-sub h x g)))
  :hints (("Goal" :use ((:instance equal-conj-sub-a-b (a x) (b (e g))))))) 

(defthm conjs-sub-closed
  (implies (and (subgroupp h g)
                (member-equal s (conjs-sub h g))
		(in x g))
	   (member-equal (conj-sub s x g) (conjs-sub h g)))
  :hints (("Goal" :in-theory (disable member-conjs-sub)
                  :use ((:instance conjs-sub-conjer (k s))
                        (:instance member-conjs-sub (x (OP X (CONJER-SUB S H G) G)))
                        (:instance equal-conj-sub-a-b (a x) (b (conjer-sub s h g)))))))

(defaction conj-sub-act (h) g (subgroupp h g) (conjs-sub h g) (conj-sub s x g))

;; We define the normalizer of h to be the stabilizer of (conj-sub h (e g) g):

(defund normalizer (h g)
  (stabilizer (conj-sub h (e g) g)
	      (conj-sub-act h g)
	      g))

(defthm groupp-normalizer
  (implies (subgroupp h g)
           (groupp (normalizer h g)))
  :hints (("Goal" :in-theory (enable normalizer))))

(defthm subgroupp-normalizer
  (implies (subgroupp h g)
           (subgroupp (normalizer h g) g))
  :hints (("Goal" :in-theory (enable normalizer))))

(local-defthmd subgroup-of-normalizer-1
  (implies (and (subgroupp h g)
                (in x h)
		(in y h))
	   (in y (conj-sub h x g)))
  :hints (("Goal" :in-theory (enable conj)
                  :use ((:instance member-conj-sub-list (x y) (a x))
		        (:instance group-left-inverse (g h))
		        (:instance group-closure (x (inv x g)) (g h))
			(:instance group-closure (x (op (inv x g) y g)) (y x) (g h))))))

(local-defthm subgroup-of-normalizer-2
  (implies (and (subgroupp h g)
                (in x h)
		(member-equal y (conj-sub-list h (e g) g)))
	   (member-equal y (conj-sub-list h x g)))
  :hints (("Goal" :use (subgroup-of-normalizer-1
                        (:instance member-conj-sub-e (x y))))))

(local-defthm subgroup-of-normalizer-3
  (implies (and (subgroupp h g)
                (in x h)
		(sublistp l (conj-sub-list h (e g) g)))
	   (sublistp l (conj-sub-list h x g))))

(local-defthmd subgroup-of-normalizer-4
  (implies (and (subgroupp h g)
                (in x h))
	   (sublistp (conj-sub-list h (e g) g)
	             (conj-sub-list h x g))))

(local-defthmd subgroup-of-normalizer-5
  (implies (and (subgroupp h g)
                (in x h))
	   (permp (conj-sub-list h (e g) g)
	          (conj-sub-list h x g)))
  :hints (("Goal" :in-theory (disable permp-eq-len)
                  :use (subgroup-of-normalizer-4
                        (:instance permp-eq-len (l (conj-sub-list h (e g) g)) (m (conj-sub-list h x g)))
                        (:instance order-conj-sub (a x))
                        (:instance order-conj-sub (a (e g)))))))

(local-defthmd subgroup-of-normalizer-6
  (implies (and (subgroupp h g)
                (in x h))
	   (equal (conj-sub-list h (e g) g)
	          (conj-sub-list h x g)))
  :hints (("Goal" :in-theory (enable permp)
                  :use (subgroup-of-normalizer-5
		        (:instance ordp-equal (x (conj-sub-list h (e g) g)) (y (conj-sub-list h x g)))))))

(local-defthmd subgroup-of-normalizer-7
  (implies (and (subgroupp h g)
                (in x h))
	   (equal (conj-sub h (e g) g)
	          (conj-sub h x g)))
  :hints (("Goal" :in-theory (enable permp)
                  :use (subgroup-of-normalizer-6
		        (:instance subgroups-equal-elts (h (conj-sub h (e g) g)) (k (conj-sub h x g)))))))

(local-defthm subgroup-of-normalizer-8
  (implies (and (subgroupp h g)
                (in x h))
	   (in x (normalizer h g)))
  :hints (("Goal" :in-theory (e/d (normalizer) (conjs-sub-assoc))
                  :use (subgroup-of-normalizer-7
		        (:instance equal-conj-sub-a-b (a x) (b (e g)))
		        (:instance member-stab-elts (a (conj-sub-act h g)) (s (conj-sub h (e g) g)))))))

(local-defthmd subgroup-of-normalizer-9
  (implies (and (subgroupp h g)
                (sublistp l (elts h)))
           (sublistp l (elts (normalizer h g)))))

(local-defthmd subgroup-of-normalizer-10
  (implies (subgroupp h g)
           (sublistp (elts h) (elts (normalizer h g))))
  :hints (("Goal" :in-theory (enable subgroup-of-normalizer-9))))

(defthmd subgroup-of-normalizer
  (implies (subgroupp h g)
           (subgroupp h (normalizer h g)))
  :hints (("Goal" :in-theory (disable subgroupp-normalizer member-sublist ACL2::SUBSETP-MEMBER subgroup-of-normalizer-8)
                  :use (subgroup-of-normalizer-10 subgroupp-normalizer
                        (:instance subgroup-of-normalizer-8 (x (CAR (SXY (CAR H) H (NORMALIZER H G)))))
                        (:instance subgroup-of-normalizer-8 (x (CadR (SXY (CAR H) H (NORMALIZER H G)))))
                        (:instance not-subgroupp-cex (g (normalizer h g)))))))

(defthmd normalizer-elts
  (implies (and (subgroupp h g)
		(in x g))
	   (iff (in x (normalizer h g))
		(equal (conj-sub h x g)
		       (conj-sub h (e g) g))))
  :hints (("Goal" :in-theory (enable normalizer)
	          :use ((:instance member-stab-elts (a (conj-sub-act h g)) (s (conj-sub h (e g) g)))
			(:instance equal-conj-sub-a-b (a x) (b (e g)))))))

(local-defthmd inv-normalizer
  (implies (and (subgroupp h g)
		(in x (normalizer h g)))
	   (in (inv x g) (normalizer h g)))
  :hints (("Goal" :in-theory (disable subgroup-inv group-right-inverse group-left-inverse)
                  :use ((:instance group-left-inverse (g (normalizer h g)))
		        (:instance subgroup-inv (h (normalizer h g)))))))

(local-defthmd hack
  (implies (equal x y) (equal (elts x) (elts y))))

(defthmd normalizer-conj
  (implies (and (subgroupp h g)
		(in x (normalizer h g))
	        (in y h))
	   (in (conj y x g) h))
  :hints (("Goal" :use (inv-normalizer
                        (:instance hack (x (CONJ-SUB H (INV X G) G)) (y (CONJ-SUB H (E G) G)))
                        (:instance normalizer-elts (x (inv x g)))
		        (:instance member-conj-sub-e (x y))
			(:instance member-conj-sub-list (x y) (a (inv x g)))))))

;; A subgroup is a normal subgroup of its normalizer:

(defthmd normalizer-normp
  (implies (subgroupp h g)
           (normalp h (normalizer h g)))
  :hints (("Goal" :use (subgroup-of-normalizer
                        (:instance not-normalp-cex (g (normalizer h g)))		
                        (:instance normalizer-conj (x (cadr (normalp-cex h (normalizer h g))))
			                           (y (car (normalp-cex h (normalizer h g)))))						   
                        (:instance subgroup-conj (h (normalizer h g))
			                         (x (cadr (normalp-cex h (normalizer h g))))
			                         (y (car (normalp-cex h (normalizer h g)))))))))

;; On the other hand, if x is not in (normalizer h g), then we can find y in h such that (conj y x g) is not in h:

(defund normalizer-cex (x h g)
  (conj (scex1 (conj-sub-list h x g) (conj-sub-list h (e g) g)) (inv x g) g))

(local-defthmd normalizer-cex-1
  (implies (and (subgroupp h g)
                (in x g)
		(not (in x (normalizer h g))))
           (not (equal (conj-sub-list h x g)
	               (conj-sub-list h (e g) g))))
  :hints (("Goal" :in-theory (enable normalizer)
                  :use ((:instance member-stab-elts (a (conj-sub-act h g)) (s (conj-sub h (e g) g)))
		        (:instance subgroups-equal-elts (k (conj-sub h x g)) (h (conj-sub h (e g) g)))
			(:instance equal-conj-sub-a-b (a x) (b (e g)))))))

(local-defthmd normalizer-cex-2
  (implies (and (subgroupp h g)
                (in x g)
		(not (in x (normalizer h g))))
           (not (sublistp (conj-sub-list h x g)
	                  (conj-sub-list h (e g) g))))
  :hints (("Goal" :in-theory (enable permp)
                  :use (normalizer-cex-1
                        (:instance ordp-equal (x (conj-sub-list h (e g) g)) (y (conj-sub-list h x g)))
		        (:instance permp-eq-len (l (conj-sub-list h x g)) (m (conj-sub-list h (e g) g)))
			(:instance order-conj-sub (a x))
                        (:instance order-conj-sub (a (e g)))))))

(local-defthmd normalizer-cex-3
  (implies (and (subgroupp h g)
                (in x g)
		(not (in x (normalizer h g))))
	   (let ((z (scex1 (conj-sub-list h x g) (conj-sub-list h (e g) g))))
	     (and (in z (conj-sub h x g))
	          (not (in z h)))))
  :hints (("Goal" :use (normalizer-cex-2
                        (:instance scex1-lemma (l (conj-sub-list h x g)) (m (conj-sub-list h (e g) g)))
                        (:instance member-conj-sub-e (x (scex1 (conj-sub-list h x g) (conj-sub-list h (e g) g))))))))

(defthmd normalizer-cex-lemma
  (implies (and (subgroupp h g)
                (in x g)
		(not (in x (normalizer h g))))
	   (let ((y (normalizer-cex x h g)))
	     (and (in y h)
	          (not (in (conj y x g) h)))))
  :hints (("Goal" :in-theory (enable normalizer-cex)
                  :use (normalizer-cex-3
                        (:instance member-conj-sub-list (x (scex1 (conj-sub-list h x g) (conj-sub-list h (e g) g)))
			                                (a x))))))

;;------------------------------------------------------------------------------------------------------------------------

(defthm sublistp-conjs-sub-orbit-1
  (implies (and (subgroupp h g)
                (sublistp l (conjs-sub h g)))
	   (sublistp l (orbit (conj-sub h (e g) g) (conj-sub-act h g) g)))
  :hints (("Subgoal *1/3" :in-theory (enable conj-sub-conj-sub-e)
                          :use ((:instance conjs-sub-conjer (k (car l)))
                                (:instance member-act-orbit (x (conjer-sub (car l) h g))
				                            (s (conj-sub h (e g) g))
							    (a (conj-sub-act h g)))))))

(defthmd sublistp-conjs-sub-orbit
  (implies (subgroupp h g)
	   (sublistp (conjs-sub h g) (orbit (conj-sub h (e g) g) (conj-sub-act h g) g))))

(defthmd conjs-sub-orbit
  (implies (subgroupp h g)
	   (equal (orbit (conj-sub h (e g) g) (conj-sub-act h g) g)
	          (conjs-sub h g)))
  :hints (("Goal" :in-theory (e/d (sublistp-conjs-sub-orbit) (ordp-a conj-sub-act-dom sublistp-orbit))
                  :use (conj-sub-act-dom
		        (:instance ordp-a (a (conj-sub-act h g)))
			(:instance sublistp-orbit (a (conj-sub-act h g)) (s (conj-sub h (e g) g)))
		        (:instance ordp-equal (x (orbit (conj-sub h (e g) g) (conj-sub-act h g) g))
                                              (y (conjs-sub h g))
					      (g (conj-sub-act h g)))))))


;;------------------------------------------------------------------------------------------------------------------------

(defthmd index-normalizer
  (implies (subgroupp h g)
           (equal (len (conjs-sub h g))
	          (subgroup-index (normalizer h g) g)))
  :hints (("Goal" :in-theory (e/d (normalizer) (order-pos))
                  :use (conjs-sub-orbit
		        (:instance order-pos (g (stabilizer (conj-sub h (e g) g) (conj-sub-act h g) g)))
		        (:instance lagrange (h (normalizer h g)))
		        (:instance stabilizer-orbit (s (conj-sub h (e g) g)) (a (conj-sub-act h g)))))))

;;------------------------------------------------------------------------------------------------------------------------

(defthmd permp-conjs-sub-1
  (implies (and (subgroupp h g)
		(in x g)
		(in y g))
	   (equal (conj-sub (conj-sub h x g) (op y (inv x g) g) g)
		  (conj-sub h y g)))
  :hints (("Goal" :use ((:instance conj-sub-conj-sub-e (x y))
                        (:instance equal-conj-sub-a-b (a (inv x g)) (b x))
			(:instance equal-conj-sub-a-b (a y) (b (inv x g)))))))

(defthm permp-conjs-sub-2
  (implies (and (subgroupp h g)
		(in x g)
		(sublistp l (conjs-sub h g)))
	   (sublistp l (conjs-sub (conj-sub h x g) g)))	   
  :hints (("subgoal *1/2" :in-theory (disable member-conjs-sub)
                          :use ((:instance conjs-sub-conjer (k (car l)))
                                (:instance permp-conjs-sub-1 (y (conjer-sub (car l) h g)))				
				(:instance member-conjs-sub (h (conj-sub h x g)) (x (op (conjer-sub (car l) h g) (inv x g) g)))))))

(defthmd permp-conjs-sub-3
  (implies (and (subgroupp h g)
		(in x g))
	   (sublistp (conjs-sub (conj-sub h x g) g)
	             (conjs-sub (conj-sub h x g) g))))

(defthm permp-conjs-sub-4
  (implies (and (subgroupp h g)
		(in x g)
		(sublistp l (conjs-sub (conj-sub h x g) g)))
	   (sublistp l (conjs-sub h g)))	   
  :hints (("subgoal *1/2" :in-theory (disable member-conjs-sub)
                          :use ((:instance conjs-sub-conjer (k (car l)) (h (conj-sub h x g)))
                                (:instance equal-conj-sub-a-b (a (conjer-sub (car l) (conj-sub h x g) g)) (b x))
				(:instance member-conjs-sub (x (op (conjer-sub (car l) (conj-sub h x g) g) x g)))))))

(defthmd permp-conjs-sub-5
  (implies (and (subgroupp h g)
		(in x g))
	   (sublistp (conjs-sub (conj-sub h x g) g)
	             (conjs-sub h g))))

(defthm permp-conjs-sub
  (implies (and (subgroupp h g)
		(in x g))
	   (permp (conjs-sub (conj-sub h x g) g)
	          (conjs-sub h g)))
  :hints (("Goal" :in-theory (enable permp)
                  :use (permp-conjs-sub-3 permp-conjs-sub-5))))

(defthmd member-conjs-sub-self
  (implies (and (subgroupp m g)
		(member c (conjs-sub m g)))
           (member-equal c (conjs-sub c g)))
  :hints (("Goal" :in-theory (disable member-conjs-sub)
                  :use ((:instance orpd-h-conj-sub (h c))		  
                        (:instance member-conjs-sub (h c) (x (e g)))))))

(local-defthmd normalizer-conj-sub-1
  (implies (and (subgroupp m g)
		(member-equal c (conjs-sub m g)))
	   (iff (in x (stabilizer c (conj-sub-act m g) g))
	        (in x (normalizer c g))))
  :hints (("Goal" :in-theory (enable normalizer)
                  :use (member-conjs-sub-self
                        (:instance member-stab-elts (a (conj-sub-act c g)) (s c))
                        (:instance member-stab-elts (a (conj-sub-act m g)) (s c))
			(:instance permp-conjs-sub (h m) (x (conjer-sub c h g)))
			(:instance conjs-sub-conjer (k c))))))

(local-defthmd normalizer-conj-sub-2
  (implies (and (subgroupp m g)
		(member-equal c (conjs-sub m g)))
	   (and (sublistp (elts (stabilizer c (conj-sub-act m g) g))
	                  (elts (normalizer c g)))
	        (sublistp (elts (normalizer c g))
		          (elts (stabilizer c (conj-sub-act m g) g)))))
  :hints (("Goal" :use ((:instance scex1-lemma (l (elts (stabilizer c (conj-sub-act m g) g)))
                                               (m (elts (normalizer c g))))
			(:instance scex1-lemma (m (elts (stabilizer c (conj-sub-act m g) g)))
                                               (l (elts (normalizer c g))))
			(:instance normalizer-conj-sub-1 (x (scex1 (elts (stabilizer c (conj-sub-act m g) g)) (elts  (normalizer c g)))))
			(:instance normalizer-conj-sub-1 (x (scex1 (elts (normalizer c g)) (elts (stabilizer c (conj-sub-act m g) g)))))))))

(local-defthmd normalizer-conj-sub-3
  (implies (and (subgroupp m g)
		(member-equal c (conjs-sub m g)))
	   (equal (stabilizer c (conj-sub-act m g) g)
	          (normalizer c g)))
  :hints (("Goal" :in-theory (enable normalizer)
                  :use (member-conjs-sub-self normalizer-conj-sub-2
                        (:instance ordp-equal (x (elts (stabilizer c (conj-sub-act m g) g)))
			                      (y (elts (normalizer c g))))
		        (:instance subgroups-equal-elts (h (stabilizer c (conj-sub-act m g) g)) (k (normalizer c g)))))))

(defthmd normalizer-conj-sub
  (implies (and (subgroupp m g)
		(member-equal c (conjs-sub m g)))
	   (equal (normalizer c g) (conj-sub (normalizer m g) (conjer-sub c m g) g)))
  :hints (("Goal" :in-theory (enable normalizer)
                  :use (normalizer-conj-sub-3
		        (:instance conj-stabilizer (a (conj-sub-act m g)) (x (conjer-sub c m g)) (s (conj-sub m (e g) g)))
			(:instance conj-sub-conj-sub-e (h m) (x (conjer-sub c m g)))
			(:instance conjs-sub-conjer (h m) (k c))))))

;;---------------------------------------------------------------------------------------------------
;; Induced Hormomorphisn into (sym (order g))
;;---------------------------------------------------------------------------------------------------

;; An action of a group g associates each element of g with a permutation of (dom a).
;; By identifying an element of (dom a) with its index, we have an element of (sym n),
;; where n = (order a).  If x is in g and p is the element of (sym n) corresponding to x,
;; then for 0 <= k < n, the image of k under p is computed by the following:

(defund act-perm-val (x k a g)
  (index (act x (nth k (dom a)) a g)
         (dom a)))

(defthm actionp-pos-len
  (implies (actionp a g)
	   (posp (len (dom a))))
  :hints (("Goal" :expand ((len (car a))))))

(local-defthmd act-perm-val-val
  (implies (and (actionp a g)
		(in x g)
		(member-equal k (ninit (order a))))
	   (member-equal (act-perm-val x k a g)
			 (ninit (order a))))
  :hints (("Goal" :in-theory (enable act-perm-val member-ninit))))

(local-defthmd act-perm-val-1-1
  (implies (and (actionp a g)
		(in x g)
		(member-equal j (ninit (order a)))
		(member-equal k (ninit (order a)))
		(not (= j k)))
	   (not (equal (act-perm-val x j a g)
		       (act-perm-val x k a g))))
  :hints (("Goal" :in-theory (enable act-perm-val member-ninit)
	          :use ((:instance action-cancel (r (nth j (dom a))) (s (nth k (dom a))))
		        (:instance index-1-to-1  (x (act x (nth j (car a)) a g)) (y (act x (nth k (car a)) a g)) (l (car a)))))))

;; The element of (sym n) corresponding to x:

(defun act-perm-aux (x k a g)
  (if (zp k)
      ()
    (append (act-perm-aux x (1- k) a g)
            (list (act-perm-val x (1- k) a g)))))

(defund act-perm (x a g)
  (act-perm-aux x (order a) a g))

(local-defthmd member-act-perm-aux
  (implies (and (actionp a g)
		(in x g)
		(member-equal k (ninit (order a)))
		(natp j)
		(<= j k))
	   (not (member-equal (act-perm-val x k a g)
	                      (act-perm-aux x j a g))))
  :hints (("Subgoal *1/2" :use (act-perm-val-1-1
                                (:instance act-perm-val-1-1 (j (1- j)))
                                (:instance act-perm-val-1-1 (k (1- j))))
                          :in-theory (enable member-ninit))))

(local-defthmd sublistp-act-perm-aux
  (implies (and (actionp a g)
		(in x g)
		(natp k)
		(<= k (order a)))
	   (and (sublistp (act-perm-aux x k a g)
	                  (ninit (order a)))
		(dlistp (act-perm-aux x k a g))))
  :hints (("Subgoal *1/2" :use ((:instance act-perm-val-val (k (1- k)))
                                (:instance member-act-perm-aux (k (1- k)) (j (1- k))))
                          :in-theory (enable member-ninit))))

(local-defthmd sublistp-act-perm
  (implies (and (actionp a g)
		(in x g))
	   (and (sublistp (act-perm x a g)
	                  (ninit (order a)))
		(dlistp (act-perm x a g))))
  :hints (("Goal" :in-theory (enable act-perm)
                  :use ((:instance sublistp-act-perm-aux (k (order a)))))))

(local-defthm len-act-perm-aux
  (implies (and (actionp a g)
		(in x g)
		(natp k))
	   (equal (len (act-perm-aux x k a g))
	          k)))

(local-defthm len-act-perm
  (implies (and (actionp a g)
		(in x g))
	   (equal (len (act-perm x a g))
	          (order a)))
  :hints (("Goal" :in-theory (enable act-perm))))

(defthmd act-perm-is-perm
  (implies (and (actionp a g)
                (in x g))
	   (in (act-perm x a g)
	       (sym (order a))))
  :hints (("Goal" :use (sublistp-act-perm
                        (:instance permp-eq-len (l (act-perm x a g)) (m (ninit (order a))))
			(:instance member-perm-slist (n (order a)) (x (act-perm x a g)))))))

(local-defthmd nth-act-perm-aux
  (implies (and (actionp a g)
		(in x g)
		(natp k)
		(<= k (order a))
		(natp j)
		(< j k))
	   (equal (nth j (act-perm-aux x k a g))
	          (act-perm-val x j a g))))

(defthm act-perm-val-is-val
  (implies (and (actionp a g)
                (in x g)
		(member-equal k (ninit (order a))))
	   (equal (nth k (act-perm x a g))
	          (act-perm-val x k a g)))
  :hints (("Goal" :in-theory (enable member-ninit act-perm)
                  :use ((:instance nth-act-perm-aux (k (order a)) (j k))))))

(local-defthmd act-perm-val-e
  (implies (and (actionp a g)
		(member-equal k (ninit (order a))))
	   (equal (nth k (act-perm (e g) a g))
	          k))
  :hints (("Goal" :in-theory (enable act-perm-val))))

;; The identity of g corresponds to the identity of (sym n):

(defthmd act-perm-e
  (implies (actionp a g)
	   (equal (act-perm (e g) a g)
	          (ninit (order a))))
  :hints (("Goal" :in-theory (enable member-ninit)
                  :use ((:instance act-perm-is-perm (x (e g)))
		        (:instance act-perm-val-e (k (nth-diff (act-perm (e g) a g) (ninit (len (car a))))))
		        (:instance nth-diff-perm (n (order a)) (x (act-perm (e g) a g)) (y (ninit (order a))))))))

;; The group operation is preserved by this correspondence:

(local-defthmd act-perm-val-comp
  (implies (and (actionp a g)
                (in x g)
		(in y g)
		(member-equal k (ninit (order a))))
	   (equal (nth k (act-perm (op x y g) a g))
	          (nth (nth k (act-perm y a g)) (act-perm x a g))))
  :hints (("Goal" :in-theory (enable act-perm-val action-aassoc))))

(defthmd act-perm-comp
  (implies (and (actionp a g)
                (in x g)
		(in y g))
	   (equal (act-perm (op x y g) a g)
	          (comp-perm (act-perm x a g)
		             (act-perm y a g)
			     (order a))))
  :hints (("Goal" :use (act-perm-is-perm
                        (:instance act-perm-is-perm (x y))
                        (:instance act-perm-is-perm (x (op x y g)))
			(:instance nth-diff-perm (n (order a)) (x (act-perm (op x y g) a g))
			                                       (y (comp-perm (act-perm x a g) (act-perm y a g) (order a))))
			(:instance act-perm-val-comp (k (nth-diff (act-perm (op x y g) a g) (comp-perm (act-perm x a g) (act-perm y a g) (order a)))))))))

;; Thus, we have a homomorphism from g into the symmetric group:

(defmap act-sym (a g)
  (elts g)
  (act-perm x a g))

(local-defthmd act-perm-codomain-cex
  (implies (actionp a g)
           (not (codomain-cex (act-sym a g) g (sym (order a)))))
  :hints (("Goal" :use ((:instance codomain-cex-lemma (map (act-sym a g)) (h (sym (order a))))
                        (:instance act-perm-is-perm (x (codomain-cex (act-sym a g) g (sym (order a)))))))))

(local-defthmd act-perm-homomorphism-cex
  (implies (actionp a g)
           (not (homomorphism-cex (act-sym a g) g (sym (order a)))))
  :hints (("Goal" :use ((:instance act-perm-is-perm (x (car (homomorphism-cex (act-sym a g) g (sym (order a))))))
                        (:instance act-perm-is-perm (x (cdr (homomorphism-cex (act-sym a g) g (sym (order a))))))
                        (:instance act-perm-is-perm (x (op (car (homomorphism-cex (act-sym a g) g (sym (order a))))
			                                   (cdr (homomorphism-cex (act-sym a g) g (sym (order a))))
							   g)))
                        (:instance act-perm-is-perm (x (op x y g)))
			(:instance homomorphismp-cex-lemma (map (act-sym a g)) (h (sym (order a))))
                        (:instance act-perm-comp (x (car (homomorphism-cex (act-sym a g) g (sym (order a)))))
			                         (y (cdr (homomorphism-cex (act-sym a g) g (sym (order a))))))))))

(defthmd homomorphismp-act-sym
  (implies (actionp a g)
           (homomorphismp (act-sym a g)
	                  g
			  (sym (order a))))
  :hints (("Goal" :in-theory (enable e homomorphismp)
                  :use (act-perm-e act-perm-codomain-cex act-perm-homomorphism-cex))))

;; An element of the kernel of (act-sym a g) acts trivially on every element of (dom a):

(local-defthmd act-perm-ninit
  (implies (and (actionp a g)
                (in x g)
		(equal (act-perm x a g) (ninit (order a)))
		(member-equal k (ninit (order a))))
	   (equal (index (act x (nth k (dom a)) a g) (dom a))
	          k))		  
  :hints (("Goal" :use (act-perm-val-is-val)
                  :in-theory (e/d (act-perm-val member-ninit) (act-perm-val-is-val)))))

(local-defthmd index-act
  (implies (and (actionp a g)
                (in x g)
		(in s a)
		(equal (act-perm x a g) (ninit (order a))))
	   (equal (index (act x s a g) (dom a))
	          (index s (dom a))))
  :hints (("Goal" :use ((:instance act-perm-ninit (k (index s (dom a))))))))

(defthmd act-sym-kernel
  (implies (and (actionp a g)
                (in x g)
                (equal (act-perm x a g) (e (sym (order a))))
		(in s a))
	  (equal  (act x s a g)
	          s))
  :hints (("Goal" :in-theory (enable e)
                  :use (index-act (:instance index-1-to-1 (x (act x s a g)) (y s) (l (dom a)))))))

;; We have observed that every group g is an action of itself on its element list, with (act g x s g) = (op x s g).
;; The identity of g is the only element that acts trivially.  Therefore, every group g is isomorphic to a
;; subgrouyp of (sym (order g)):

(local-defthmd act-sym-g-e
  (implies (and (groupp g)
                (in x g)
                (equal (act-perm x g g) (e (sym (order g)))))
	   (equal (e g) x))
  :hints (("Goal" :in-theory (enable actionp-group)
                  :use ((:instance act-sym-kernel (a g) (s x))
                        (:instance left-cancel (a x) (y (e g)))))))

(defthm endomorphismp-act-sym-g
  (implies (groupp g)
	   (endomorphismp (act-sym g g) g (sym (order g))))
  :hints (("Goal" :in-theory (enable actionp-group)
                  :use ((:instance homomorphismp-act-sym (a g))
		        (:instance act-sym-g-e (x (cadr (kelts (act-sym g g) g (sym (order g))))))
                        (:instance homomorphism-endomorphism (map (act-sym g g)) (h (sym (order g))))))))

;; Recall the action act-lcosets of a group g on the left cosets of a subgroup h.
;; The kernel of the homomorphism induced by this action is a subgroup of h:

(local-defthmd kernel-act-lcosets-sym-1
  (implies (and (subgroupp h g)
                (in x g)
		(equal (act-perm x (act-lcosets h g) g)
		       (e (sym (subgroup-index h g)))))
	   (in x h))
  :hints (("Goal" :use (equal-lcoset-lcoset-e
                        (:instance act-sym-kernel (a (act-lcosets h g)) (s (lcoset (e g) h g)))
                        (:instance equal-lcosets-cancel (y (car (lcoset (e g) h g))) (z (e g))))
		  :in-theory (enable lcoset-car))))

(local-defthmd kernel-act-lcosets-sym-2
  (implies (and (subgroupp h g)
		(in x (kernel (act-sym (act-lcosets h g) g) (sym (subgroup-index h g)) g)))
	   (in x h))
  :hints (("Goal" :use (kernel-act-lcosets-sym-1
                        (:instance member-kelts (map (act-sym (act-lcosets h g) g)) (h (sym (subgroup-index h g))))
		        (:instance homomorphismp-act-sym (a (act-lcosets h g)))
                        (:instance member-kelts (map (act-sym (act-lcosets h g) g)) (h (sym (subgroup-index h g))))))))

(local-defthmd kernel-act-lcosets-sym-3
  (implies (subgroupp h g)
           (sublistp (elts (kernel (act-sym (act-lcosets h g) g) (sym (subgroup-index h g)) g))
	             (elts h)))
  :hints (("Goal" :use ((:instance kernel-act-lcosets-sym-2 (x (scex1 (elts (kernel (act-sym (act-lcosets h g) g) (sym (subgroup-index h g)) g))
                                                                      (elts h))))
		        (:instance scex1-lemma (l (elts (kernel (act-sym (act-lcosets h g) g) (sym (subgroup-index h g)) g)))
			                       (m (elts h)))))))

(defthmd subgroup-kernel-act-cosets
  (implies (subgroupp h g)
	   (subgroupp (kernel (act-sym (act-lcosets h g) g)
	                      (sym (subgroup-index h g))
			      g)
		      h))
  :hints (("Goal" :use (kernel-act-lcosets-sym-3
		        (:instance homomorphismp-act-sym (a (act-lcosets h g)))
			(:instance subgroup-subgroup (K h) (h (kernel (act-sym (act-lcosets h g) g) (sym (subgroup-index h g)) g)))))))

;; The last result has the following important consequence:

;; LEMMA: Let p be the least prime dividing (order g) and suppose the index of h ib g is p.  Then h is normal in g.

;; Proof: Let k = (kernel (act-sym (act-cosets h g) g) (sym (subgroup-index h g)) g).
;; We have shown that k is normal in g.
;; By endomorphism-quotient-map, (quotient g k) is isomorphic to a subgroup of (sym p),
;; and therefore (subgroup-index k g) divides p!, which implies (subgroup-index k h) divides (p-1)!.
;; If (subgroup-index k h) > 1, then (subgroup-index k g) has a prime divisor q.  Since q divides (p-1)!,
;; q < p. (This may be proved by induction on p as a consequence of euclid.)
;; But since q divides (order g), q >= p by assumption, a contradiction.  Thus, (subgroup-index k h) = 1,
;; which implies (permp (elts k) (elts h)), and by permp-normalp, h is normal in g.

(local-defund kern (g h) (kernel (act-sym (act-lcosets h g) g) (sym (subgroup-index h g)) g))

(local-defund phi (g h) (quotient-map (act-sym (act-lcosets h g) g) g (sym (subgroup-index h g))))

(local-defund symsub (g h) (image (phi g h) (quotient g (kern g h)) (sym (subgroup-index h g))))

(local-defthmd ildn-0
  (implies (subgroupp h g)
           (normalp (kern g h) g))
  :hints (("Goal" :in-theory (enable kern)
		  :use ((:instance homomorphismp-act-sym (a (act-lcosets h g)))))))

(local-defthmd ildn-1
  (implies (subgroupp h g)
	   (isomorphismp (phi g h) (quotient g (kern g h)) (symsub g h)))
  :hints (("Goal" :in-theory (enable phi kern symsub)
	          :use ((:instance endomorphismp-quotient-map (map (act-sym (act-lcosets h g) g)) (h (sym (subgroup-index h g))))
		        (:instance homomorphismp-act-sym (a (act-lcosets h g)))
		        (:instance endomorphismp-isomorphismp (map (phi g h)) (g (quotient g (kern g h))) (h (sym (subgroup-index h g))))))))

(local-defthmd ildn-2
  (implies (subgroupp h g)
	   (subgroupp (symsub g h) (sym (subgroup-index h g))))
  :hints (("Goal" :in-theory (enable phi kern symsub)
	          :use ((:instance endomorphismp-quotient-map (map (act-sym (act-lcosets h g) g)) (h (sym (subgroup-index h g))))
		        (:instance homomorphismp-act-sym (a (act-lcosets h g)))))))

(local-defthmd ildn-3
  (implies (subgroupp h g)
	   (subgroupp (kern g h) h))
  :hints (("Goal" :in-theory (enable kern)
	          :use (subgroup-kernel-act-cosets))))

(local-defund lpd (g) (least-prime-divisor (order g)))

(local-defthmd ildn-4
  (implies (and (groupp g)
                (> (order g) 1))
           (and (primep (lpd g))
	        (divides (lpd g) (order g))))
  :hints (("Goal" :in-theory (enable lpd)
                  :use ((:instance primep-least-divisor (n (order g)))
		        (:instance least-divisor-divides (k 2) (n (order g)))))))

(local-defthmd ildn-5
  (implies (and (groupp g)
                (> (order g) 1)
		(primep q)
		(divides q (order g)))
           (<= (lpd g) q))
  :hints (("Goal" :in-theory (enable lpd)
                  :use ((:instance least-divisor-is-least (d q) (k 2) (n (order g)))))))

(local-defthmd ildn-6
  (implies (and (subgroupp h g)
                (> (order g) 1)
		(= (subgroup-index h g) (lpd g)))
           (divides (order (quotient g (kern g h)))
	            (fact (lpd g))))
  :hints (("Goal" :use (ildn-1 ildn-2 ildn-4
                        (:instance lagrange (g (sym (lpd g))) (h (symsub g h)))
			(:instance isomorphism-equal-orders (map (phi g h)) (g (quotient g (kern g h))) (h (symsub g h)))
			(:instance order-sym (n (lpd g)))))))

(local-defthmd len-lcosets-pos
  (implies (subgroupp h g)
           (> (len (lcosets h g)) 0))
  :hints (("Goal" :in-theory (disable member-lcoset-cosets)
                  :expand ((len (lcosets h g)))
                  :use ((:instance member-lcoset-cosets (x (e g)))))))

(local-defthmd ildn-7
  (implies (and (subgroupp h g)
                (> (order g) 1)
		(= (subgroup-index h g) (lpd g)))
           (divides (subgroup-index (kern g h) h)
	            (fact (1- (lpd g)))))
  :hints (("Goal" :in-theory (disable subgroup-e)
                  :use (ildn-0 ildn-3 ildn-6 len-lcosets-pos
                        (:instance prod-indices (k h) (h (kern g h)))
			(:instance len-lcosets-pos (h (kern g h)))
			(:instance len-lcosets-pos (h (kern g h)) (g h))
			(:instance subgroupp-transitive (h (kern g h)) (k h))))))

(local-defthmd ildn-8
  (implies (and (subgroupp h g)
                (> (order g) 1)
		(= (subgroup-index h g) (lpd g))
		(primep q)
		(divides q (subgroup-index (kern g h) h)))
           (divides q (fact (1- (lpd g)))))
  :hints (("Goal" :use (ildn-7
                        (:instance divides-transitive (x q) (y (subgroup-index (kern g h) h)) (z (fact (1- (lpd g)))))))))

(local-defthmd ildn-9
  (implies (and (primep q)
                (posp n)
		(divides q (fact n)))
	   (<= q n))
  :hints (("Subgoal *1/4" :use ((:instance euclid (p q) (a n) (b (fact (1- n))))))))

(local-defthmd ildn-10
  (implies (and (subgroupp h g)
                (> (order g) 1)
		(= (subgroup-index h g) (lpd g))
		(primep q)
		(divides q (subgroup-index (kern g h) h)))
           (< q (lpd g)))
  :hints (("Goal" :use (ildn-8
                        (:instance ildn-9 (n (1- (lpd g))))))))

(local-defthmd ildn-11
  (implies (and (subgroupp h g)
                (> (order g) 1)
		(= (subgroup-index h g) (lpd g))
		(primep q)
		(divides q (subgroup-index (kern g h) h)))
           (divides q (order h)))
  :hints (("Goal" :use (ildn-3
                        (:instance lagrange (h (kern g h)) (g h))
                        (:instance divides-transitive (x q) (y (subgroup-index (kern g h) h)) (z (order h)))))))

(local-defthmd ildn-12
  (implies (and (subgroupp h g)
                (> (order g) 1)
		(= (subgroup-index h g) (lpd g))
		(primep q)
		(divides q (subgroup-index (kern g h) h)))
           (divides q (order g)))
  :hints (("Goal" :use (ildn-11 lagrange
                        (:instance divides-transitive (x q) (y (order h)) (z (order g)))))))

(local-defthmd ildn-13
  (implies (and (subgroupp h g)
                (> (order g) 1)
		(= (subgroup-index h g) (lpd g))
		(primep q))
           (not (divides q (subgroup-index (kern g h) h))))
  :hints (("Goal" :use (ildn-5 ildn-10 ildn-12))))

(local-defthmd ildn-14
  (implies (and (subgroupp h g)
                (> (order g) 1)
		(= (subgroup-index h g) (lpd g)))
           (equal (subgroup-index (kern g h) h)
	          1))
  :hints (("Goal" :use (ildn-3
                        (:instance ildn-13 (q (least-prime-divisor (subgroup-index (kern g h) h))))
                        (:instance primep-least-divisor (n (subgroup-index (kern g h) h)))
			(:instance len-lcosets-pos (h (kern g h)) (g h))
			(:instance least-divisor-divides (k 2) (n (subgroup-index (kern g h) h)))))))


(local-defthmd ildn-15
  (implies (and (subgroupp h g)
                (> (order g) 1)
		(= (subgroup-index h g) (lpd g)))
           (equal (order (kern g h)) (order h)))
  :hints (("Goal" :use (ildn-3 ildn-14 (:instance lagrange (h (kern g h)) (g h))))))

(local-defthmd ildn-16
  (implies (and (subgroupp h g)
                (> (order g) 1)
		(= (subgroup-index h g) (lpd g)))
           (permp (elts (kern g h)) (elts h)))
  :hints (("Goal" :use (ildn-3 ildn-15
                        (:instance permp-eq-len (l (elts (kern g h))) (m (elts h)))))))

(defthmd index-least-divisor-normal
  (implies (and (subgroupp h g)
                (> (order g) 1)
		(equal (subgroup-index h g)
		       (least-prime-divisor (order g))))
	   (normalp h g))
  :hints (("Goal" :in-theory (enable lpd)
                  :use (ildn-0 ildn-16
                        (:instance permp-normalp (h (kern g h)) (k h))))))


;;-------------------------------------------------------------------------------------------------------

(local-defthmd conjs-sub-not-subgroup-1
  (implies (and (subgroupp h g)
		(member-equal k1 (conjs-sub h g))
		(member-equal k2 (conjs-sub h g)))
	   (member-equal k2 (conjs-sub k1 g)))
  :hints (("Goal" :in-theory (e/d (permp) (ordp-conj-sub-list))
                  :use ((:instance conjs-sub-conjer (k k1))
                        (:instance permp-conjs-sub (x (conjer-sub k1 h g)))))))

(local-defthmd conjs-sub-not-subgroup-2
  (implies (and (subgroupp h g)
		(member-equal k1 (conjs-sub h g)))
	   (ordp (elts k1) g))
  :hints (("Goal" :in-theory (disable conj-sub-elts ordp-conj-sub-list)
                  :use ((:instance conjs-sub-conjer (k k1))
		        (:instance conj-sub-elts (a (conjer-sub k1 h g)))
			(:instance ordp-conj-sub-list (a (conjer-sub k1 h g)))))))

(defthm conjs-sub-not-subgroup
  (implies (and (subgroupp h g)
		(member-equal k1 (conjs-sub h g))
		(member-equal k2 (conjs-sub h g))
		(subgroupp k1 k2))
	   (equal k2 k1))
  :rule-classes ()
  :hints (("Goal" :use (conjs-sub-not-subgroup-1 conjs-sub-not-subgroup-2
                        (:instance conjs-sub-subgroup (h k1) (k k2))
			(:instance orpd-h-conj-sub (h k1))))))

(defthmd order-conjs-sub
  (implies (and (subgroupp h g)
                (member-equal k (conjs-sub h g)))
	   (equal (order k) (order h)))
  :hints (("Goal" :use (conjs-sub-conjer (:instance order-conj-sub (a (conjer-sub k h g)))))))


(local-defthmd lcsn-1
  (implies (and (subgroupp h g)
                (equal (len (conjs-sub h g)) 1))
	   (equal (order (normalizer h g))
	          (order g)))
  :hints (("Goal" :use (index-normalizer (:instance lagrange (h (normalizer h g)))))))

(defthm ordp-normalizer
  (implies (subgroupp h g)
           (ordp (elts (normalizer h g)) g))
  :hints (("Goal" :in-theory (enable normalizer))))

(defthmd posp-len-conjs-sub
  (implies (subgroupp h g)
           (posp (len (conjs-sub h g))))
  :hints (("Goal" :in-theory (disable member-conjs-sub)
                  :expand ((LEN (CONJS-SUB H G)))
                  :use ((:instance member-conjs-sub (x (e g)))))))

(defthmd len-conjs-sub-normalp
  (implies (and (subgroupp h g)
                (<= (len (conjs-sub h g)) 1))
	   (normalp h g))
  :hints (("Goal" :use (lcsn-1 normalizer-normp posp-len-conjs-sub
                        (:instance ordp-subgroup-equal (h (normalizer h g)))))))

