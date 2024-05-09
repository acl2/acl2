;; David M. Russinoff
;; david@russinoff.com
;; http://www.russinoff.com

(in-package "DM")

(local (include-book "support/actions"))

(include-book "cauchy")
(include-book "symmetric")

;;---------------------------------------------------------------------------------------------------
;; Group Actions
;;---------------------------------------------------------------------------------------------------

;; Informally, if g is a group and d is a dlist, an action of g on d is a function a: g x d -> d such 
;; that for s in d and x and y in g,
;;   (1) a((e g), s) = s
;;   (2) a(x, a(y, s)) = a((op x y g), s).
;; Formally, we shall define an action to be a table, similar to the operation table of a group.  Thus,
;; a is a matrix of dimensions (order g) x (len d), with (car a) = d.

(defmacro dom (a) `(car ,a))

;; Note that by definition, (order a) is just (len (domain a)).

;; a(x, s) is computed by a table look-up:

(defund act (x s a g)
  (nth (ind s a)
       (nth (ind x g) a)))

;; The first property above is automatic:

(defthm action-identity
  (implies (member-equal s (dom a))
           (equal (act (e g) s a g)
	          s)))

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
           (groupp g)))

(defthm actionp-dlistp
  (implies (actionp a g)
           (dlistp (dom a))))

(defthm actionp-pos-len
  (implies (actionp a g)
	   (posp (len (dom a)))))

(defthm ordp-a
  (implies (actionp a g)
           (ordp (dom a) a)))

  ;; Closure:

(defthm action-closure
  (implies (and (actionp a g)
                (in x g)
		(member-equal s (dom a)))
	   (member-equal (act x s a g) (dom a))))

;; Converse of action-closure is useful in proving closure of a purported action:

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

(defthmd action-aassoc
  (implies (and (actionp a g)                
                (in x g)
		(in y g)
		(in s a))
	   (equal (act x (act y s a g) a g)
		  (act (op x y g) s a g))))

;; Converse of action-aassoc is useful in proving associativity of a purported action::

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

;; Cancellation law:

(defthm action-cancel
  (implies (and (actionp a g)                
                (in x g)
		(in r a)
		(in s a)
		(equal (act x r a g) (act x s a g)))
	   (equal r s))
  :rule-classes ())

;; Every group is an action of itself on its element list.  Thus, we may view the notion of a group
;; action as a generalization of the notion of a group:

(defthm group-act
  (implies (and (groupp g)
                (in x g)
		(in s g))
	   (equal (act x s g g)
	          (op x s g))))

(defthmd actionp-group
  (implies (groupp g)
	   (actionp g g)))


;;---------------------------------------------------------------------------------------------------
;; Parametrized Group Actions
;;---------------------------------------------------------------------------------------------------

;; The macro defaction is based on the following encapsulation, which constrains three functions
;; representing the acting group, the domain of the action, and the values of the action:

(encapsulate (((agrp) => *) ((aelts) => *) ((aact * *) => *))
  (local (defun agrp () '((0))))
  (local (defun aelts () (list 0)))
  (local (defun aact (x y) (+ x y)))
  (defthm groupp-grp (groupp (agrp)))
  (defthm consp-aelts (consp (aelts)))
  (defthm dlistp-aelts (dlistp (aelts)))
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

(defthm aelts-elts
  (equal (dom (a))
         (aelts)))
	 
(defthm act-a-rewrite
  (implies (and (in x (agrp))
		(in s (a)))
           (equal (act x s (a) (agrp))
	          (aact x s)))		  )

(in-theory (disable a (a)))

(defthm actionp-a
  (actionp (a) (agrp)))

;; The macro defaction generates families of group actions through functional instantiation of the above results.

;; Parameters of defaction:

;; name: name of the generated action
;; args: a list of parameters
;; grp: the acting group
;; cond: a predicate that must be satisfied by args
;; elts: a list of the elements of the domain as a function of args
;; act: the result of a group element x acting on an element s of the domain

;; Prior to a call of defgroup, 6 rewrite rules corresponding to the theorems of the encapsulation must
;; be proved.

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
                       
(defaction act-lcosets (h) g
  (subgroupp h g)
  (lcosets h g)
  (lcoset (op x (car s) g) h g))

;; A group action of g induces an action by any subgroup of g:

(defaction subaction (a g) h
  (and (actionp a g)
       (subgroupp h g))
  (dom a)
  (act x s a g))


;;---------------------------------------------------------------------------------------------------
;; Orbits of an Action
;;---------------------------------------------------------------------------------------------------

;; Given s in the domain of an action a, the orbit of s is the ordered list of all r in (dom a) such 
;; that r = (act x s a g) for some x in g:

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

(defthm ordp-orbit
  (implies (and (actionp a g)
                (in s a))
	   (ordp (orbit s a g) a))
  :hints (("Goal" :in-theory (enable orbit))))

(defthm sublistp-orbit
  (implies (and (actionp a g)
                (member-equal s (dom a)))
	   (sublistp (orbit s a g) (dom a)))
  :hints (("Goal" :in-theory (enable orbit))))

;; Every orbit is a dlist:

(defthm dlistp-orbit
  (implies (groupp g)
           (dlistp (orbit s a g)))
  :hints (("Goal" :in-theory (enable orbit))))

;; Every element of the domain belongs to its own orbit:

(defthm member-self-orbit
  (implies (and (actionp a g)
                (member-equal s (dom a)))
	   (member-equal s (orbit s a g))))

;; If (act x s a g) = r, then r is in the orbit of s:

(defthmd member-act-orbit
  (implies (and (actionp a g)
                (in x g))
	   (member-equal (act x s a g) (orbit s a g))))

;; If r is in the orbit of s, then for some x, (act x s a g) = r:

(defun actor-aux (r s a g l)
  (if (consp l)
      (if (equal (act (car l) s a g) r)
          (car l)
	(actor-aux r s a g (cdr l)))
    ()))

(defund actor (r s a g)
  (actor-aux r s a g (elts g)))

(defthmd actor-acts
  (implies (and (actionp a g)
                (member-equal r (orbit s a g)))
	   (let ((x (actor r s a g)))
	     (and (in x g)
	          (equal (act x s a g) r)))))

;; If r is in the orbit of s, then the orbits of r and s are equal:

(defthmd equal-orbits
  (implies (and (actionp a g)
                (member-equal s (dom a))
                (member-equal r (orbit s a g)))
	   (equal (orbit r a g) (orbit s a g)))
  :hints (("Goal" :in-theory (enable permp)
                  :use (permp-orbit-orbit (:instance ordp-equal (g a) (x (orbit r a g)) (y (orbit s a g)))))))

;; Distinct orbits are disjoint:

(defthmd disjointp-orbits
  (implies (and (actionp a g)
                (member-equal s (dom a))
                (member-equal r (dom a))
		(not (equal (orbit r a g) (orbit s a g))))
	   (disjointp (orbit r a g) (orbit s a g))))

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

(defthm dlistp-orbits
  (implies (actionp a g)
           (dlistp (orbits a g))))

(defthm member-list-orbits
  (implies (and (actionp a g)
		(in x a))
           (member-list x (orbits a g))))

(defthmd member-orbits-orbit
  (implies (and (actionp a g)
		(member-equal x (orbits a g)))
	   (and (in (car x) a)
	        (equal (orbit (car x) a g) x))))

;; Appending the orbits yields a permutation of the domain:

(defthm orbits-pairwise-disjoint
  (implies (actionp a g)
	   (disjointp-pairwise (orbits a g))))

(defthm dlistp-list-orbits
  (implies (actionp a g)
	   (dlistp-list (orbits a g))))
  
(defthm dlistp-append-list-orbits
  (implies (actionp a g)
	   (dlistp (append-list (orbits a g)))))

(defthmd append-list-orbits
  (implies (actionp a g)
	   (permp (append-list (orbits a g))
		  (dom a))))

;; Note that the conjugacy class of x is the orbit of x under the conjugacy action:

(defthmd conjs-orbit
  (implies (and (groupp g)
	        (in x g))
	   (equal (conjs x g)
		  (orbit x (conjugacy g) g))))

;; Since (center g) consists of all orbits of length 1 and (conjs-list g) consists of all orbits of
;; length > 1, the class equation could be derived from append-list orbits and conjs-orbit:

;; (defthmd class-equation
;;   (implies (groupp g)
;;            (equal (len (append (elts (center g))
;;                                (append-list (conjs-list g))))
;;                   (order g))))


;;---------------------------------------------------------------------------------------------------
;; Stabilizer of a Domain Element
;;---------------------------------------------------------------------------------------------------

;; The stabilizer of an element s of the domain of an action a is the ordered subgroup of g comprising
;; all x such that (act x s a g) = s:

(defun stab-elts-aux (s a g l)
  (if (consp l)
      (if (equal (act (car l) s a g) s)
          (cons (car l) (stab-elts-aux s a g (cdr l)))
	(stab-elts-aux s a g (cdr l)))
    ()))

(defund stab-elts (s a g)
  (stab-elts-aux s a g (elts g)))

(defthm sublistp-stab-elts
  (implies (actionp a g)
	   (sublistp (stab-elts s a g) (elts g))))

(defthm ordp-stab-elts
  (implies (actionp a g)
	   (ordp (stab-elts s a g) g)))

(defthm dlistp-stab-elts
  (implies (actionp a g)
	   (dlistp (stab-elts s a g))))

(defthmd member-stab-elts
  (implies (and (actionp a g)
		(in x g))
	   (iff (member-equal x (stab-elts s a g))
	        (equal (act x s a g) s))))

(defthm stab-elts-closed
  (implies (and (actionp a g)
		(in s a)
		(in x g)
		(in y g)
		(member-equal x (stab-elts s a g))
		(member-equal y (stab-elts s a g)))
	   (member-equal (op x y g) (stab-elts s a g))))

(defthm stab-elts-inv
  (implies (and (actionp a g)
		(in s a)
		(in x g)
		(member-equal x (stab-elts s a g)))
	   (member-equal (inv x g) (stab-elts s a g))))

(defthm car-stab-elts
  (implies (and (actionp a g)
		(in s a))
	   (equal (car (stab-elts s a g))
	          (e g))))

(defthm consp-stab-elts
  (implies (and (actionp a g)
		(in s a))
	   (consp (stab-elts s a g))))

(defsubgroup stabilizer (s a) g
  (and (actionp a g)
       (member-equal s (dom a)))
  (stab-elts s a g))

(defthmd stabilizer-subaction
  (implies (and (actionp a g)
		(subgroupp h g)
		(in s a)
		(in x h))
	   (iff (in x (stabilizer s (subaction a g h) h))
	        (in x (stabilizer s a g)))))

;; We shall define a bijection from (lcosets (stabilizer s a g) g) to (orbit s a g),
;; and conclude that the 2 lists have the same length:

(defund lcosets2orbit (c s a g)
  (act (car c) s a g))

;; Inverse bijection:

(defund orbit2lcosets (r s a g)
  (lcoset (actor r s a g) (stabilizer s a g) g))

(defthm lcosets2orbit-1-1
  (implies (and (actionp a g)
		(in s a)
		(member-equal c (lcosets (stabilizer s a g) g)))
           (and (member-equal (lcosets2orbit c s a g) (orbit s a g))
	        (equal (orbit2lcosets (lcosets2orbit c s a g) s a g)
		       c))))

(defthm orbit2lcosets-1-1
  (implies (and (actionp a g)
		(in s a)
		(member-equal r (orbit s a g)))
           (and (member-equal (orbit2lcosets r s a g) (lcosets (stabilizer s a g) g))
	        (equal (lcosets2orbit (orbit2lcosets r s a g) s a g)
		       r))))

;; Functional instantiation of len-1-1-equal yields the following:

(defthm len-orbit-lcosets
  (implies (and (actionp a g)
		(in s a))
	   (equal (len (orbit s a g))
	          (len (lcosets (stabilizer s a g) g)))))

;; The following is a consequence of Lagrange's Theorem:

(defthmd stabilizer-orbit
  (implies (and (actionp a g)
		(in s a))
	   (equal (* (order (stabilizer s a g))
		     (len (orbit s a g)))
		  (order g))))

(defthmd len-orbit-divides
  (implies (and (actionp a g)
		(in s a))
	   (divides (len (orbit s a g))
		    (order g))))

;; Note that the centralizer of x is its stabilizer under the conjugacy action:

(defthmd centralizer-stabilizer
  (implies (and (groupp g)
		(in x g))
	   (equal (centralizer x g)
		  (stabilizer x (conjugacy g) g))))

;; Consequently, the lemma len-conjs-cosets could be derived from conjs-orbit and stabilizer-orbit:

;; (defthm len-conjs-cosets
;;   (implies (and (groupp g) (in x g))
;;            (equal (len (conjs x g))
;; 	             (subgroup-index (centralizer x g) g))))


;;---------------------------------------------------------------------------------------------------
;; Conjugate Subgroups
;;---------------------------------------------------------------------------------------------------

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

(defthm ordp-conj-sub-list
  (implies (and (subgroupp h g)
		(in a g))
	   (ordp (conj-sub-list h a g) g)))

(defthm sublistp-conj-sub-list
  (implies (and (subgroupp h g)
		(in a g))
	   (sublistp (conj-sub-list h a g) (elts g))))

(defthm conj-sub-list-non-nil
  (implies (and (subgroupp h g)
		(in a g))
	   (not (member-equal () (conj-sub-list h a g)))))

(defthmd member-conj-sub-list
  (implies (and (subgroupp h g)
		(in a g)
		(in x g))
	   (iff (member-equal x (conj-sub-list h a g))
	        (in (conj x (inv a g) g) h))))

(defthm dlistp-conj-sub-list
  (implies (and (subgroupp h g)
		(in a g))
	   (dlistp (conj-sub-list h a g))))

(defthmd e-in-conj-sub-list
  (implies (and (subgroupp h g)
		(in a g))
	   (member-equal (e g) (conj-sub-list h a g)))	   )

(defthm car-conj-sub-list
  (implies (and (subgroupp h g)
		(in a g))
	   (equal (car (conj-sub-list h a g))
	          (e g))))

(defthm consp-conj-sub-list
  (implies (and (subgroupp h g)
		(in a g))
	   (consp (conj-sub-list h a g))))

(defthm conj-sub-list-closed
  (implies (and (subgroupp h g)
		(in a g)
		(member-equal x (conj-sub-list h a g))
		(member-equal y (conj-sub-list h a g)))
           (member-equal (op x y g) (conj-sub-list h a g))))

(defthm conj-sub-list-inv
  (implies (and (subgroupp h g)
		(in a g)
		(member-equal x (conj-sub-list h a g)))
           (member-equal (inv x g) (conj-sub-list h a g))))

(defsubgroup conj-sub (h a) g
  (and (subgroupp h g)
       (in a g))
  (conj-sub-list h a g))

;; Conjugate subgroups have the same order:

(defthm order-conj-sub
  (implies (and (subgroupp h g)
		(in a g))
	   (equal (order (conj-sub h a g))
	          (order h))))

;; A subgroup h of g need not be ordered with respect to g, but (conj-sub h (e g) g) is an ordered
;; subgroup of g with the same elements as h:

(defthmd permp-conj-sub-e
  (implies (subgroupp h g)
	   (permp (elts (conj-sub h (e g) g)) (elts h))))

(defthm member-conj-sub-e
  (implies (and (subgroupp h g)
                (in x g))
	   (iff (in x (conj-sub h (e g) g))
	        (in x h))))

(defthmd subgroupp-conj-sub-e
  (implies (subgroupp h g)
	   (subgroupp h (conj-sub h (e g) g))))

(defthmd orpd-h-conj-sub
  (implies (and (subgroupp h g)
		(ordp (elts h) g))
	   (equal (conj-sub h (e g) g)
	          h)))

(defthmd equal-conj-sub-a-b
  (implies (and (subgroupp h g)
		(in a g)
		(in b g))
	   (equal (conj-sub (conj-sub h b g) a g)
	          (conj-sub h (op a b g) g))))

(defthmd conj-sub-conj-sub-e
  (implies (and (subgroupp h g)
		(in x g))
	   (equal (conj-sub (conj-sub h (e g) g) x g)
	          (conj-sub h x g))))

;; If one conjugate of h is a subgroup of another, then they are equal:

(defthmd conj-subgroup-equal
  (implies (and (subgroupp h g)
		(in a g)
		(in b g)
                (subgroupp (conj-sub h a g) (conj-sub h b g)))
	   (equal (conj-sub h a g) (conj-sub h b g))))

;; Therefore, (conj-sub h (e g) g) is the only conjugate of h that includes h:

(defthmd conj-sub-subgroup-e
  (implies (and (subgroupp h g)
                (in a g)
		(subgroupp h (conj-sub h a g)))
	   (equal (conj-sub h a g)
	          (conj-sub h (e g) g))))

;; The stabilizer of an element of the orbit of s is a conjugate of the stabilizer of s:

(defthmd conj-stabilizer
  (implies (and (actionp a g)
		(in s a)
		(in x g))
	   (equal (stabilizer (act x s a g) a g)
	          (conj-sub (stabilizer s a g) x g))))

;;---------------------------------------------------------------------------------------------------
;; Conjugation of Subgroups as a Group Action
;;---------------------------------------------------------------------------------------------------

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

(defthm dlistp-conjs-sub
  (dlistp (conjs-sub h g)))

;; (conjs-sub h g) contains every conjugate of h:

(defthm member-conjs-sub
  (implies (and (subgroupp h g)
                (in x g))
           (member-equal (conj-sub h x g)
	                 (conjs-sub h g))))

;; (conjs-sub h g) contains only conjugates of h:

(defun conjer-sub-aux (k h g l)
  (if (consp l)
      (if (equal k (conj-sub h (car l) g))
          (car l)
	(conjer-sub-aux k h g (cdr l)))
    ()))

(defund conjer-sub (k h g)
  (conjer-sub-aux k h g (elts g)))

(defthmd conjs-sub-conjer
  (implies (and (subgroupp h g)
		(member-equal k (conjs-sub h g)))
	   (and (in (conjer-sub k h g) g)
	        (equal (conj-sub h (conjer-sub k h g) g)
	               k))))

;; Every conjugate of a subgroup of g is a subgroup of g:

(defthm subgroupp-conjs-sub
  (implies (and (subgroupp h g)
		(member-equal k (conjs-sub h g)))
	   (subgroupp k g)))

;; h is a subgroup of exactly one member of (conjs-sub h g):

(defthmd conjs-sub-subgroup
  (implies (and (subgroupp h g)
		(member-equal k (conjs-sub h g)))
           (iff (subgroupp h k)
	        (equal k (conj-sub h (e g) g)))))

(defthm conjs-sub-not-subgroup
  (implies (and (subgroupp h g)
		(member-equal k1 (conjs-sub h g))
		(member-equal k2 (conjs-sub h g))
		(subgroupp k1 k2))
	   (equal k2 k1))
  :rule-classes ())

;; If (conjs-sub h g) has length 1, then h is normal in g:

(defthmd len-conjs-sub-normalp
  (implies (and (subgroupp h g)
                (<= (len (conjs-sub h g)) 1))
	   (normalp h g)))

  ;; A conjugate of a subgroup h of g has the same conjugates as h:

(defthm permp-conjs-sub
  (implies (and (subgroupp h g)
		(in x g))
	   (permp (conjs-sub (conj-sub h x g) g)
	          (conjs-sub h g))))

(defthmd member-conjs-sub-self
  (implies (and (subgroupp m g)
		(member c (conjs-sub m g)))
           (member-equal c (conjs-sub c g))))

;;  The group action axioms:

(defthm conjs-sub-identity
  (implies (and (subgroupp h g)
                (member-equal s (conjs-sub h g)))
	   (equal (conj-sub s (e g) g) s)))

(defthm conjs-sub-assoc
  (implies (and (subgroupp h g)
                (member-equal s (conjs-sub h g))
		(in x g)
		(in y g))
	   (equal (conj-sub s (op x y g) g)
	          (conj-sub (conj-sub s y g) x g))))

(defthm conjs-sub-closed
  (implies (and (subgroupp h g)
                (member-equal s (conjs-sub h g))
		(in x g))
	   (member-equal (conj-sub s x g) (conjs-sub h g))))

(defaction conj-sub-act (h) g (subgroupp h g) (conjs-sub h g) (conj-sub s x g))


;;---------------------------------------------------------------------------------------------------
;; Normalizers
;;---------------------------------------------------------------------------------------------------

;; We define the normalizer of a subgroup h of g to be the stabilizer of (conj-sub h (e g) g):

(defund normalizer (h g)
  (stabilizer (conj-sub h (e g) g)
	      (conj-sub-act h g)
	      g))

(defthm groupp-normalizer
  (implies (subgroupp h g)
           (groupp (normalizer h g))))

(defthm subgroupp-normalizer
  (implies (subgroupp h g)
           (subgroupp (normalizer h g) g)))

(defthmd index-normalizer
  (implies (subgroupp h g)
           (equal (len (conjs-sub h g))
	          (subgroup-index (normalizer h g) g))))

(defthmd subgroup-of-normalizer
  (implies (subgroupp h g)
           (subgroupp h (normalizer h g))))

(defthmd normalizer-elts
  (implies (and (subgroupp h g)
		(in x g))
	   (iff (in x (normalizer h g))
		(equal (conj-sub h x g)
		       (conj-sub h (e g) g)))))

;; A subgroup is a normal subgroup of its normalizer:

(defthmd normalizer-conj
  (implies (and (subgroupp h g)
		(in x (normalizer h g))
	        (in y h))
	   (in (conj y x g) h)))

(defthmd normalizer-normp
  (implies (subgroupp h g)
           (normalp h (normalizer h g))))

;; On the other hand, if x is not in (normalizer h g), then we can find y in h such that (conj y x g) is not in h:

(defund normalizer-cex (x h g)
  (conj (scex1 (conj-sub-list h x g) (conj-sub-list h (e g) g)) (inv x g) g))

(defthmd normalizer-cex-lemma
  (implies (and (subgroupp h g)
                (in x g)
		(not (in x (normalizer h g))))
	   (let ((y (normalizer-cex x h g)))
	     (and (in y h)
	          (not (in (conj y x g) h))))))

;; The normalizer of a conjugte of h is a conjugate of the normalizer of h:

(defthmd normalizer-conj-sub
  (implies (and (subgroupp m g)
		(member-equal c (conjs-sub m g)))
	   (equal (normalizer c g)
		  (conj-sub (normalizer m g) (conjer-sub c m g) g))))


;;---------------------------------------------------------------------------------------------------
;; Induced Hormomorphism from g to (sym (order a))
;;---------------------------------------------------------------------------------------------------

;; An action a of a group g associates each element of g with a permutation of (dom a).
;; By identifying an element of (dom a) with its index, we have an element of (sym n),
;; where n = (order a).  If x is in g and p is the element of (sym n) corresponding to x,
;; then for 0 <= k < n, the image of k under p is computed by the following:

(defund act-perm-val (x k a g)
  (index (act x (nth k (dom a)) a g)
         (dom a)))

;; The element of (sym n) corresponding to x:

(defun act-perm-aux (x k a g)
  (if (zp k)
      ()
    (append (act-perm-aux x (1- k) a g)
            (list (act-perm-val x (1- k) a g)))))

(defund act-perm (x a g)
  (act-perm-aux x (order a) a g))

(defthmd act-perm-is-perm
  (implies (and (actionp a g)
                (in x g))
	   (in (act-perm x a g)
	       (sym (order a)))))

(defthm act-perm-val-is-val
  (implies (and (actionp a g)
                (in x g)
		(member-equal k (ninit (order a))))
	   (equal (nth k (act-perm x a g))
	          (act-perm-val x k a g))))

;; The identity of g corresponds to the identity of (sym n):

(defthmd act-perm-e
  (implies (actionp a g)
	   (equal (act-perm (e g) a g)
	          (ninit (order a)))))

;; The group operation is preserved by this correspondence:

(defthmd act-perm-comp
  (implies (and (actionp a g)
                (in x g)
		(in y g))
	   (equal (act-perm (op x y g) a g)
	          (comp-perm (act-perm x a g)
		             (act-perm y a g)
			     (order a)))))

;; Thus, we have a homomorphism from g into the symmetric group:

(defmap act-sym (a g)
  (elts g)
  (act-perm x a g))

(defthmd homomorphismp-act-sym
  (implies (actionp a g)
           (homomorphismp (act-sym a g)
	                  g
			  (sym (order a)))))

;; An element of the kernel of (act-sym a g) acts trivially on every element of (dom a):

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
;; subgroup of (sym (order g)):

(defthm endomorphismp-act-sym-g
  (implies (groupp g)
	   (endomorphismp (act-sym g g) g (sym (order g)))))

;; Recall the action act-lcosets of a group g on the left cosets of a subgroup h.
;; The kernel of the homomorphism induced by this action is a subgroup of h:

(defthmd subgroup-kernel-act-cosets
  (implies (subgroupp h g)
	   (subgroupp (kernel (act-sym (act-lcosets h g) g)
	                      (sym (subgroup-index h g))
			      g)
		      h)))

;; The preceding result has the following important consequence:

;; LEMMA: Let p be the least prime dividing (order g) and suppose the index of h in g is p.
;; Then h is normal in g.

;; Proof: Let k = (kernel (act-sym (act-cosets h g) g) (sym (subgroup-index h g)) g).
;; We have shown that k is normal in g.
;; By endomorphismp-quotient-map, (quotient g k) is isomorphic to a subgroup of (sym p),
;; and therefore (subgroup-index k g) divides p!, which implies (subgroup-index k h) divides (p-1)!.
;; If (subgroup-index k h) > 1, then (subgroup-index k g) has a prime divisor q.  Since q divides (p-1)!,
;; q < p. (This may be proved by induction on p as a consequence of euclid.)
;; But since q divides (order g), q >= p by assumption, a contradiction.  Thus, (subgroup-index k h) = 1,
;; which implies (permp (elts k) (elts h)), and by permp-normalp, h is normal in g.

(defthmd index-least-divisor-normal
  (implies (and (subgroupp h g)
                (> (order g) 1)
		(equal (subgroup-index h g)
		       (least-prime-divisor (order g))))
	   (normalp h g)))

