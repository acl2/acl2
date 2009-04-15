(in-package "ALIST")

(include-book "set" :dir :lists)
(include-book "keyquiv")
(include-book "good-rewrite-order" :dir :util)
(include-book "nary" :dir :nary)

(defun subkeyquivp (list x y)
  (declare (type t list x y))
  (and (list::setequiv (list::setintersection list (alist::keys x))
		       (list::setintersection list (alist::keys y)))
       (list::setequiv (list::setdifference list (alist::keys x))
		       (list::setdifference list (alist::keys y)))
       (alist::assoc-equiv list x y)))

;; must prove for an arbitrary member of list:

(defthmd open-subkeyquivp
  (equal (subkeyquivp list x y)
	 (if (consp list)
	     (and (cons-equiv (assoc (car list) x)
			      (assoc (car list) y))
		  (equal (list::memberp (car list) (alist::keys x))
			 (list::memberp (car list) (alist::keys y)))
		  (subkeyquivp (cdr list) x y))
	   t))
  :hints (("Goal" :do-not-induct t
	   :in-theory (enable assoc-equiv
			      list::memberp
			      LIST::OPEN-SETEQUIV-ON-CONSP-1
			      LIST::SETINTERSECTION
			      list::setdifference))
	  (and stable-under-simplificationp
	       (acl2::occur-lst 'LIST::ARBITRARY-ELEMENT clause)
	       `(:cases ((equal (car list) LIST::ARBITRARY-ELEMENT)))))
  :rule-classes (:definition))

(encapsulate
 ()

 (encapsulate
  (((subkeyquiv-hyps) => *)
   ((subkeyquiv-list) => *)
   ((subkeyquiv-lhs) => *)
   ((subkeyquiv-rhs) => *))
  
  (local (defun subkeyquiv-hyps () nil))
  (local (defun subkeyquiv-lhs  () nil))
  (local (defun subkeyquiv-rhs  () nil))
  (local (defun subkeyquiv-list () nil))
  
  (defthm subkeyquiv-multiplicity-constraint
    (implies 
     (and
      (subkeyquiv-hyps)
      (memberp arbitrary-element (subkeyquiv-list)))
     (and (cons-equiv (assoc arbitrary-element (subkeyquiv-lhs))
		      (assoc arbitrary-element (subkeyquiv-rhs)))
	  (equal (memberp arbitrary-element (keys (subkeyquiv-lhs)))
		 (memberp arbitrary-element (keys (subkeyquiv-rhs))))))
    :rule-classes nil)
  )

 (local (defun badguy (list x y)
          (cond ((atom list)
                 nil)
                ((not (cons-equiv (assoc (car list) x)
				  (assoc (car list) y)))
                 (list (car list)))
                ((not (equal (list::memberp (car list) (alist::keys x))
			     (list::memberp (car list) (alist::keys y))))
                 (list (car list)))
                (t (badguy (cdr list) x y)))))
 
 (local (defthm badguy-witness
	  (equal (subkeyquivp list x y)
		 (null (badguy list x y)))
	  :hints (("Goal" :in-theory (e/d (open-subkeyquivp) (subkeyquivp))
		   :induct (badguy list x y)))))

 (local (defthm badguy-memberp
	  (implies
	   (badguy list x y)
	   (memberp (car (badguy list x y)) list))))

 (local (defthm badguy-implication
	  (implies
	   (badguy list x y)
	   (not (and (cons-equiv (assoc (car (badguy list x y)) x)
				 (assoc (car (badguy list x y)) y))
		     (equal (memberp (car (badguy list x y)) (keys x))
			    (memberp (car (badguy list x y)) (keys y))))))
	  :rule-classes nil))
       
 (defthm subkeyquiv-by-multiplicity-driver
   (implies (subkeyquiv-hyps)
            (subkeyquivp (subkeyquiv-list) (subkeyquiv-lhs) (subkeyquiv-rhs)))
   :rule-classes nil
   :hints(("Goal" 
           :use ((:instance 
                  subkeyquiv-multiplicity-constraint
                  (arbitrary-element (car (badguy (subkeyquiv-list) (subkeyquiv-lhs) (subkeyquiv-rhs)))))
		 (:instance
		  badguy-implication
		  (list (subkeyquiv-list))
		  (x    (subkeyquiv-lhs))
		  (y    (subkeyquiv-rhs)))))))

 (ADVISER::defadvice subkeyquiv-by-multiplicity
   (implies (subkeyquiv-hyps)
	    (subkeyquivp (subkeyquiv-list) (subkeyquiv-lhs) (subkeyquiv-rhs)))
   :rule-classes (:pick-a-point :driver subkeyquiv-by-multiplicity-driver))

 )

;; You *must* do this .. the loop-stopper

(defthm subkeyquivp-commute
  (implies
   (syntaxp (acl2::good-rewrite-order x y))
   (equal (subkeyquivp list y x)
	  (subkeyquivp list x y)))
  :rule-classes ((:rewrite :loop-stopper nil)))

;; The following rules are the key to being able to disable the
;; equivalence relation as early as possible and begin to rely on the
;; pick-a-point strategy.  You need to show congruence for the
;; aftermath of the pick-a-point modulo the original equivalence
;; relation.

(defthm memberp-keys-replacement
  (implies
   (and
    (subkeyquivp list x y)
    (list::memberp a list)
    (syntaxp (acl2::good-rewrite-order x y)))
   (equal (list::memberp a (alist::keys x))
	  (list::memberp a (alist::keys y)))))

(defthm cons-equiv-assoc-replacement
  (implies
   (and
    (subkeyquivp list x y)
    (list::memberp a list)
    (syntaxp (acl2::good-rewrite-order x y)))
   (cons-equiv (assoc a x)
	       (assoc a y))))

(in-theory (disable subkeyquivp))

(defthm subkeyquivp-chaining-1
  (implies
   (and
    (subkeyquivp list x a)
    (subkeyquivp list y x))
   (and (subkeyquivp list y a)
	(subkeyquivp list a y)))
  :rule-classes (:forward-chaining))

(defthm subkeyquivp-chaining-2
  (implies
   (and
    (subkeyquivp list x a)
    (subkeyquivp list x y))
   (and (subkeyquivp list y a)
	(subkeyquivp list a y)))
  :rule-classes (:forward-chaining))

(defthm subkeyquivp-chaining-3
  (implies
   (and
    (subkeyquivp list a x)
    (subkeyquivp list y x))
   (and (subkeyquivp list y a)
	(subkeyquivp list a y)))
  :rule-classes (:forward-chaining))

(defcong keyquiv equal (subkeyquivp list x y) 2)
(defcong keyquiv equal (subkeyquivp list x y) 3)
(defcong list::setequiv equal (subkeyquivp list x y) 1)

(defthm subkeyquivp-id
  (subkeyquivp list x x))

(defthmd subkeyquivp-commute-forward
  (implies
   (subkeyquivp list x y)
   (subkeyquivp list y x))
  :rule-classes (:forward-chaining))

(acl2::defequiv+ (subkeyquivp domain x y)
  :lhs x
  :rhs y
  :equiv   subkeyquiv
  :context subkeyquiv-ctx
  :keywords t
  :chaining t
  :congruences ((domain list::setequiv)
 	        (x      alist::keyquiv)
 		(y      alist::keyquiv))
  )

;; Would we rather do this .. or normalize our expressions in the
;; hypothesis?

(defthm subkeyquivp-cong
  (implies
   (acl2::bind-contextp ((x (equal a (subkeyquiv-ctx x)))
			 (y (equal b (subkeyquiv-ctx y)))))
   (equal (subkeyquivp domain x y)
	  (acl2::skip-rewrite (subkeyquivp domain a b)))))

(defthm subkeyquiv-replacement
  (implies
   (and
    (subkeyquivp list x y)
    (syntaxp (acl2::good-rewrite-order x y))
    (list::subsetp domain list))
   (subkeyquiv :lhs x
	       :rhs y)))

(defthm assoc-subkeyquivp-cong
  (implies
   (and
    (list::setequiv domain (double-rewrite (list key)))
    (acl2::bind-contextp ((x (equal a (subkeyquiv-ctx x :domain domain))))))
   (cons-equiv (assoc key x)
	       (acl2::skip-rewrite (assoc key a)))))

(defthm cons-subkeyquivp-cong
  (implies
   (and
    (list::setequiv newdomain (double-rewrite (list::remove (car pair) domain)))
    (acl2::bind-contextp ((x (equal a (subkeyquiv-ctx x :domain newdomain))))))
   (subkeyquiv :lhs (cons pair x)
	       :rhs (cons pair a))))

(defthm subkeyquiv-drop-cons
  (implies
   (not (list::memberp (car pair) domain))
   (subkeyquiv :lhs (cons pair y)
	       :rhs y)))

(defthm acons-subkeyquivp-cong
  (implies
   (and
    (list::setequiv newdomain (double-rewrite (list::remove key domain)))
    (acl2::bind-contextp ((x (equal a (subkeyquiv-ctx x :domain newdomain))))))
   (subkeyquiv :lhs (acons key v x)
	       :rhs (acons key v a))))

(defthm subkeyquiv-drop-acons
  (implies
   (not (list::memberp key domain))
   (subkeyquiv :lhs (acons key value y)
	       :rhs y)))

;; This could be stronger .. if we allowed ourselves to compute the
;; domain of x.  Is it worth it?

(defthm append-subkeyquivp-cong
  (implies
   (acl2::bind-contextp ((x (equal a (subkeyquiv-ctx x)))
			 (y (equal b (subkeyquiv-ctx y)))))
   (subkeyquiv :lhs (append x y)
	       :rhs (append a b))))

