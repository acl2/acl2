(in-package "ACL2")

;; Several theorems we need are about universal closures of formulas:
;; (alls (free-vars f) f).  These will be proved first for an arbitrary
;; set of variables that closes the formulas.  But when we go to prove
;; the theorems in terms of universal closure, the variables aren't
;; necessarily in the correct order, and there might me too many variables.
;;
;; The main theorem in this file (xeval-alls-subset) brings things together:
;;
;; If A is a subset of variable-set B, and if (ALLS A F) is closed,
;; then (ALLS A F) is equivalent to (ALLS B F).
;;
;; The proof uses the special-purpose evaluation function keval.

(include-book "keval")
(include-book "permutations")
(include-book "../../../../../ordinals/e0-ordinal")
(set-well-founded-relation e0-ord-<)

(local (include-book "arithmetic"))

(local (in-theory (enable domain-term)))

;; Note that this book uses both remove-equal and remove1-equal.  We could
;; probably use one or the other exclusively, because we are dealing
;; with var-set.

(defthm var-set-remove1-equal
  (implies (var-set v)
	   (var-set (remove1-equal x v))))

(defthm idx-cancel-not-member
  (implies (equal (+ 1 (idx a1 b2)) 1)
	   (not (member-equal a1 b2))))

;; Many of the following theorems are separated into two cases:
;; whether or not (car b) is equal to a1.
;;
;; Comment added long after these proofs were done:  I just learned
;; about the :cases hint;  I guess it could be used to clean this
;; up quite a bit.

;;-----------------  closer

(defthm closer-1
  (implies (and (integerp e)
		(<= 0 e)
		(variable-term a1)
		(var-set b)
		(member-equal a1 b)
		(equal (car b) a1))
	   (equal (xeval (alls (remove1-equal a1 b)
			       (subst-free f a1 e))
			 (domain i) i)
		  (keval b f (domain i) (idx a1 b)
			 e i)))
  :hints (("goal"
	   :do-not-induct t))
  :rule-classes nil)

; JSM: I added these two events when I eliminated the worse-than test
; in ancestors-check.  Member-equal-append, especially, is a real
; killer if you take a brute force approach to backchain cutoff.

(in-theory (disable  member-append-right
                     member-append-left
                     member-equal-append))

(defthm member-equal-append-strong
  (iff (member-equal x (append a b))
       (or (member-equal x a)
           (member-equal x b))))

(defthm closer-2
  (implies (and (integerp e)
		(<= 0 e)
		(variable-term a1)
		(var-set b)
		(member-equal a1 b)
		(not (equal (car b) a1))
		(domain-term-list (fringe dm)))
	   (equal (xeval (alls (remove1-equal a1 b) (subst-free f a1 e))
			 dm i)
		  (keval b f dm (idx a1 b)
			 e i)))
  :hints (("goal"
	   :induct (keval-i b f dm (idx a1 b) e i)
	   :expand ((keval (list* b1 b3 b4) f dm 2 e i))))
  :rule-classes nil)

(defthm closer
  (implies (and (integerp e)
		(<= 0 e)
		(variable-term a1)
		(var-set b)
		(member-equal a1 b))
	   (equal (xeval (alls (remove1-equal a1 b) (subst-free f a1 e))
			 (domain i) i)
		  (keval b f (domain i) (idx a1 b)
			 e i)))
  :hints (("goal"
	   :do-not-induct t
	   :use ((:instance closer-1)
		 (:instance closer-2 (dm (domain i)))))))

;;---------------- side step to prove xeval-alls-free

(in-theory (enable not-free-not-change-2))

(defthm no-vars-subst-free
  (implies (not (free-vars f))
	   (equal (subst-free f x tm) f)))

(defthm not-free-quant-xeval-2
  (implies (and (domain-term-list (fringe dom))
		(variable-term x)
                (not (free-vars f)))
           (equal (xeval (list 'all x f) dom i)
                  (xeval f (domain i) i)))
  :hints (("goal"
           :in-theory (disable domain-term)
           :induct (dom-i dom))))

(in-theory (disable not-free-not-change-2 no-vars-subst-free))

(defthm xeval-alls-free
  (implies (and (var-list b)
		(not (free-vars f)))
	   (equal (xeval (alls b f) (domain i) i)
		  (xeval f (domain i) i)))
  :hints (("goal"
	   :induct (alls b f)
	   :in-theory (disable domain-term))))

;;---------------- end of side step

(defthm xeval-alls-free-expanded
  (implies (and (var-list b)
                (not (free-vars f)))
           (equal (xeval (alls b f) (domain i) i)
                  (xeval f (domain i) i)))
  :hints (("goal"
	   :use ((:instance xeval-alls-free (i i))))))

(defthm base-1
  (implies (and (integerp dom)
		(<= 0 dom)
		(variable-term a1)
		(var-set b)
		(member-equal a1 b)
		(not (remove-equal a1 (free-vars f)))
		(equal (car b) a1))
	   (equal (keval b f (domain i) (idx a1 b) dom i)
		  (xeval (subst-free f a1 dom) (domain i) i)))
  :hints (("goal"
           :do-not-induct t))
  :rule-classes nil)

(defthm if-x-is-only-member-then-something-else-isnt-member  ;; duh
  (implies (and (not (equal x y))
		(not (remove-equal x a)))
	   (not (member-equal y a)))
  :rule-classes nil)

(defthm not-free-not-change-remove
  (implies (and (not (equal x y))
		(not (remove-equal x (free-vars f))))
	   (equal (subst-free f y tm) f))
  :hints (("goal"
	   :do-not-induct t
	   :in-theory (enable not-free-not-change-2)
           :use ((:instance if-x-is-only-member-then-something-else-isnt-member
			    (a (free-vars f)))))))

(defthm base-2
  (implies (and (integerp dom)
		(<= 0 dom)
		(variable-term a1)
		(var-set b)
		(member-equal a1 b)
		(not (remove-equal a1 (free-vars f)))
		(not (equal (car b) a1))
		(domain-term-list (fringe dm)))
	   (equal (keval b f dm (idx a1 b) dom i)
		  (xeval (subst-free f a1 dom) (domain i) i)))
  :hints (("goal"
	   :do-not generalize
           :induct (keval-i b f dm (idx a1 b) dom i)))
  :rule-classes nil)

(defthm base  ;; important case of the big one.
  (implies (and (integerp dom)
		(<= 0 dom)
		(variable-term a1)
		(var-set b)
		(member-equal a1 b)
		(not (remove-equal a1 (free-vars f))))
	   (equal (keval b f (domain i) (idx a1 b) dom i)
		  (xeval (subst-free f a1 dom) (domain i) i)))
  :hints (("goal"
	   :do-not-induct t
	   :use ((:instance base-1)
		 (:instance base-2 (dm (domain i)))))))

;;------------ ugly-a  Subgoal *1/2.10'7' of the big one

(defthm ugly-a1
  (implies (and (not (keval b f (domain i) (idx a1 b) dom1 i))
		(equal (car b) a1))
	   (not (keval b f (domain i) (idx a1 b) (cons dom1 dom2) i)))
  :hints (("goal"
	   :do-not-induct t))
  :rule-classes nil)

(defthm ugly-a2
  (implies (and (domain-term-list (append (fringe dom1) (fringe dom2)))
		(variable-term a1)
		(var-set b)
		(member-equal a1 b)
		(not (keval b f dm (idx a1 b) dom1 i))
		(not (equal (car b) a1))
		(domain-term-list (fringe dm)))
	   (not (keval b f dm (idx a1 b) (cons dom1 dom2) i)))
  :hints (("goal"
	   :induct (keval-i b f dm (idx a1 b) dom1 i)
	   :expand (keval (list* b1 b3 b4) f dm 2 (cons dom1 dom2)
			  i)
	   ))
  :rule-classes nil)

(defthm ugly-a
  (implies (and (domain-term-list (append (fringe dom1) (fringe dom2)))
		(variable-term a1)
		(var-set b)
		(member-equal a1 b)
		(not (keval b f (domain i) (idx a1 b) dom1 i)))
	   (not (keval b f (domain i) (idx a1 b) (cons dom1 dom2) i)))
  :hints (("goal"
	   :do-not-induct t
	   :use ((:instance ugly-a1)
		 (:instance ugly-a2 (dm (domain i)))))))

;;---------- ugly-d

(defthm ugly-d1
  (implies (and (keval b f (domain i) (idx a1 b) dom1 i)
		(equal (car b) a1))
	   (equal
	    (keval b f (domain i) (idx a1 b) (cons dom1 dom2) i)
	    (keval b f (domain i) (idx a1 b) dom2 i)))
  :hints (("goal"
	   :do-not-induct t))
  :rule-classes nil)

(defthm ugly-d2
  (implies (and (domain-term-list (append (fringe dom1) (fringe dom2)))
		(variable-term a1)
		(var-set b)
		(member-equal a1 b)
		(keval b f dm (idx a1 b) dom1 i)
		(not (equal (car b) a1))
		(domain-term-list (fringe dm)))
	   (equal
	    (keval b f dm (idx a1 b) (cons dom1 dom2) i)
	    (keval b f dm (idx a1 b) dom2 i)))
  :hints (("goal"
	   :induct (keval-i b f dm (idx a1 b) dom1 i)
	   :in-theory (disable ugly-a)
	   :expand ((keval (list* b1 b3 b4) f dm 2 (cons dom1 dom2)
			   i))))
  :rule-classes nil)

(defthm ugly-d
  (implies (and (domain-term-list (append (fringe dom1) (fringe dom2)))
		(variable-term a1)
		(var-set b)
		(member-equal a1 b)
		(keval b f (domain i) (idx a1 b) dom1 i)
		)
	   (equal
	    (keval b f (domain i) (idx a1 b) (cons dom1 dom2) i)
	    (keval b f (domain i) (idx a1 b) dom2 i)))
  :hints (("goal"
	   :do-not-induct t
	   :use ((:instance ugly-d1)
		 (:instance ugly-d2 (dm (domain i)))))))

;; Induction scheme for the big one.

(defun giv2 (v w f dom i)
  (declare (xargs :measure (cons (+ 1 (acl2-count v)) (acl2-count dom))
                  :guard (and (var-list v) (var-list w) (wff f)
                              (domain-term-list (fringe dom)))))
  (if (atom v)
      nil
      (if (atom dom)
          (giv2 (cdr v) (remove1-equal (car v) w)
		(subst-free f (car v) dom) (domain i) i)
          (cons (giv2 v w f (car dom) i)
                (giv2 v w f (cdr dom) i)))))

;;-------------------------------
;; The big one: first the cons case, then the atom case, then put
;; together those 2 cases, then get it in final form.

(defthm keval-alls-subset-cons
  (implies (and (domain-term-list (fringe dom))
		(var-set a)
		(var-set b)
		(subsetp-equal a b)
		(not (free-vars (alls a f)))
		(consp a))
	   (equal (xeval (alls a f) dom i)
		  (keval b f (domain i) (idx (car a) b) dom i)))
  :hints (("goal"
	   :induct (giv2 a b f dom i)
	   ))
  :rule-classes nil)

(defthm keval-alls-subset-atom
  (implies (and (var-set a)
		(var-set b)
		(subsetp-equal a b)
		(not (free-vars (alls a f)))
		(atom a))
	   (equal (xeval (alls a f) (domain i) i)
		  (keval b f (domain i) (idx (car a) b) (domain i) i)))
  :hints (("goal"
	   :do-not-induct t))
  :rule-classes nil)

(defthm keval-alls-subset-2
  (implies (and (var-set a)
		(var-set b)
		(subsetp-equal a b)
		(not (free-vars (alls a f))))
	   (equal (xeval (alls a f) (domain i) i)
		  (keval b f (domain i) (idx (car a) b) (domain i) i)))
  :hints (("goal"
	   :do-not-induct t
	   :hands-off (keval xeval)
	   :use ((:instance keval-alls-subset-cons (dom (domain i)))
		 (:instance keval-alls-subset-atom)))
	  )
  :rule-classes nil)

;;---- The main events

(defthm xeval-alls-subset
  (implies (and (var-set a)
		(var-set b)
		(subsetp-equal a b)
		(not (free-vars (alls a f))))
	   (equal (xeval (alls a f) (domain i) i)
		  (xeval (alls b f) (domain i) i)))
  :hints (("goal"
	   :do-not-induct t
	   :use ((:instance keval-alls-subset-2)))
	  )
  :rule-classes nil)

(defthm feval-alls-subset
  (implies (and (var-set a)
		(var-set b)
		(subsetp-equal a b)
		(not (free-vars (alls a f))))
	   (equal (feval (alls a f) i)
		  (feval (alls b f) i)))
  :hints (("Goal" :use ((:instance xeval-feval (f (alls a f)))
			(:instance xeval-feval (f (alls b f)))
			xeval-alls-subset)))
  :rule-classes nil)

