(in-package "ACL2")

;; This is a nasty (and slow) book.  Lemmas xeval-append-a and
;; xeval-append-b below are the what we need in book sk-step-sound.
;; The need for these arise because of the way build-sk uses the
;; domain to build a Skolem function.  In particular, the function
;; is built for the two "halfs" of the domain then appended.
;; When proving soundness of sk-step, this append shows itself in
;; an ugly way.

(include-book "sk-useless")
(include-book "sk-step")
(set-well-founded-relation e0-ord-<)

;;------------------------------------------------------
;; Miscellaneus lemmas placed here during a reorganization.

(defthm subst-term-list-append-commute
  (implies (and (variable-term y)
		(not (equal y x)))
	   (equal (subst-term-list (append vars (list y)) x e)
		  (append (subst-term-list vars x e) (list y)))))

(defthm subst-sk-commute-helper
 (implies (and (domain-term e)
	       (function-symbol fsym)
	       (true-listp args)
	       (not (equal x y))
	       (not (member-equal x (quantified-vars f))))
	  (equal (subst-free (subst-free f x e) y
			     (cons fsym (subst-term-list args x e)))
		 (subst-free (subst-free f y (cons fsym args)) x e)))
 :hints (("goal"
	  :use ((:instance subst-flip-fix (tm (cons fsym args))))
	  :do-not-induct t)))

(defthm subst-free-step-sk-commute
  (implies (and (domain-term e)
		(true-listp args)
		(function-symbol fsym)
		(not (member-equal x (quantified-vars f))))
	   (equal (subst-free (step-sk f args fsym) x e)
		  (step-sk (subst-free f x e)
			   (subst-term-list args x e) fsym)))
  :hints (("Goal"
	   :induct (step-sk f args fsym))))

;;------------------------------------------------------------
;; Here is a non-mutual version of build-sk/build-sk-d.  This
;; is analogous to the xeval version of feval/feval-d.

(defun xbuild (f vals dom i)
  (declare (xargs :measure (cons (wff-count f) (acl2-count dom))
		   :guard (and (wff f)
			       (nnfp f)
			       (domain-term-list vals)
			       (domain-term-list (fringe dom)))
		   :verify-guards nil
		   ))
   (cond ((or (wfand f) (wfor f))
	  (if (> (exists-count (a1 f)) 0)
	      (xbuild (a1 f) vals dom i)
	      (xbuild (a2 f) vals dom i)))
	 ((wfexists f) (list (cons vals (val-or-0 (a2 f)
						  (a1 f)
						  (domain i) i))))
	 ((wfall f)
	  (if (atom dom)
	      (xbuild (subst-free (a2 f) (a1 f) dom)
			(append vals (list dom)) (domain i) i)
	      (append (xbuild f vals (car dom) i)
		      (xbuild f vals (cdr dom) i))))
	 (t nil)))

(defthm true-listp-xbuild
  (true-listp (xbuild f vals dom i)))

(verify-guards xbuild)

(defthm xbuild-build-flg
  (if flg
      (equal (build-sk f vals i)
	     (xbuild f vals (domain i) i))
    (implies (wfall f)
	     (equal (build-sk-d f vals dom i)
		    (xbuild f vals dom i))))
  :hints (("Goal"
           :do-not generalize
           :induct (build-sk-i flg f vals dom i)))
  :rule-classes nil)

(defthm xbuild-build-sk
  (equal (build-sk f vals i)
	 (xbuild f vals (domain i) i))
  :hints (("Goal"
           :by (:instance xbuild-build-flg (flg t)))))

(defthm xbuild-build-sk-d
  (implies (wfall f)
	   (equal (build-sk-d f vals dom i)
		  (xbuild f vals dom i)))
  :hints (("Goal"
           :by (:instance xbuild-build-flg (flg nil)))))

(in-theory (disable xbuild-build-sk xbuild-build-sk-d))

;;------------------------------------
;; following 3 help sk-subst-commute lemma

(defthm true-listp-append-list
  (true-listp (append a (list x))))

(defthm subst-term-list-append-list
  (implies (variable-term x)
	   (equal (subst-term-list (append lst (list x)) x tm)
		  (append (subst-term-list lst x tm) (list tm)))))

(defthm subst-term-list-domain-term-list
  (implies (domain-term-list vals)
	   (equal (subst-term-list vals x tm)
		  vals)))

;;------------------------------------

(defun ith-member (lst n)
  (declare (xargs :guard (integerp n)))

  (cond ((atom lst) nil)
	((equal n 1) (car lst))
	(t (ith-member (cdr lst) (- n 1)))))

(defun func-pos-n (func n lst)
  (declare (xargs :guard (and (integerp n)
			      (> n 0)
			      (true-listp lst))))
  (if (atom func)
      t
      (and (if (atom (car func))
	       t
	       (member-equal (ith-member (caar func) n) lst))
	   (func-pos-n (cdr func) n lst))))

(defthm func-pos-n-append-append
  (implies (and (func-pos-n f1 n l1)
		(func-pos-n f2 n l2))
	   (func-pos-n (append f1 f2) n (append l1 l2))))

(defthm func-pos-n-append
  (implies (and (func-pos-n f1 n lst)
		(func-pos-n f2 n lst))
	   (func-pos-n (append f1 f2) n lst)))

(defthm ith-member-append-junk
  (implies (<= n (len lst))
	   (equal (ith-member (append lst junk) n)
		  (ith-member lst n))))

(defun tuple-pos-n (vals n e)
  (declare (xargs :guard (and (domain-term-list vals)
			      (natp n)
			      (domain-term e))))
  (equal (ith-member vals n) e))

(defthm fapply-append-1
  (implies (not (fassoc tuple func1))
	   (equal (fapply (append func1 func2) tuple)
		  (fapply func2 tuple)))
  :hints (("Goal"
           :in-theory (enable fapply))))

(defthm fapply-append-2
  (implies (not (fassoc tuple func2))
	   (equal (fapply (append func1 func2) tuple)
		  (fapply func1 tuple)))
  :hints (("Goal"
           :in-theory (enable fapply))))

;;------------------------------------

(defthm func-pos-n-not-fassoc
  (implies (and (func-pos-n func n lst)
		(not (member-equal (ith-member vals n) lst))
		(< 0 n)
		(<= n (len vals)))
	   (not (fassoc vals func)))
  :rule-classes :forward-chaining)

(defthm eval-term-list-append-a  ;; ok
  (implies
   (and (variable-term z)
	(domain-term-list vls)
	(subsetp-equal vls (fringe (domain i)))
	(function-symbol fsym)
	(not (member-equal fsym (funcs-in-term-list lst)))
	(integerp n)
	(< 0 n)
	(<= n (len vls))
	(domain-term (ith-member vls n))
	(not (member-equal (ith-member vls n) (fringe dm)))
	(func-pos-n func1 n (fringe dm))
	)
   (equal (eval-term-list (subst-term-list lst z (cons fsym vls))
			  (list* (domain i)
				 (relations i)
				 (cons (cons fsym (len vls))
				       (append func1 func2))
				 (functions i)))
	  (eval-term-list (subst-term-list lst z (cons fsym vls))
			  (list* (domain i)
				 (relations i)
				 (cons (cons fsym (len vls))
				       func2)
				 (functions i)))))
  :hints (("Goal"
	   :induct (subst-term-list lst z (cons fsym vls))
	   ))
  :rule-classes nil)

;; The preceding rule doesn't get applied because of the free
;; variables n and dm.  Here is a trick.  The function (arg-1-of-3 func n dm)
;; which just projects out the first argument, is used to plant the
;; free variables n and dm in the trigger term.  We make a new rule
;; which is similar to the preceding, but with (arg-1-of-3 func1 n dm)
;; instead of func1.  Then we disable arg-1-of-3, and the modified rule
;; gets used automatically as we wish.  (Later on, we get rid of the
;; arg-1-of-3 term.)

(defun arg-1-of-3 (func n dm)
  (declare (xargs :guard t)
	   (ignore n dm))
  func)

(defthm eval-term-list-append-ax
  (implies
   (and (variable-term z)
	(domain-term-list vls)
	(subsetp-equal vls (fringe (domain i)))
	(function-symbol fsym)
	(not (member-equal fsym (funcs-in-term-list lst)))
	(integerp n)
	(< 0 n)
	(<= n (len vls))
	(domain-term (ith-member vls n))
	(not (member-equal (ith-member vls n) (fringe dm)))
	(func-pos-n func1 n (fringe dm))
	)
   (equal (eval-term-list (subst-term-list lst z (cons fsym vls))
			  (list* (domain i)
				 (relations i)
				 (cons (cons fsym (len vls))
				       (append (arg-1-of-3 func1 n dm) func2))
				 (functions i)))
	  (eval-term-list (subst-term-list lst z (cons fsym vls))
			  (list* (domain i)
				 (relations i)
				 (cons (cons fsym (len vls))
				       func2)
				 (functions i)))))
  :hints (("Goal"
	   :use ((:instance eval-term-list-append-a)))))

(in-theory (disable arg-1-of-3))

(local (include-book "arithmetic"))

(defthm list-car-subst-term-list-car
  (implies (> (len a) 0)
	   (equal (list (car (subst-term-list a x tm)))
		  (subst-term-list (list (car a)) x tm))))

(defthm list-car-subst-term-list-cadr
  (implies (> (len a) 1)
	   (equal (list (cadr (subst-term-list a x tm)))
		  (subst-term-list (list (cadr a)) x tm))))

(defthm not-member-fsym-list-cadr
  (implies (not (member-equal fsym (funcs-in-term-list (cdr f))))
	   (not (member-equal fsym (funcs-in-term-list (list (cadr f)))))))

(defthm not-member-fsym-list-caddr
  (implies (not (member-equal fsym (funcs-in-term-list (cdr f))))
	   (not (member-equal fsym (funcs-in-term-list (list (caddr f)))))))

(defthm variable-not-in-domain-term-list-a
  (implies (domain-term-list vals)
	   (not (var-occurrence-term-list x vals))))

(defthm variable-not-in-domain-term-list-b
  (implies (domain-term-list vals)
	   (not (var-occurrence-term-list x (list (cons fsym vals))))))

(defthm xeval-append-a-1  ;; ok, 251 seconds
  (implies (and (variable-term z)
		(domain-term-list vls)
		(subsetp-equal vls (fringe (domain i)))
		(function-symbol fsym)
		(not (member-equal fsym (funcs-in-formula f)))
		(not (member-equal z (quantified-vars f)))
		(setp (quantified-vars f))
		(integerp n)
		(< 0 n)
		(<= n (len vls))
		(domain-term (ith-member vls n))
		(not (member-equal (ith-member vls n) (fringe dm)))
		(func-pos-n func1 n (fringe dm))
		(domain-term-list (fringe dom)))
	   (equal (xeval (subst-free f z (cons fsym vls))
			 dom
			 (list* (domain i)
				(relations i)
				(cons (cons fsym (len vls))
				      (append (arg-1-of-3 func1 n dm) func2))
				(functions i)))
		  (xeval (subst-free f z (cons fsym vls))
			 dom
			 (list* (domain i)
				(relations i)
				(cons (cons fsym (len vls))
				      func2)
				(functions i)))))
  :hints (("Goal"
	   :induct (xeval-i f dom i)
	   :in-theory (enable eval-atomic)
	   )))

;;--------------------------------------------------

(defthm subst-free-preserves-step-sk-arity
  (equal (step-sk-arity (subst-free f x tm) n)
	 (step-sk-arity f n)))

(defthm xeval-append-a-2  ;; 121 sec
  (implies (and (function-symbol fsym)
		(domain-term-list vls)
		(subsetp-equal vls (fringe (domain i)))
		(not (member-equal fsym (funcs-in-formula f)))
		(setp (quantified-vars f))
		(integerp n) (> n 0) (<= n (len vls))
		(domain-term e)
		(not (member-equal e (fringe dm)))
		(func-pos-n func1 n (fringe dm))
		(tuple-pos-n vls n e)
		(domain-term-list (fringe dom))
		(subsetp-equal (fringe dom) (fringe (domain i)))
		)
	   (equal (xeval (step-sk f vls fsym)
			 dom
			 (list* (domain i)
				(relations i)
				(cons (cons fsym (step-sk-arity f (len vls)))
				      (append (arg-1-of-3 func1 n dm) func2))
				(functions i)))
		  (xeval (step-sk f vls fsym)
			 dom
			 (list* (domain i)
				(relations i)
				(cons (cons fsym (step-sk-arity f (len vls)))
				      func2)
				(functions i)))))
  :hints (("Goal"
	   :do-not generalize
	   :induct (xbuild f vls dom i))))

(defthm xeval-append-a-3  ;; get rid of arg-1-of-3
  (implies (and (function-symbol fsym)
		(domain-term-list vls)
		(subsetp-equal vls (fringe (domain i)))
		(not (member-equal fsym (funcs-in-formula f)))
		(setp (quantified-vars f))
		(integerp n) (> n 0) (<= n (len vls))
		(domain-term e)
		(not (member-equal e (fringe dm)))
		(func-pos-n func1 n (fringe dm))
		(tuple-pos-n vls n e)
		(domain-term-list (fringe dom))
		(subsetp-equal (fringe dom) (fringe (domain i)))
		)
	   (equal (xeval (step-sk f vls fsym)
			 dom
			 (list* (domain i)
				(relations i)
				(cons (cons fsym (step-sk-arity f (len vls)))
				      (append func1 func2))
				(functions i)))
		  (xeval (step-sk f vls fsym)
			 dom
			 (list* (domain i)
				(relations i)
				(cons (cons fsym (step-sk-arity f (len vls)))
				      func2)
				(functions i)))))
  :hints (("Goal"
	   :use ((:instance xeval-append-a-2))
	   :in-theory (enable arg-1-of-3))))

(defthm ith-member-append-list
  (equal (ith-member (append lst (list e)) (+ 1 (len lst)))
	 e))

(defthm xeval-append-a-4
  (implies (and (not (consp dom))
		(function-symbol fsym)
		(domain-term-list vals)
		(subsetp-equal vals (fringe (domain i)))
		(not (member-equal fsym (funcs-in-formula f5)))
		(setp (quantified-vars f5))
		(not (member-equal dom (fringe dm)))
		(func-pos-n func1 (+ 1 (len vals))
			    (fringe dm))
		(domain-term dom)
		(member-equal dom (fringe (domain i))))
	   (equal (xeval (step-sk (subst-free f5 f3 dom)
				  (append vals (list dom))
				  fsym)
			 (domain i)
			 (list* (domain i)
				(relations i)
				(cons (cons fsym
					    (step-sk-arity f5 (+ 1
								 (len vals))))
				      (append func1 func2))
				(functions i)))
		  (xeval (step-sk (subst-free f5 f3 dom)
				  (append vals (list dom))
				  fsym)
			 (domain i)
			 (list* (domain i)
				(relations i)
				(cons (cons fsym
					    (step-sk-arity f5 (+ 1
								 (len vals))))
				      func2)
				(functions i)))))
  :hints (("Goal"
	   :use ((:instance xeval-append-a-3
			    (e dom)
			    (dom (domain i))
			    (f (subst-free f5 f3 dom))
			    (vls (append vals (list dom)))
			    (n (+ 1 (len vals)))))
           :do-not-induct t)))

(defthm xeval-append-a-5  ;; 141 sec
  (implies (and (function-symbol fsym)
		(< (len vals) (step-sk-arity f (len vals)))
		(domain-term-list vals)
		(subsetp-equal vals (fringe (domain i)))
		(not (member-equal fsym (funcs-in-formula f)))
		(setp (quantified-vars f))
		(disjoint (fringe dom) (fringe dm))
		(func-pos-n func1 (+ 1 (len vals)) (fringe dm))
		(domain-term-list (fringe dom))
		(subsetp-equal (fringe dom) (fringe (domain i)))
		)
	   (equal (xeval (step-sk f vals fsym)
			 dom
			 (list* (domain i)
				(relations i)
				(cons (cons fsym (step-sk-arity f (len vals)))
				      (append func1
					      func2))

				(functions i)))
		  (xeval (step-sk f vals fsym)
			 dom
			 (list* (domain i)
				(relations i)
				(cons (cons fsym (step-sk-arity f (len vals)))
				      func2)
				(functions i)))))
  :hints (("Goal"
	   :induct (xbuild f vals dom i))))

;;---------------------

(defthm xbuild-pos
  (implies (and (integerp n)
		(<= n (len vals)))
	   (func-pos-n (xbuild f vals dom i)
		       n
		       (list (ith-member vals n)))))

(defthm xbuild-pos-last
  (func-pos-n (xbuild f (append vals (list e)) dom i)
	      (+ 1 (len vals))
	      (list e))
  :hints (("Goal"
	   :in-theory (disable xbuild-pos)
	   :use ((:instance xbuild-pos
			    (vals (append vals (list e)))
			    (n (+ 1 (len vals))))))))

(defthm xbuild-pos-all
  (implies (and (wfall f))
	   (func-pos-n (xbuild f vals dom i)
		       (+ 1 (len vals))
		       (fringe dom)))
  :hints (("goal"
	   :expand ((xbuild (list 'all f3 f5) vals dom i))
	   :induct (dom-i dom))))

(defthm step-sk-sym-n-1
  (implies (step-sk-arity f n)
	   (<= n (step-sk-arity f n)))
  :rule-classes nil)

(defthm step-sk-sym-n-2
  (implies (step-sk-arity f (+ 1 n))
	   (< n (step-sk-arity f (+ 1 n))))
  :hints (("Goal"
	   :use ((:instance step-sk-sym-n-1 (n (+ 1 n)))))))

(defthm step-sk-sym-n-3
  (implies (and (wfall f)
		(step-sk-arity f n))
	   (< n (step-sk-arity f n))))

(defthm xeval-append-a-6
  (implies (and (wfall f)
		(function-symbol fsym)
		(step-sk-arity f (len vals))
		(domain-term-list vals)
		(subsetp-equal vals (fringe (domain i)))
		(not (member-equal fsym (funcs-in-formula f)))
		(setp (quantified-vars f))
		(disjoint (fringe dom) (fringe dm))
		(domain-term-list (fringe dom))
		(subsetp-equal (fringe dom) (fringe (domain i)))
		)
	   (equal (xeval (step-sk f vals fsym)
			 dom
			 (list* (domain i)
				(relations i)
				(cons (cons fsym (step-sk-arity f (len vals)))
				      (append (xbuild f vals dm i)
					      func2))
				(functions i)))
		  (xeval (step-sk f vals fsym)
			 dom
			 (list* (domain i)
				(relations i)
				(cons (cons fsym (step-sk-arity f (len vals)))
				      func2)
				(functions i))))))

(defthm xeval-append-a-7
  (implies
   (and (variable-term y)
	(function-symbol fsym)
	(step-sk-arity g (+ 1 (len vals)))
	(domain-term-list vals)
	(subsetp-equal vals (fringe (domain i)))
	(not (member-equal fsym (funcs-in-formula g)))
	(not (member-equal y (quantified-vars g)))
	(setp (quantified-vars g))
	(disjoint (fringe dom) (fringe dm))
	(domain-term-list (fringe dom))
	(subsetp-equal (fringe dom)
		       (fringe (domain i))))
   (equal (xeval (list 'all y (step-sk g (append vals (list y)) fsym))
		 dom
		 (list* (domain i)
			(relations i)
			(cons (cons fsym (step-sk-arity g (+ 1 (len vals))))
			      (append (xbuild (list 'all y g) vals dm i)
				      func2))
			(functions i)))
	  (xeval (list 'all y (step-sk g (append vals (list y)) fsym))
		 dom
		 (list* (domain i)
			(relations i)
			(cons (cons fsym (step-sk-arity g (+ 1 (len vals))))
			      func2)
			(functions i)))))
  :hints (("Goal"
           :use ((:instance xeval-append-a-6 (f (list 'all y g)))))))

(defthm xeval-append-a
  (implies
   (and (variable-term y)
	(function-symbol fsym)
	(step-sk-arity f (+ 1 (len vals)))
	(domain-term-list vals)
	(subsetp-equal vals (fringe (domain i)))
	(not (member-equal fsym (funcs-in-formula f)))
	(not (member-equal y (quantified-vars f)))
	(setp (quantified-vars f))
	(disjoint (fringe dom) (fringe dm))
	(domain-term-list (fringe dom))
	(subsetp-equal (fringe dom) (fringe (domain i))))
   (equal (feval-d (list 'all y (step-sk f (append vals (list y)) fsym))
		   dom
		   (list* (domain i)
			  (relations i)
			  (cons (cons fsym (step-sk-arity f (+ 1 (len vals))))
				(append (build-sk-d (list 'all y f) vals dm i)
					func2))
			  (functions i)))
	  (feval-d (list 'all y (step-sk f (append vals (list y)) fsym))
		   dom
		   (list* (domain i)
			  (relations i)
			  (cons (cons fsym (step-sk-arity f (+ 1 (len vals))))
				func2)
			  (functions i)))))
  :hints (("Goal"
	   :in-theory (enable xeval-feval-d xbuild-build-sk-d))))

;;------------------------------------
;; Next, prove the analogous theorem for the other side append.
;; All of these theorems are similar to preceding ones.
;;
;; It probably would be cleaner to prove something like the following,
;; then use the theorem for the first side.
;;
;; (implies
;;  (disjoint (fringe dom1) (fringe dom2))
;;  (equal (feval f (list* (domain i)
;;                          (relations i)
;;                          (cons sym-arity
;;                                (append
;;                                 (build-sk-d (list 'all y f) vals dom1 i)
;;                                 (build-sk-d (list 'all y f) vals dom2 i)
;;                                 ))
;;                          (functions i)))
;;          (feval f (list* (domain i)
;;                          (relations i)
;;                          (cons sym-arity
;;                                (append
;;                                 (build-sk-d (list 'all y f) vals dom2 i)
;;                                 (build-sk-d (list 'all y f) vals dom1 i)
;;                                 ))
;;                          (functions i)))))
;;
;; In fact, I started to prove this (see work-append-other), but it
;; wasn't easy, so I did it this way instead.

(defthm eval-term-list-append-b
  (implies
   (and (variable-term z)
	(domain-term-list vls)
	(subsetp-equal vls (fringe (domain i)))
	(function-symbol fsym)
	(not (member-equal fsym (funcs-in-term-list lst)))
	(integerp n)
	(< 0 n)
	(<= n (len vls))
	(domain-term (ith-member vls n))
	(not (member-equal (ith-member vls n) (fringe dm)))
	(func-pos-n func2 n (fringe dm))
	)
   (equal (eval-term-list (subst-term-list lst z (cons fsym vls))
			  (list* (domain i)
				 (relations i)
				 (cons (cons fsym (len vls))
				       (append func1 func2))
				 (functions i)))
	  (eval-term-list (subst-term-list lst z (cons fsym vls))
			  (list* (domain i)
				 (relations i)
				 (cons (cons fsym (len vls))
				       func1)
				 (functions i)))))
  :hints (("Goal"
	   :induct (subst-term-list lst z (cons fsym vls))
	   ))
  :rule-classes nil)

(in-theory (enable arg-1-of-3))

(defthm eval-term-list-append-bx
  (implies
   (and (variable-term z)
	(domain-term-list vls)
	(subsetp-equal vls (fringe (domain i)))
	(function-symbol fsym)
	(not (member-equal fsym (funcs-in-term-list lst)))
	(integerp n)
	(< 0 n)
	(<= n (len vls))
	(domain-term (ith-member vls n))
	(not (member-equal (ith-member vls n) (fringe dm)))
	(func-pos-n func2 n (fringe dm))
	)
   (equal (eval-term-list (subst-term-list lst z (cons fsym vls))
			  (list* (domain i)
				 (relations i)
				 (cons (cons fsym (len vls))
				       (append func1 (arg-1-of-3 func2 n dm)))
				 (functions i)))
	  (eval-term-list (subst-term-list lst z (cons fsym vls))
			  (list* (domain i)
				 (relations i)
				 (cons (cons fsym (len vls))
				       func1)
				 (functions i)))))
  :hints (("Goal"
	   :use ((:instance eval-term-list-append-b)))))

(in-theory (disable arg-1-of-3))

(defthm xeval-append-b-1  ;; ok, 251 seconds
  (implies (and (variable-term z)
		(domain-term-list vls)
		(subsetp-equal vls (fringe (domain i)))
		(function-symbol fsym)
		(not (member-equal fsym (funcs-in-formula f)))
		(not (member-equal z (quantified-vars f)))
		(setp (quantified-vars f))
		(integerp n)
		(< 0 n)
		(<= n (len vls))
		(domain-term (ith-member vls n))
		(not (member-equal (ith-member vls n) (fringe dm)))
		(func-pos-n func2 n (fringe dm))
		(domain-term-list (fringe dom)))
	   (equal (xeval (subst-free f z (cons fsym vls))
			 dom
			 (list* (domain i)
				(relations i)
				(cons (cons fsym (len vls))
				      (append func1 (arg-1-of-3 func2 n dm)))
				(functions i)))
		  (xeval (subst-free f z (cons fsym vls))
			 dom
			 (list* (domain i)
				(relations i)
				(cons (cons fsym (len vls))
				      func1)
				(functions i)))))
  :hints (("Goal"
	   :induct (xeval-i f dom i)
	   :in-theory (enable eval-atomic)
	   )))

;;--------------------------------------------------

(defthm xeval-append-b-2  ;; 121 sec
  (implies (and (function-symbol fsym)
		(domain-term-list vls)
		(subsetp-equal vls (fringe (domain i)))
		(not (member-equal fsym (funcs-in-formula f)))
		(setp (quantified-vars f))
		(integerp n) (> n 0) (<= n (len vls))
		(domain-term e)
		(not (member-equal e (fringe dm)))
		(func-pos-n func2 n (fringe dm))
		(tuple-pos-n vls n e)
		(domain-term-list (fringe dom))
		(subsetp-equal (fringe dom) (fringe (domain i)))
		)
	   (equal (xeval (step-sk f vls fsym)
			 dom
			 (list* (domain i)
				(relations i)
				(cons (cons fsym (step-sk-arity f (len vls)))
				      (append func1 (arg-1-of-3 func2 n dm)))
				(functions i)))
		  (xeval (step-sk f vls fsym)
			 dom
			 (list* (domain i)
				(relations i)
				(cons (cons fsym (step-sk-arity f (len vls)))
				      func1)
				(functions i)))))
  :hints (("Goal"
	   :do-not generalize
	   :induct (xbuild f vls dom i))))

(defthm xeval-append-b-3  ;; get rid of arg-1-of-3
  (implies (and (function-symbol fsym)
		(domain-term-list vls)
		(subsetp-equal vls (fringe (domain i)))
		(not (member-equal fsym (funcs-in-formula f)))
		(setp (quantified-vars f))
		(integerp n) (> n 0) (<= n (len vls))
		(domain-term e)
		(not (member-equal e (fringe dm)))
		(func-pos-n func2 n (fringe dm))
		(tuple-pos-n vls n e)
		(domain-term-list (fringe dom))
		(subsetp-equal (fringe dom) (fringe (domain i)))
		)
	   (equal (xeval (step-sk f vls fsym)
			 dom
			 (list* (domain i)
				(relations i)
				(cons (cons fsym (step-sk-arity f (len vls)))
				      (append func1 func2))
				(functions i)))
		  (xeval (step-sk f vls fsym)
			 dom
			 (list* (domain i)
				(relations i)
				(cons (cons fsym (step-sk-arity f (len vls)))
				      func1)
				(functions i)))))
  :hints (("Goal"
	   :use ((:instance xeval-append-b-2))
	   :in-theory (enable arg-1-of-3))))

(defthm xeval-append-b-4
  (implies (and (not (consp dom))
		(function-symbol fsym)
		(domain-term-list vals)
		(subsetp-equal vals (fringe (domain i)))
		(not (member-equal fsym (funcs-in-formula f5)))
		(setp (quantified-vars f5))
		(not (member-equal dom (fringe dm)))
		(func-pos-n func2 (+ 1 (len vals))
			    (fringe dm))
		(domain-term dom)
		(member-equal dom (fringe (domain i))))
	   (equal (xeval (step-sk (subst-free f5 f3 dom)
				  (append vals (list dom))
				  fsym)
			 (domain i)
			 (list* (domain i)
				(relations i)
				(cons (cons fsym
					    (step-sk-arity f5 (+ 1
								 (len vals))))
				      (append func1 func2))
				(functions i)))
		  (xeval (step-sk (subst-free f5 f3 dom)
				  (append vals (list dom))
				  fsym)
			 (domain i)
			 (list* (domain i)
				(relations i)
				(cons (cons fsym
					    (step-sk-arity f5 (+ 1
								 (len vals))))
				      func1)
				(functions i)))))
  :hints (("Goal"
	   :use ((:instance xeval-append-b-3
			    (e dom)
			    (dom (domain i))
			    (f (subst-free f5 f3 dom))
			    (vls (append vals (list dom)))
			    (n (+ 1 (len vals)))))
           :do-not-induct t)))

(defthm xeval-append-b-5  ;; 141 sec
  (implies (and (function-symbol fsym)
		(< (len vals) (step-sk-arity f (len vals)))
		(domain-term-list vals)
		(subsetp-equal vals (fringe (domain i)))
		(not (member-equal fsym (funcs-in-formula f)))
		(setp (quantified-vars f))
		(disjoint (fringe dom) (fringe dm))
		(func-pos-n func2 (+ 1 (len vals)) (fringe dm))
		(domain-term-list (fringe dom))
		(subsetp-equal (fringe dom) (fringe (domain i)))
		)
	   (equal (xeval (step-sk f vals fsym)
			 dom
			 (list* (domain i)
				(relations i)
				(cons (cons fsym (step-sk-arity f (len vals)))
				      (append func1 func2))
				(functions i)))
		  (xeval (step-sk f vals fsym)
			 dom
			 (list* (domain i)
				(relations i)
				(cons (cons fsym (step-sk-arity f (len vals)))
				      func1)
				(functions i)))))
  :hints (("Goal"
	   :induct (xbuild f vals dom i))))

;;---------------------

(defthm xeval-append-b-6
  (implies (and (wfall f)
		(function-symbol fsym)
		(step-sk-arity f (len vals))
		(domain-term-list vals)
		(subsetp-equal vals (fringe (domain i)))
		(not (member-equal fsym (funcs-in-formula f)))
		(setp (quantified-vars f))
		(disjoint (fringe dom) (fringe dm))
		(domain-term-list (fringe dom))
		(subsetp-equal (fringe dom) (fringe (domain i)))
		)
	   (equal (xeval (step-sk f vals fsym)
			 dom
			 (list* (domain i)
				(relations i)
				(cons (cons fsym (step-sk-arity f (len vals)))
				      (append func1 (xbuild f vals dm i)))

				(functions i)))
		  (xeval (step-sk f vals fsym)
			 dom
			 (list* (domain i)
				(relations i)
				(cons (cons fsym (step-sk-arity f (len vals)))
				      func1)
				(functions i))))))

(defthm xeval-append-b-7
  (implies
   (and (variable-term y)
	(function-symbol fsym)
	(step-sk-arity g (+ 1 (len vals)))
	(domain-term-list vals)
	(subsetp-equal vals (fringe (domain i)))
	(not (member-equal fsym (funcs-in-formula g)))
	(not (member-equal y (quantified-vars g)))
	(setp (quantified-vars g))
	(disjoint (fringe dom) (fringe dm))
	(domain-term-list (fringe dom))
	(subsetp-equal (fringe dom) (fringe (domain i))))
   (equal (xeval (list 'all y (step-sk g (append vals (list y)) fsym))
		 dom
		 (list* (domain i)
			(relations i)
			(cons (cons fsym (step-sk-arity g (+ 1 (len vals))))
			      (append func1
				      (xbuild (list 'all y g) vals dm i)))
			(functions i)))
	  (xeval (list 'all y (step-sk g (append vals (list y)) fsym))
		 dom
		 (list* (domain i)
			(relations i)
			(cons (cons fsym (step-sk-arity g (+ 1 (len vals))))
			      func1)
			(functions i)))))
  :hints (("Goal"
           :use ((:instance xeval-append-b-6 (f (list 'all y g)))))))

(defthm xeval-append-b
  (implies
   (and (variable-term y)
	(function-symbol fsym)
	(step-sk-arity f (+ 1 (len vals)))
	(domain-term-list vals)
	(subsetp-equal vals (fringe (domain i)))
	(not (member-equal fsym (funcs-in-formula f)))
	(not (member-equal y (quantified-vars f)))
	(setp (quantified-vars f))
	(disjoint (fringe dom) (fringe dm))
	(domain-term-list (fringe dom))
	(subsetp-equal (fringe dom) (fringe (domain i))))
   (equal (feval-d (list 'all y (step-sk f (append vals (list y)) fsym))
		   dom
		   (list* (domain i)
			  (relations i)
			  (cons (cons fsym (step-sk-arity f (+ 1 (len vals))))
				(append
				 func1
				 (build-sk-d (list 'all y f) vals dm i)))
			  (functions i)))
	  (feval-d (list 'all y (step-sk f (append vals (list y)) fsym))
		   dom
		   (list* (domain i)
			  (relations i)
			  (cons (cons fsym (step-sk-arity f (+ 1 (len vals))))
				func1)
			  (functions i)))))
  :hints (("Goal"
	   :in-theory (enable xeval-feval-d xbuild-build-sk-d))))

