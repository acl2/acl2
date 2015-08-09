(in-package "ACL2")

(defthm equal-cons-cases
  (equal (equal (cons a b) c)
	 (and (consp c)
	      (equal a (car c))
	      (equal b (cdr c)))))

(defun lastatom (x)
  (if (consp x) (lastatom (cdr x))
    x))

(defthm lastatom-update-nth-<
  (implies
   (< (nfix a) (len x))
   (equal (lastatom (update-nth a v x))
	  (lastatom x))))

(defthm lastatom-update-nth->
  (implies
   (not (< (nfix a) (len x)))
   (equal (lastatom (update-nth a v x))
	  nil)))

(defthm lastatom-update-nth
  (equal (lastatom (update-nth a v x))
	 (if (< (nfix a) (len x))
	     (lastatom x)
	   nil)))

(defun nfix-equiv (a b)
  (equal (nfix a)
	 (nfix b)))

(defthmd equal-nfix-rewrite
  (iff (equal (nfix a) b)
       (and (natp b)
	    (nfix-equiv a b))))

(theory-invariant
 (incompatible
  (:definition nfix-equiv)
  (:rewrite equal-nfix-rewrite)
  ))

(defequiv nfix-equiv)

(defcong nfix-equiv equal (nth a x) 1
  :hints (("goal" :in-theory (enable nth))))

(defcong nfix-equiv equal (update-nth a v x) 1
  :hints (("goal" :in-theory (enable update-nth))))

(defun nmx-induction (n m x)
  (if (zp n) x
    (if (zp m) n
      (nmx-induction (1- n) (1- m) (cdr x)))))

(defthm update-nth-of-update-nth
  (implies
   (nfix-equiv a b)
   (equal (update-nth a v (update-nth b w x))
	  (update-nth a v x)))
  :hints (("Goal" :induct (nmx-induction a b x)
	   :in-theory (enable update-nth))))

(defthm update-nth-over-update-nth
  (implies
   (not (nfix-equiv a b))
   (equal (update-nth a v (update-nth b w x))
	  (update-nth b w (update-nth a v x))))
  :hints (("Goal" :induct (nmx-induction a b x)
	   :in-theory (enable update-nth))))

(defthm nfix-equiv-nfix
  (nfix-equiv (nfix x) x))

(defund clr-nth (a x)
  (update-nth a nil x))

(defthm lastatom-clr-nth
  (equal (lastatom (clr-nth a x))
	 (if (< (nfix a) (len x))
	     (lastatom x)
	   nil))
  :hints (("Goal" :in-theory (enable clr-nth))))

(defthm len-clr-nth
  (equal (len (clr-nth a x))
	 (max (1+ (nfix a)) (len x)))
  :hints (("Goal" :in-theory (enable clr-nth))))

(defcong nfix-equiv equal (clr-nth a x) 1
  :hints (("goal" :in-theory (enable clr-nth))))

(defthm clr-nth-defn
  (equal (clr-nth n x)
	 (if (zp n) (cons nil (cdr x))
	   (cons (car x)
		 (clr-nth (1- n) (cdr x)))))
  :hints (("Goal" :in-theory (enable clr-nth update-nth)))
  :rule-classes (:definition))

(defthm open-clr-nth
  (and
   (implies
    (not (zp n))
    (equal (clr-nth n x)
	   (cons (car x)
		 (clr-nth (1- n) (cdr x)))))
   (implies
    (zp n)
    (equal (clr-nth n x)
	   (cons nil (cdr x))))))

(defthm open-update-nth
  (and
   (implies
    (not (zp n))
    (equal (update-nth n v x)
	   (cons (car x)
		 (update-nth (1- n) v (cdr x)))))
   (implies
    (zp n)
    (equal (update-nth n v x)
	   (cons v (cdr x))))))

(defthm clr-nth-update-nth
  (equal (clr-nth a (update-nth b v x))
	 (if (nfix-equiv a b) (clr-nth a x)
	   (update-nth b v (clr-nth a x))))
  :hints (("Goal" :in-theory (enable clr-nth))))

(defthm clr-nth-of-clr-nth
  (equal (clr-nth a (clr-nth a x))
	 (clr-nth a x))
  :hints (("goal" :in-theory (enable clr-nth))))

(defthm clr-nth-over-clr-nth
  (equal (clr-nth a (clr-nth b x))
	 (clr-nth b (clr-nth a x)))
  :hints (("goal" :in-theory (enable clr-nth))))

(defthm nth-clr-nth
  (equal (nth a (clr-nth b x))
	 (if (nfix-equiv a b) nil
	   (nth a x)))
  :hints (("Goal" :in-theory (enable clr-nth))))

(defun equal-nth-conclusion (a x y)
  (and (equal (lastatom x) (lastatom y))
       (equal (len x) (len y))
       (equal (nth a x) (nth a y))
       (equal (clr-nth a x)
	      (clr-nth a y))))

(defthm open-equal-nth-conclusion
  (equal (equal-nth-conclusion n x y)
	 (if (zp n) (if (and (consp x) (consp y))
			(and (equal (car x) (car y))
			     (equal (cdr x) (cdr y)))
		      (equal x y))
	   (if (and (consp x)
		    (consp y))
	       (and (equal (car x) (car y))
		    (equal-nth-conclusion (1- n) (cdr x) (cdr y)))
	     (equal x y))))
  :rule-classes (:definition))

(defun equal-nth-conclusion-fn (n x y)
  (if (zp n) (if (and (consp x) (consp y))
		 (and (equal (car x) (car y))
		      (equal (cdr x) (cdr y)))
	       (equal x y))
    (if (and (consp x)
	     (consp y))
	(and (equal (car x) (car y))
	     (equal-nth-conclusion-fn (1- n) (cdr x) (cdr y)))
      (equal x y))))

(defthmd equal-nth-conclusion-fn-to-equal-nth-conclusion
  (equal (equal-nth-conclusion n x y)
	 (equal-nth-conclusion-fn n x y)))

(defthm equal-nth-conclusion-fn-to-equal
  (equal (equal-nth-conclusion-fn n x y)
	 (equal x y)))

(defthmd equal-to-nth-reduction
  (equal (equal x y)
	 (equal-nth-conclusion n x y))
  :hints (("Goal" :in-theory '(equal-nth-conclusion-fn-to-equal-nth-conclusion
			       equal-nth-conclusion-fn-to-equal))))

(defthm equal-update-nth-reduction
  (equal (equal (update-nth n v x) y)
	 (and (< (nfix n) (len y))
	      (equal v (nth n y))
	      (equal (clr-nth n x)
		     (clr-nth n y))))
  :hints (("Goal" :use (:instance equal-to-nth-reduction
				  (x (update-nth n v x))))))

(defthm update-nth-nth
  (implies
   (< (nfix n) (len x))
   (equal (update-nth n (nth n x) x) x)))

#| nil-list

(defun nil-list (n v)
  (if (zp n) (list v)
    (cons nil (nil-list (1- n) v))))

(defthm update-nth-to-append
  (implies
   (<= (len x) (nfix n))
   (equal (update-nth n v x)
	  (append x (nil-list (- (nfix n) (len x)) v))))
  :hints (("Goal" :in-theory (enable append update-nth))))

(defthm nth-nil-list-nfix-equiv
  (implies
   (nfix-equiv a m)
   (equal (nth a (nil-list m v)) v))
  :hints (("Goal" :in-theory (enable nth))))

(defthm nth-nil-list-not-nfix-equiv
  (implies
   (not (nfix-equiv a m))
   (equal (nth a (nil-list m v)) nil))
  :hints (("Goal" :induct (nm-induction a m)
	   :in-theory (enable nth))))

(defthm nth-nil-list
  (equal (nth a (nil-list m v))
	 (if (nfix-equiv a m) v
	   nil))
  :hints (("Goal" :in-theory
	   '(nth-nil-list-not-nfix-equiv
	     nth-nil-list-nfix-equiv))))

(defthm nthcdr-nil-list
  (equal (nthcdr n (nil-list m v))
	 (if (<= (nfix n) (nfix m))
	     (nil-list (- (nfix m) (nfix n)) v)
	   nil))
  :hints (("Goal" :induct (nm-induction n m)
	   :in-theory (enable nthcdr))))

(xxinclude-book "basic" :dir :lists)

(defthm firstn-nil-list
  (implies
   (not (zp n))
   (equal (firstn n (nil-list m v))
	  (if (<= (nfix n) (nfix m))
	      (nil-list (1- (nfix n)) nil)
	    (nil-list m v))))
  :hints (("Goal" :induct (nm-induction n m)
	   :in-theory (enable firstn))))

(defthm car-nil-list-nil
  (equal (car (nil-list n nil))
	 nil))

|#

#| equal append rules ..

(defthm equal-append-append-tail-equal
  (equal (equal (append x y) (append z y))
	 (list::equiv x z))
  :hints (("goal" :induct (list::len-len-induction x z)
	   :in-theory (enable append))))

(defthmd equal-to-equiv
  (equal (equal x y)
	 (and
	  (list::equiv x y)
	  (equal (lastatom x) (lastatom y))))
  :hints (("goal" :induct (list::len-len-induction x y))))

(defun equal-append-append-case (x a y b)
  (and (list::equiv x (firstn (len x) a))
       (list::equiv (firstn (- (len a) (len x)) y)
		    (nthcdr (len x) a))
       (equal (nthcdr (- (len a) (len x)) y)
	      b)))

(defthm equiv-append-reduction-1
  (equal (list::equiv (append x y) z)
	 (and (list::equiv x (firstn (len x) z))
	      (list::equiv y (nthcdr (len x) z))))
  :hints (("Goal" :in-theory (e/d (LIST::EQUAL-APPEND-REDUCTION! list::equiv)
				  (LIST::LIST-EQUIV-HACK LIST::EQUAL-OF-FIXES)))))

(defthm equiv-append-reduction-2
  (equal (list::equiv z (append x y))
	 (and (list::equiv x (firstn (len x) z))
	      (list::equiv y (nthcdr (len x) z))))
  :hints (("Goal" :in-theory (e/d (LIST::EQUAL-APPEND-REDUCTION! list::equiv)
				  (LIST::LIST-EQUIV-HACK LIST::EQUAL-OF-FIXES)))))

(defthmd equal-append-append-reduction2!
  (equal (equal (append x y) (append a b))
	 (if (< (len x) (len a))
	     (equal-append-append-case x a y b)
	   (equal-append-append-case a x b y)))
  :hints (("goal" :in-theory '(LIST::EQUAL-APPEND-REDUCTION!))
	  (and stable-under-simplificationp
	       '(:in-theory (current-theory :here)))
	  (and stable-under-simplificationp
	       '(:in-theory '(LIST::EQUAL-APPEND-REDUCTION!)))
	  (and stable-under-simplificationp
	       '(:in-theory (current-theory :here)))))

|#

(in-theory (disable nfix nfix-equiv))
(in-theory (enable equal-nfix-rewrite))
(in-theory (disable nth update-nth))

(defun nfix-list (list)
  (if (consp list)
      (cons (nfix (car list))
	    (nfix-list (cdr list)))
    nil))

(defun nfix-list-equiv (x y)
  (equal (nfix-list x)
	 (nfix-list y)))

(defequiv nfix-list-equiv)

(defthm open-nfix-list-equiv
  (and
   (implies
    (consp x)
    (equal (nfix-list-equiv x y)
	   (and (consp y)
		(equal (nfix (car x))
		       (nfix (car y)))
		(nfix-list-equiv (cdr x) (cdr y)))))
   (implies
    (not (consp x))
    (equal (nfix-list-equiv x y)
	   (not (consp y))))))

(in-theory (disable nfix-list-equiv))


(defun nth* (list st)
  (if (consp list)
      (cons (nth (car list) st)
	    (nth* (cdr list) st))
    nil))

(defund nth*-equiv (list st1 st2)
  (equal (nth* list st1)
	 (nth* list st2)))

(defthm nth*-equiv-def
  (equal (nth*-equiv list st1 st2)
	 (if (consp list)
	     (and (equal (nth (car list) st1)
			 (nth (car list) st2))
		  (nth*-equiv (cdr list) st1 st2))
	   t))
  :hints (("Goal" :in-theory (enable nth*-equiv)))
  :rule-classes (:definition))

(defun clr-nth* (list st)
  (if (consp list)
      (clr-nth (car list)
	       (clr-nth* (cdr list) st))
    st))

(defthm open-clr-nth*
  (implies
   (consp list)
   (equal (clr-nth* list st)
	  (clr-nth (car list)
		   (clr-nth* (cdr list) st)))))

(defthm clr-nth-clr-nth*
  (equal (clr-nth* list (clr-nth a st))
	 (clr-nth a (clr-nth* list st)))
  :hints (("Subgoal *1/1" :cases ((nfix-equiv a (car list))))))

(defun equal-nth*-conclusion (list x y)
  (and (equal (lastatom x) (lastatom y))
       (equal (len x) (len y))
       (nth*-equiv list x y)
       (equal (clr-nth* list x)
	      (clr-nth* list y))))

(defthm nth*-equiv-over-clr-nth-backchaining
  (implies
   (nth*-equiv list x y)
   (nth*-equiv list (clr-nth a x) (clr-nth a y)))
  :hints (("Goal" :in-theory (enable nth*-equiv))))

(defthm nth*-equiv-identity
  (nth*-equiv list x x)
  :hints (("Goal" :in-theory (enable nth*-equiv))))

(defun equal-nth*-induction (list x y)
  (if (consp list)
      (equal-nth*-induction (cdr list)
			    (clr-nth (car list) x)
			    (clr-nth (car list) y))
    (list x y)))

(defthmd equal-nth*-reduction
  (equal (equal x y)
	 (equal-nth*-conclusion list x y))
  :hints (("Goal" :induct (equal-nth*-induction list x y)
	   :in-theory (disable equal-nth*-conclusion lastatom-clr-nth len-clr-nth))
	  ("Subgoal *1/2" :in-theory (enable equal-nth*-conclusion))
	  ("Subgoal *1/1" :in-theory (enable equal-nth*-conclusion)
	   :use ((:instance equal-to-nth-reduction
			    (n (car list)))))))


(defun copy-nth* (list st1 st2)
  (if (consp list)
      (update-nth (car list)
		  (nth (car list) st1)
		  (copy-nth* (cdr list) st1 st2))
    st2))

;;
;; Does the default ordering go the wrong way?
;;
(defthm clr-nth-thru-clr-nth*
  (equal (clr-nth ZZZZ (clr-nth* list (update-nth ZZZZ v x)))
	 (clr-nth ZZZZ (clr-nth* list x))))

(defthm nth*-clr-copy-nth*
  (equal (clr-nth* list (copy-nth* list st1 st2))
	 (clr-nth* list st2)))

(defund nth*-copy-equiv (list x y z)
  (equal (copy-nth* list x z)
	 (copy-nth* list y z)))


(encapsulate
    ()

  (defun maxval-p (a list)
    (if (consp list)
	(if (< (nfix a) (nfix (car list))) nil
	  (maxval-p a (cdr list)))
      t))

  (defun maxval (list)
    (if (consp list)
	(if (maxval-p (car list) (cdr list))
	    (nfix (car list))
	  (maxval (cdr list)))
      0))

  (defthm maxval-p-maxval-prop
    (IMPLIES (AND (NOT (MAXVAL-P A Z))
		  (MAXVAL-P X Z)
		  (< (NFIX X) (NFIX A)))
	     (< (NFIX X) (MAXVAL Z)))
    :rule-classes (:linear :rewrite))

  (defthm not-maxval-p-maxval-prop-2
    (implies
     (not (maxval-p x list))
     (< (nfix x) (maxval list)))
    :rule-classes (:rewrite :linear))

  (defthm maxval-p-maxval-prop-3
    (implies
     (maxval-p x list)
     (<= (maxval list) (nfix x)))
    :rule-classes (:rewrite :linear))

  (defund maxsize (list)
    (if (consp list)
	(1+ (maxval list))
      0))

  (local
   (defthm max-maxsize
     (equal (max (1+ (nfix x)) (maxsize list))
	    (if (maxval-p x list) (1+ (nfix x))
	      (maxsize list)))
     :hints (("Goal" :in-theory (enable maxsize)))))

  (local
   (defthm open-maxsize
     (implies
      (consp list)
      (equal (maxsize list)
	     (if (maxval-p (car list) (cdr list))
		 (1+ (nfix (car list)))
	       (maxsize (cdr list)))))
     :hints (("goal" :in-theory (enable maxsize)))))

  (local
   (defthm equal-max-reduction
     (implies (equal (max a b) d)
	      (iff (equal (max a (max b c))
			  (max d c)) t))))

  (defthm len-copy-nth*
    (equal (len (copy-nth* list x y))
	   (max (maxsize list) (len y)))
    :hints (("Goal" :induct (copy-nth* list x y)
	     :in-theory (disable max))
	    ("Subgoal *1/2" :in-theory (enable maxsize max))))

  )


(defthm nth*-copy-equiv-reduction
  (equal (nth*-copy-equiv list x y z)
	 (equal-nth*-conclusion list (copy-nth* list x z) (copy-nth* list y z)))
  :hints (("Goal" :in-theory (enable nth*-copy-equiv)
	   :use (:instance equal-nth*-reduction
			   (x (copy-nth* list x z))
			   (y (copy-nth* list y z))
			   (list list)))))

(defthm nth*-equiv-update-nth-chaining
  (implies
   (and
    (nth*-equiv list x y)
    (equal v (nth a y)))
   (nth*-equiv list (update-nth a v x) y))
  :hints (("goal" :induct (len list))))

(defthm nth*-equiv-copy-nth*
  (nth*-equiv list (copy-nth* list x y) x))

(defthm nth*-copy-nth*
  (equal (nth* list (copy-nth* list x y))
	 (nth* list x))
  :hints (("Goal" :in-theory `(nth*-equiv)
	   :use (:instance nth*-equiv-copy-nth*))))

(defthm nth*-equiv-copy-nth*-copy-nth*
  (equal (nth*-equiv list (copy-nth* list x a)
		     (copy-nth* list y b))
	 (nth*-equiv list x y))
  :hints (("Goal" :in-theory (enable nth*-equiv))))

(defthm lastatom-copy-nth*
  (equal (lastatom (copy-nth* list x y))
	 (if (or (not (consp list)) (< (maxval list) (len y)))
	     (lastatom y)
	   nil))
  :hints (("Goal" :in-theory (enable maxsize)))
  :otf-flg t)

(defthm nth*-equiv-reduction
  (equal (nth*-equiv list x y)
	 (nth*-copy-equiv list x y z)))

(defun use (list st)
  (copy-nth* list st nil))

(defthm nth-use
  (implies
   (member (nfix n) (nfix-list list))
   (equal (nth n (use list x))
	  (nth n x)))
  :hints (("Goal" :in-theory (enable use))))

(defthm nth*-get-copy-equivalence
  (equal (equal (nth* list x)
		(nth* list y))
	 (equal (use list x)
		(use list y)))
  :hints (("goal" :in-theory '(use
			       nth*-equiv
			       nth*-copy-equiv)
	   :use (:instance nth*-equiv-reduction
			   (z nil)))))

(defthm nth-copy-nth*
  (equal (nth a (copy-nth* list x y))
	 (if (member (nfix a) (nfix-list list)) (nth a x)
	   (nth a y))))

(defthm update-nth-nil-reduction
  (equal (update-nth a nil x)
	 (clr-nth a x))
  :hints (("Goal" :in-theory (enable clr-nth))))

(defthm clr-nth-copy-nth*-member
  (implies
   (member (nfix a) (nfix-list list))
   (equal (clr-nth a (copy-nth* list x y))
	  (copy-nth* list (clr-nth a x) y)))
  :hints (("Goal" :in-theory (disable EQUAL-UPDATE-NTH-REDUCTION))))

(defthm clr-nth-copy-nth*-non-member
  (implies
   (not (member (nfix a) (nfix-list list)))
   (equal (clr-nth a (copy-nth* list x y))
	  (copy-nth* list x (clr-nth a y))))
  :hints (("Goal" :in-theory (disable EQUAL-UPDATE-NTH-REDUCTION))))

(defthm clr-nth*-copy-nth*
  (equal (clr-nth a (copy-nth* list x y))
	 (if (member (nfix a) (nfix-list list)) (copy-nth* list (clr-nth a x) y)
	   (copy-nth* list x (clr-nth a y)))))

(defthm update-nth-thru-copy-nth*
  (equal (update-nth a v (copy-nth* list (update-nth a w x) y))
	 (update-nth a v (copy-nth* list x y))))

(defthm copy-nth*-update-nth-member
  (implies
   (member (nfix a) (nfix-list list))
   (equal (copy-nth* list (update-nth a v x) z)
	  (update-nth a v (copy-nth* list x z))))
  :hints (("Goal" :in-theory (disable EQUAL-UPDATE-NTH-REDUCTION))))

(defthm copy-nth*-update-nth-non-member
  (implies
   (not (member (nfix a) (nfix-list list)))
   (equal (copy-nth* list (update-nth a v x) z)
	  (copy-nth* list x z)))
  :hints (("Goal" :in-theory (disable EQUAL-UPDATE-NTH-REDUCTION))))

(defthm copy-nth*-update-nth
  (equal (copy-nth* list (update-nth a v x) z)
	 (if (member (nfix a) (nfix-list list))
	     (update-nth a v (copy-nth* list x z))
	   (copy-nth* list x z)))
  :hints (("Goal" :in-theory '(copy-nth*-update-nth-member
			       copy-nth*-update-nth-non-member
			       ))))

(defthm use-update-nth-non-member
  (implies
   (not (member (nfix a) (nfix-list list)))
   (equal (use list (update-nth a v x))
	  (use list x))))

(defthmd use-update-nth-member
  (implies
   (member (nfix a) (nfix-list list))
   (equal (use list (update-nth a v x))
	  (update-nth a v (use list x)))))

(defthmd use-update-nth
  (equal (use list (update-nth a v x))
	 (if (member (nfix a) (nfix-list list))
	     (update-nth a v (use list x))
	   (use list x)))
  :hints (("Goal" :in-theory '(use-update-nth-non-member
			       use-update-nth-member
			       ))))

(defthm use-use
  (equal (use list (use list x))
	 (use list x)))

(defthm member-append
  (iff (member x (append y z))
       (or (member x y)
	   (member x z))))

(defthm nfix-list-append
  (equal (nfix-list (append x y))
	 (append (nfix-list x) (nfix-list y))))

(defthmd open-use
  (and
   (implies
    (consp list)
    (equal (use list x)
	   (update-nth (car list) (nth (car list) x)
		       (use (cdr list) x))))
   (implies
    (not (consp list))
    (equal (use list x) nil)))
  :hints (("Goal" :in-theory (e/d (use) (EQUAL-UPDATE-NTH-REDUCTION)))))


(defun subset (x y)
  (if (consp x)
      (and (member (car x) y)
	   (subset (cdr x) y))
    t))

(defthm nth*-use
  (implies
   (subset list listx)
   (equal (nth* list (use listx st))
	  (nth* list st)))
  :hints (("Goal" :in-theory (e/d (use)
				  (NTH*-GET-COPY-EQUIVALENCE)))))

(defthm subset-append
  (subset list (append list y)))

(defthm equal-nth*-append-reduction
  (equal (equal (nth* (append x y) a)
		(nth* (append x y) b))
	 (and (equal (nth* x a)
		     (nth* x b))
	      (equal (nth* y a)
		     (nth* y b))))
  :hints (("Goal" :in-theory (disable
			      NTH*-GET-COPY-EQUIVALENCE
			      ))))

(defthm clr-nth-use
  (implies
   (member (nfix a) (nfix-list list))
   (equal (clr-nth a (use list x))
	  (use list (clr-nth a x))))
  :hints (("Goal" :in-theory (enable use))))

(in-theory (disable OPEN-UPDATE-NTH))

