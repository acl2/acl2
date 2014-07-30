(in-package "ACL2")

;; The main lemma of this book is that
;;      (universal-closure (list 'and a b))
;; is equivalent to
;;      (list 'and (universal-closure a) (universal-closure b))
;;
;; Also, we define a function that separately closes the
;; parts of a conjunction.

(include-book "stage")

(local (include-book "close"))

;;----------------------------

(local (defthm alls-vars-and-1
  (implies (and (wfand h)
                (var-set vars))
	   (equal (xeval (alls vars h) dom i)
		  (and (xeval (alls vars (a1 h)) dom i)
		       (xeval (alls vars (a2 h)) dom i))))
  :hints (("Goal"
           :induct (var-induct vars h dom i))
	  ("Subgoal *1/3"
           :expand ((alls vars h))))
  :rule-classes nil))

(local (defthm alls-vars-and-2
  (implies (var-set vars)
	   (equal (xeval (alls vars (list 'and f g)) dom i)
		  (and (xeval (alls vars f) dom i)
		       (xeval (alls vars g) dom i))))
  :hints (("Goal"
           :do-not-induct t
	   :use ((:instance alls-vars-and-1 (h (list 'and f g))))))))

(defthm uc-conj
  (equal (xeval (universal-closure (list 'and f g)) (domain i) i)
	 (and (xeval (universal-closure f) (domain i) i)
	      (xeval (universal-closure g) (domain i) i)))
  :hints (("Goal"
	   :do-not-induct t
           :use ((:instance xeval-alls-subset
                            (f f)
                            (a (free-vars f))
                            (b (union-equal (free-vars f) (free-vars g))))
		 (:instance xeval-alls-subset
                            (f g)
                            (a (free-vars g))
                            (b (union-equal (free-vars f) (free-vars g))))
		 (:instance xeval-alls-subset
                            (f (list 'and f g))
                            (a (union-equal (free-vars f) (free-vars g)))
                            (b (union-equal (free-vars f) (free-vars g))))
		 ))
	  ))

;;----------------------------------------------------------------------

(defthm uc-conj-left
  (implies (xeval (universal-closure (list 'and f g)) (domain i) i)
	   (xeval (universal-closure f) (domain i) i))
  :rule-classes nil)

(defthm uc-conj-right
  (implies (xeval (universal-closure (list 'and f g)) (domain i) i)
	   (xeval (universal-closure g) (domain i) i))
  :rule-classes nil)

;;----------------------------------------------------------------------
;; Here is a version of universal closure that separately closes
;; the parts of a conjunction.

(defun univ-closure-conj (f)
  (declare (xargs :guard (wff f)))
  (if (wfand f)
      (list 'and
	    (univ-closure-conj (a1 f))
	    (univ-closure-conj (a2 f)))
    (universal-closure f)))

(defthm univ-clossure-conj-ok-x
  (equal (xeval (univ-closure-conj f) (domain i) i)
	 (xeval (universal-closure f) (domain i) i))
  :hints (("Goal"
	   :induct (univ-closure-conj f))
	  ("Subgoal *1/1"
	   :use ((:instance uc-conj (f (a1 f)) (g (a2 f)))))))

(defthm univ-closure-conj-ok
  (equal (feval (univ-closure-conj f) i)
	 (feval (universal-closure f) i))
  :hints (("Goal"
         :in-theory (enable xeval-feval))))

(defthm univ-closure-conj-closed
  (not (free-vars (univ-closure-conj f)))
  :hints (("Subgoal *1/2"
           :in-theory (disable free-vars))))


