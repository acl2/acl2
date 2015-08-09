(in-package "ACL2")

(include-book "lemma-4")

(defun-sk ste-thm (ckt a c)
  (forall r (implies (and (r-p r)
			  (t-p r ckt)
			  (r-nmp r (l-depth a) (l-maxn a))

			  (equal (l-depth a) (l-depth c))
			  (equal (l-maxn a) (l-maxn c))

			  (equal (len ckt) (l-maxn a))

			  (l-eval a r)
			  )
		     (l-eval c r))))

(defthm ste-thm-backward
  (implies (and (l-p a)
		(l-p c)
		(c-p ckt)

		(r-lte (l-defseq  c (l-depth c) (l-maxn c))
		       (l-deftraj a ckt))
		)
	   (ste-thm ckt a c))
  :hints (("Goal'"
	   :use ((:instance lemma-2-pre
			    (l c)
			    (r (STE-THM-WITNESS CKT A C))
			    (n (L-DEPTH A))
			    (m (L-MAXN A))
			    )
		 (:instance r-lte-transitive
			    (a (L-DEFSEQ C (L-DEPTH A) (L-MAXN A)))
			    (b (R-DEFTRAJ (L-DEFSEQ A (L-DEPTH A) (L-MAXN A))
                                CKT (S-MAKE (L-MAXN A) 'X)))
			    (c (STE-THM-WITNESS CKT A C))
			    )) ) ) )


(defthm r-nmp-l-defseq
  (IMPLIES (AND (L-P A)
		;(C-P CKT)
		)
	   (R-NMP (L-DEFSEQ A (l-depth a) (l-maxn a))
		  (l-depth a)
		  (l-maxn a)))
  )

(defthm r-nmp-l-defseq-nils
  (implies (and (l-p a)
		(equal (l-maxn a) 0)
		)
	   (R-NMP (L-DEFSEQ A (L-DEPTH A) 0)
                          (L-DEPTH A)
                          0))
  :hints (("Goal"
	   :use ((:instance  r-nmp-l-defseq))))
  )

(defthm r-nmp-r-deftraj
 (IMPLIES (AND (L-P A)
	       (C-P CKT)
	       (equal (len ckt) m)

	       (r-p r)
	       (r-nmp r n m)
	       (positivep n)
	       (naturalp m)
	       (s-p s)
	       (equal (len s) m)
	       )
	  (R-NMP (R-DEFTRAJ r CKT s)
		 n
		 m) ) )


(defthm r-nmp-r-deftraj-nils
  (implies (and
	    (l-p a)
	    (equal (l-maxn a) 0)
					;(equal ckt nil)
	    ;(equal s nil)
	    ;(equal m 0)
	    )
	   (R-NMP (R-DEFTRAJ (L-DEFSEQ A (L-DEPTH A) 0)
                                     NIL NIL)
                          (L-DEPTH A)
                          0))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (disable r-nmp-r-deftraj)
	   :use ((:instance r-nmp-r-deftraj
			    (a a)
			    (ckt nil)
			    (m 0)
			    (r (L-DEFSEQ A (L-DEPTH A) 0))
			    (n (l-depth a))
			    (s nil)
			    ))))
  )


(defthm r-nmp-r-deftraj-ldefseq
  (implies (and
	    (l-p a)
	    (c-p ckt)
	    (equal (len ckt) (l-maxn a))
	    )
	   (R-NMP (R-DEFTRAJ (L-DEFSEQ A (L-DEPTH A) (L-MAXN A))
                                         CKT (S-MAKE (L-MAXN A) 'X))
                              (L-DEPTH A)
                              (L-MAXN A))
	   )
  :hints (("Goal"
	   :use ((:instance r-nmp-r-deftraj
			    (r (L-DEFSEQ A (L-DEPTH A) (L-MAXN A)))
			    (n (L-DEPTH A))
			    (m (L-MAXN A))
			    (ckt ckt)
			    (s (S-MAKE (L-MAXN A) 'X))
			    ))
	   ))
  )







(defthm ste-thm-forward
  (implies (and (l-p a)
		(l-p c)
		(c-p ckt)

		(equal (l-depth a) (l-depth c))
		(equal (l-maxn a) (l-maxn c))

		(equal (len ckt) (l-maxn a))

		(ste-thm ckt a c)
		)
	   (r-lte (l-defseq  c (l-depth c) (l-maxn c))
		  (l-deftraj a ckt)))
  :hints (("Goal"
	   :do-not '(generalize fertilize)
	   :in-theory (disable ste-thm lemma-2-pre
			       lemma-4-1
			       lemma-4-2
			       lemma-4-3 lemma-4-3-backward lemma-4-3-forward
			       l-evalp-when-n-l-depth-and-l-maxn)
	   :use (
		 (:instance ste-thm-necc
			    (r (R-DEFTRAJ (L-DEFSEQ A (L-DEPTH A) (L-MAXN A))
					  CKT (S-MAKE (L-MAXN A) 'X))))
		 (:instance lemma-4-1
			    (l a)
			    (c ckt))
		 (:instance lemma-4-2
			    (l a)
			    (c ckt))
		 )
	   )
	  ("Subgoal 5"
	   :use ((:instance l-evalp-when-n-l-depth-and-l-maxn
			    (l c)
			    )
		 (:instance lemma-2-pre
			    (l c)
			    (n (l-depth a))
			    (m 0)
			    (r (R-DEFTRAJ (L-DEFSEQ A (L-DEPTH A) 0)
                                 NIL NIL)))))
	  ("Subgoal 2"
	   :use (
		 (:instance l-evalp-when-n-l-depth-and-l-maxn
			    (l c)
			    )
		 (:instance lemma-2-pre
			    (l c)
			    (r (R-DEFTRAJ (L-DEFSEQ A (L-DEPTH A) (L-MAXN A))
					  CKT (S-MAKE (L-MAXN A) 'X)))
			    (n (L-DEPTH a))
			    (m (L-MAXN a))
			    )
		 )
	   )
	  )
  :otf-flg t
  )


(defthm fundamental-theorem-of-ste-pre
  (implies (and (l-p a)
		(l-p c)
		(c-p ckt)

		(equal (l-depth a) (l-depth c))
		(equal (l-maxn a) (l-maxn c))

		(equal (len ckt) (l-maxn a))
		)
	   (iff (ste-thm ckt a c)
		(r-lte (l-defseq  c (l-depth c) (l-maxn c))
		       (l-deftraj a ckt))))
  :hints (("Goal"
	   :use ((:instance ste-thm-forward)
		 (:instance ste-thm-backward))))
  )

(defun ste-wf-maxn (ckt thms)
  (if (consp thms)
      (cons `(equal (l-maxn ,(first (first thms))) (len ,ckt))
	    (cons `(equal (l-maxn ,(second (first thms))) (len ,ckt))
		  (ste-wf-maxn ckt (cdr thms))))
    nil))

(defun ste-wf-depth (deep thms)
  (if (consp thms)
      (cons `(l-p ,(first (first thms)))
	    (cons `(l-p ,(second (first thms)))
		  (cons `(equal (l-depth ,(first (first thms)))
				(l-depth ,deep))
			(cons `(equal (l-depth ,(second (first thms)))
				      (l-depth ,deep))
			      (ste-wf-depth deep (cdr thms))))))
    nil))

(defmacro ste-wf (ckt &rest thms)
  `(and
    (c-p ,ckt)
    ,@(ste-wf-maxn ckt thms)
    ,@(ste-wf-depth (first (first thms)) thms)
    )
  )

(defthm fundamental-theorem-of-ste
  (implies (and (l-p a)
		(l-p c)
		(c-p ckt)

		(ste-wf ckt (a c))

		;(equal (l-depth a) (l-depth c))
		;(equal (l-maxn a) (l-maxn c))

		;(equal (len ckt) (l-maxn a))
		)
	   (iff (ste-thm ckt a c)
		(r-lte (defseq  c)
		       (deftraj a ckt))))

  :hints (("Goal"
	   :use ((:instance fundamental-theorem-of-ste-pre )
		 )))
  )