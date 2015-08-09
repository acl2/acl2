(in-package "ACL2")

(include-book "fundamental")

; Added for ACL2 Version  2.7:
(set-match-free-default :once)
(add-match-free-override :once t)

(defthm r-lte-l-defseq-r-deftraj
  (implies (and ;(l-p l)
		(c-p ckt)
		(s-p s)
		(equal (len ckt) (len s))
		(r-nmp r (len r) (len s))
		;(s-lte s (car r))
		)
	   (r-lte r
		  (r-deftraj r ckt s))))



(defthm s-lte-s-lubs
 (implies (and (s-p s)
	       (s-p s1)
	       (s-p s2)
	       (s-lte s1 s2))
	  (s-lte (s-lub s s1)
		 (s-lub s s2))))

(defthm r-lte-r-deftraj
  (implies (and (r-p r1)
		(r-p r2)
		(r-lte r1 r2)
		(s-p s)
		(c-p ckt)
		(equal (len ckt) (len s))
		(r-nmp r1 (len r1) (len s))
		(r-nmp r2 (len r2) (len s)))
	   (r-lte (r-deftraj r1 ckt s)
		  (r-deftraj r2 ckt s)))
  :hints (("Goal"	       :do-not '(generalize fertilize)
           ;; modified for v2-9 by Matt K., enabling r-p-car in order to
           ;; compensate for earlier disabling of r-p-car in run.lisp, which
           ;; threw off this proof
           :in-theory (enable r-p-car))

;;; I guess some subgoals shifted around

; Version 2.3 hint
;	  ("Subgoal *1/9.8'5'" :expand ((R-DEFTRAJ (CONS R3 R4) CKT S))  )
; Not needed in Version 2.4

; Version 2.3 hint
;	  ("Subgoal *1/9.7'5'"
;	   :expand ((R-DEFTRAJ (CONS R3 R4) CKT S))
;	   :in-theory (disable r-lte-transitive lemma-3 s-lte-c-eval-is-s-lte)
;	   :use ((:instance r-lte-transitive
;			    (a (R-DEFTRAJ R4 CKT (C-EVAL CKT (S-LUB S R3))))
;			    (b (R-DEFTRAJ R4 CKT (C-EVAL CKT (S-LUB S R5))))
;			    (c (R-DEFTRAJ R6 CKT (C-EVAL CKT (S-LUB S R5))))
;			    )
;		 (:instance lemma-3
;			    (r r4)
;			    (c ckt)
;			    (s1 (C-EVAL CKT (S-LUB S R3)))
;			    (s2 (C-EVAL CKT (S-LUB S R5))))
;		 (:instance s-lte-c-eval-is-s-lte
;			    (c ckt)
;			    (s1 (s-lub s r3))
;			    (s2 (s-lub s r5))) ) )
; Version 2.4 hint

	  ("Subgoal *1/9.6'5'"
	   :in-theory (e/d (r-p-car) ; see v2-9 comment above
                           (r-lte-transitive lemma-3 s-lte-c-eval-is-s-lte))
	    :use (
		  (:instance s-lte-c-eval-is-s-lte
			     (c ckt)
			     (s1 (s-lub s r3))
			     (s2 (s-lub s r5)))
		  (:instance lemma-3
			     (r r4)
			     (c ckt)
			     (s1 (C-EVAL CKT (S-LUB S R3)))
			     (s2 (C-EVAL CKT (S-LUB S R5))))
		  (:instance r-lte-transitive
			     (a (R-DEFTRAJ R4 CKT (C-EVAL CKT (S-LUB S R3))))
			     (b (R-DEFTRAJ R4 CKT (C-EVAL CKT (S-LUB S R5))))
			     (c (R-DEFTRAJ R6 CKT (C-EVAL CKT (S-LUB S R5))))
			     )


		  ) )
	  ) )

(defthm r-lte-r-lub-r-deftraj-r-deftraj-r-lub
  (implies (and (r-p r1)
		(r-p r2)
		(s-p s)
		(c-p ckt)
		(equal (len ckt) (len s))
		(r-nmp r1 (len r1) (len s))
		(r-nmp r2 (len r1) (len s))
		)
	   (r-lte (r-lub (r-deftraj r1 ckt s)
			 (r-deftraj r2 ckt s))
		  (r-deftraj (r-lub r1 r2) ckt s))))



(defthm r-lte-r-lub-r-deftraj
  (implies (and (c-p ckt)
		(s-p s)
		(equal (len ckt) (len s))
		(r-p rc1)
		(r-p rc2)
		(r-p ra1)
		(r-p ra2)
		(r-nmp ra1 (len ra1) (len s))
		(r-nmp ra2 (len ra1) (len s))
		(r-nmp rc1 (len ra1) (len s))
		(r-nmp rc2 (len ra1) (len s))
		(r-lte rc1 (r-deftraj ra1 ckt s))
		(r-lte rc2 (r-deftraj ra2 ckt s))
		)
	   (r-lte (r-lub rc1 rc2)
		  (r-deftraj (r-lub ra1 ra2) ckt s)))
  :hints (("Goal"
	   :in-theory (disable r-lte-r-lub-r-deftraj-r-deftraj-r-lub
			       r-lub-r-lte-r-lub r-lte-transitive)
	   :use ((:instance r-lte-r-lub-r-deftraj-r-deftraj-r-lub
			    (r1 ra1)
			    (r2 ra2)
			    (ckt ckt)
			    (s s))
		 (:instance r-lub-r-lte-r-lub
			    (r1 rc1)
			    (r2 rc2 )
			    (r3 (r-deftraj ra1 ckt s) )
			    (r4 (r-deftraj ra2 ckt s))
			    )
		 (:instance r-lte-transitive
			    (a (R-LUB RC1 RC2))
			    (b (R-LUB (R-DEFTRAJ RA1 CKT S)
				      (R-DEFTRAJ RA2 CKT S)))
			    (c (R-DEFTRAJ (R-LUB RA1 RA2) CKT S) ))
		 )
	   )
	  )
  )



;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;

(defmacro ste-wft (ckt a c)
  `(and (l-p ,a)
	(l-p ,c)
	(c-p ,ckt)

	(equal (l-depth ,a) (l-depth ,c))
	(equal (l-maxn ,a) (l-maxn ,c))

	(equal (len ,ckt) (l-maxn ,a))
	))
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;

(defthm ste-thm-identity
  (ste-thm ckt a a))

(defthm ste-thm-shift-pre
  (implies (and (ste-wft ckt a c)
		(ste-thm ckt a c)
		)
	   (ste-thm ckt `(next ,a) `(next ,c)))

  :hints (("Goal" :in-theory (disable ste-thm
				      ste-thm-forward
				      ste-thm-backward) )
; Version 2.3 hint
;	  ("Subgoal 5'"
; Version 2.4 hint
	  ("Subgoal 2.2"
	   :use ((:instance r-lte-transitive
			    (a (L-DEFSEQ C (L-DEPTH A) (L-MAXN A)) )
			    (b (R-DEFTRAJ (L-DEFSEQ A (L-DEPTH A) (L-MAXN A))
					  CKT (S-MAKE (L-MAXN A) 'X)))
			    (c (R-DEFTRAJ (L-DEFSEQ A (L-DEPTH A) (L-MAXN A))
					  CKT
					  (C-EVAL CKT (S-MAKE (L-MAXN A) 'X))) )			    )		 ))
; Version 2.3 hints no longer needed
;	  ("Subgoal 3'"
;	   :use ((:instance l-evalp-when-n-l-depth-and-l-maxn (l c))))
;	  ("Subgoal 2"
;	   :use ((:instance l-evalp-when-n-l-depth-and-l-maxn (l c))))

	  ("Subgoal 1"
	   :use ((:instance l-evalp-when-n-l-depth-and-l-maxn (l c))))
	  )
  )

(defthm ste-thm-shift
  (implies (and (ste-wf ckt (a c))
		(ste-thm ckt a c)
		)
	   (ste-thm ckt `(next ,a) `(next ,c)))
  :hints (("Goal"
	   :use ((:instance ste-thm-shift-pre)))))

(defthm ste-thm-conjoin-pre
  (implies (and (ste-wft ckt a1 c1)
		(ste-wft ckt a2 c2)
		(equal (l-depth a1) (l-depth a2))
		(ste-thm ckt a1 c1)
		(ste-thm ckt a2 c2))
	   (ste-thm ckt `(and ,a1 ,a2) `(and ,c1 ,c2)))
  :hints (("Goal"
	   :in-theory (disable l-evalp-when-n-l-depth-and-l-maxn)
	   :do-not '(generalize fertilize)
	   :use ((:instance l-evalp-when-n-l-depth-and-l-maxn (l a1))
		 (:instance l-evalp-when-n-l-depth-and-l-maxn (l a2))
		 (:instance l-evalp-when-n-l-depth-and-l-maxn (l c1))
		 (:instance l-evalp-when-n-l-depth-and-l-maxn (l c2)))))
  :otf-flg t

  )

(defthm ste-thm-conjoin
  (implies (and (ste-wf ckt (a1 c1) (a2 c2))
		;(ste-wft ckt a2 c2)
		;(equal (l-depth a1) (l-depth a2))
		(ste-thm ckt a1 c1)
		(ste-thm ckt a2 c2))
	   (ste-thm ckt `(and ,a1 ,a2) `(and ,c1 ,c2)))
  :hints (("Goal"
	   ;:in-theory (disable l-evalp-when-n-l-depth-and-l-maxn)
	   ;:do-not '(generalize fertilize)
	   :use ((:instance ste-thm-conjoin-pre)))))


;(in-package "ACL2")
;
;(include-book "q")

(defthm lemma-5-bwd
  (implies (and (l-p a)
		(l-p c)
		(c-p ckt)
		(s-p s)
		(equal (len ckt) (len s))
		(equal (l-maxn a) (len s))
		(equal (l-maxn c) (len s))
		(equal (l-depth a) (l-depth c))
		(r-lte (r-deftraj (l-defseq c (l-depth c) (l-maxn c)) ckt s)
		       (r-deftraj (l-defseq a (l-depth a) (l-maxn a)) ckt s))
		)
	   (r-lte (l-defseq   c (l-depth c) (l-maxn c))
		  (r-deftraj (l-defseq a (l-depth a) (l-maxn a)) ckt s)))
  :hints (("Goal"
	   :in-theory (disable r-nmp-l-defseq r-lte-transitive  r-deftraj-r-lte R-LTE-L-DEFSEQ-R-DEFTRAJ)
	   :use ((:instance r-lte-transitive
			    (a (l-defseq   c (l-depth c) (l-maxn c)))
			    (b (r-deftraj (l-defseq c (l-depth c) (l-maxn c)) ckt s))
			    (c (r-deftraj (l-defseq a (l-depth a) (l-maxn a)) ckt s)))
		 (:instance r-deftraj-r-lte
			    (r (l-defseq   c (l-depth c) (l-maxn c)))
			    (c ckt)
			    (s s)
			    )
		 (:instance r-nmp-l-defseq (a c))
		 )
	   ))
  )


(defthm r-p-cons-1
  (implies (and (s-p s)
		(r-p r)
		)
	   (r-p (cons s r))))


(defthm deftraj-cons-expand
  (implies (and (s-p s1)
		(r-p r1)
		(c-p c)
		(s-p s)
		)
	   (equal (r-deftraj (cons s1 r1) c s)
		  (cons (s-lub s s1) (r-deftraj r1 c (c-eval c (s-lub s s1))))))
  )

(defthm s-lub-help
  (implies (and (s-p s1) (s-p s2) (s-p s)
		(s-lte s1 (s-lub s s2)))
	   (s-lte (s-lub s s1) (s-lub s s2)))
  :hints (("Goal"
	   :in-theory (enable b-p)))
  )

(defthm r-lte-r-deftraj-r-lte-r-deftrajs
  (implies (and (r-p r1)
		(r-p r2)
		(c-p ckt)
		(s-p s)
		(equal (len ckt) (len s))
		(r-nmp r1 (len r1) (len s))
		(r-nmp r2 (len r1) (len s))
		(r-lte r1 (r-deftraj r2 ckt s)))
	   (r-lte (r-deftraj r1 ckt s) (r-deftraj r2 ckt s)))
  :otf-flg t
  :hints (("Goal" :induct (induct-rrs r2 r1 s ckt))

; The following subgoal was changed to *1/1.7'' from *1/1.4'' by Matt K. for
; v2-9, due to the change to rewrite-clause that avoids using forward-chaining
; facts derived from a literal that has been rewritten.

; It was then further changed to 1/1.15'' by Matt K. upon introduction of
; rewrite-solidify-plus for making a second pass of rewriting for relieving
; hypotheses, because of which r-p-car is now disabled in run.lisp.

	  ("Subgoal *1/1.15''"
	   :in-theory (disable r-lte-transitive s-lub-help s-lte-s-lub)
	   :use ((:instance s-lub-help
			    (s1 r3)
			    (s2 (car r2))
			    (s s)
			    )
		 (:instance r-lte-transitive
			    (a (R-DEFTRAJ R4 CKT (C-EVAL CKT (S-LUB S R3))))
			    (b (R-DEFTRAJ R4 CKT (C-EVAL CKT (S-LUB S (CAR R2)))))
			    (c (R-DEFTRAJ (CDR R2)
					  CKT (C-EVAL CKT (S-LUB S (CAR R2))))))
		 ))
	  )
  )


(defthm len-defseq-help
  (implies (and (l-p l)
		(equal (l-depth l) n)
		(equal (l-maxn l) m)
		)
	   (equal (len (l-defseq l n m)) n)))

(defthm r-nmp-l-defseq-2
  (implies (and (l-p l)
		(equal (l-depth l) n)
		(equal (l-maxn l) m))
	   (r-nmp (l-defseq l n m) n m)))

(defthm lemma-5-fwd
  (implies (and (l-p a)
		(l-p c)
		(c-p ckt)
		(s-p s)
		(equal (len ckt) (len s))
		(equal (l-maxn a) (len s))
		(equal (l-maxn c) (len s))
		(equal (l-depth a) (l-depth c))
		(r-lte (l-defseq   c (l-depth c) (l-maxn c))
		       (r-deftraj (l-defseq a (l-depth a) (l-maxn a)) ckt s))
		)
	   (r-lte (r-deftraj (l-defseq c (l-depth c) (l-maxn c)) ckt s)
		  (r-deftraj (l-defseq a (l-depth a) (l-maxn a)) ckt s)))
  :hints (("Goal"
	   :in-theory (disable  r-lte-r-deftraj-r-lte-r-deftrajs)
	   :use ((:instance  r-lte-r-deftraj-r-lte-r-deftrajs
			     (r1 (l-defseq   c (l-depth c) (l-maxn c)))
			     (r2 (l-defseq a (l-depth a) (l-maxn a)))
			     (ckt ckt)
			     (s s)))
	   ))

  )

(defthm lemma-5
  (implies (and (l-p a)
		(l-p c)
		(c-p ckt)
		(s-p s)
		(equal (len ckt) (len s))
		(equal (l-maxn a) (len s))
		(equal (l-maxn c) (len s))
		(equal (l-depth a) (l-depth c))

		)
	   (iff (r-lte (l-defseq   c (l-depth c) (l-maxn c))
		       (r-deftraj (l-defseq a (l-depth a) (l-maxn a)) ckt s))
		(r-lte (r-deftraj (l-defseq c (l-depth c) (l-maxn c)) ckt s)
		       (r-deftraj (l-defseq a (l-depth a) (l-maxn a)) ckt s))))
  :hints (("Goal"
	   :use ((:instance lemma-5-fwd)
		 (:instance lemma-5-bwd)))))

;;;
;;; THIS THEOREM IS OK
;;;
;(defthm ste-thm-transitivity-simple
;  (implies (and (ste-wft ckt a1 c1)
;		(ste-wft ckt a2 c2)
;		(equal (l-depth a1) (l-depth a2))
;		(equal (l-maxn  a1) (l-maxn  a2))
;
;		(ste-thm ckt a1 c1)
;		(ste-thm ckt a2 c2)
;
;		(r-lte (l-defseq a2 (l-depth a2) (l-maxn a2))
;		       (l-defseq c1 (l-depth c1) (l-maxn c1)))
;
;		)
;	   (ste-thm ckt a1 c2))
;  :otf-flg t
;  :hints (("Goal"
;	   :do-not '(generalize fertilize)
;	   :in-theory (disable r-lte-transitive)
;	   :use ((:instance r-lte-transitive
;			    (a (l-defseq c2 (l-depth c2) (l-maxn c2)))
;			    (b (l-deftraj a2 ckt))
;			    (c (l-deftraj c1 ckt))
;			    )
;		  (:instance r-lte-transitive
;			    (a (l-defseq c2 (l-depth c2) (l-maxn c2)))
;			    (b (l-deftraj c1 ckt))
;			    (c (l-deftraj a1 ckt))
;			    )))))
;



(defthm z1
  (implies (and (r-lte (L-DEFSEQ C2 (L-DEPTH A1) (L-MAXN A1))
		       (R-DEFTRAJ (L-DEFSEQ A2 (L-DEPTH A1) (L-MAXN A1))
				  CKT (S-MAKE (L-MAXN A1) 'X)))
		(r-lte (R-DEFTRAJ (L-DEFSEQ A2 (L-DEPTH A1) (L-MAXN A1))
				  CKT (S-MAKE (L-MAXN A1) 'X))
		       (r-deftraj (R-LUB (L-DEFSEQ A1 (L-DEPTH A1) (L-MAXN A1))
					 (L-DEFSEQ C1 (L-DEPTH A1)
						   (L-MAXN A1)))
				  CKT (S-MAKE (L-MAXN A1) 'X)))
		(r-lte (r-deftraj (R-LUB (L-DEFSEQ A1 (L-DEPTH A1) (L-MAXN A1))
					 (L-DEFSEQ C1 (L-DEPTH A1)
						   (L-MAXN A1)))
				  CKT (S-MAKE (L-MAXN A1) 'X))
		       (R-DEFTRAJ (L-DEFSEQ A1 (L-DEPTH A1) (L-MAXN A1))
				  CKT (S-MAKE (L-MAXN A1) 'X)))
		)
	   (r-lte (L-DEFSEQ C2 (L-DEPTH A1) (L-MAXN A1))
		  (R-DEFTRAJ (L-DEFSEQ A1 (L-DEPTH A1) (L-MAXN A1))
			     CKT (S-MAKE (L-MAXN A1) 'X))
		  )
	   )
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance r-lte-transitive
			    (a (L-DEFSEQ C2 (L-DEPTH A1) (L-MAXN A1)))
			    (b (R-DEFTRAJ (L-DEFSEQ A2 (L-DEPTH A1) (L-MAXN A1))
					  CKT (S-MAKE (L-MAXN A1) 'X)))
			    (c (R-DEFTRAJ (L-DEFSEQ A1 (L-DEPTH A1) (L-MAXN A1))
					  CKT (S-MAKE (L-MAXN A1) 'X))))
		 (:instance r-lte-transitive
			    (a (R-DEFTRAJ (L-DEFSEQ A2 (L-DEPTH A1) (L-MAXN A1))
					  CKT (S-MAKE (L-MAXN A1) 'X)))
			    (b (r-deftraj (R-LUB (L-DEFSEQ A1 (L-DEPTH A1) (L-MAXN A1))
					 (L-DEFSEQ C1 (L-DEPTH A1)
						   (L-MAXN A1)))
				  CKT (S-MAKE (L-MAXN A1) 'X)))
			    (c (R-DEFTRAJ (L-DEFSEQ A1 (L-DEPTH A1) (L-MAXN A1))
					  CKT (S-MAKE (L-MAXN A1) 'X))))
		 ))))


(defthm z2
  (implies (and (ste-wft ckt a1 c1)
		(ste-wft ckt a2 c2)
		(equal (l-depth a1) (l-depth a2))
		(equal (l-maxn  a1) (l-maxn  a2))

		;;; ok
		(r-lte (L-DEFSEQ C2 (L-DEPTH A1) (L-MAXN A1))
		       (R-DEFTRAJ (L-DEFSEQ A2 (L-DEPTH A1) (L-MAXN A1))
				  CKT (S-MAKE (L-MAXN A1) 'X)))
		;;; ok
		(r-lte (r-deftraj (l-defseq a2 (l-depth a1) (l-maxn a1))
				  ckt (s-make (l-maxn a1) 'x))
		       (r-deftraj (R-LUB (L-DEFSEQ A1 (L-DEPTH A1) (L-MAXN A1))
					 (L-DEFSEQ C1 (L-DEPTH A1)
						   (L-MAXN A1)))
				  CKT (S-MAKE (L-MAXN A1) 'X)) )
		;;; ok
		(r-lte (r-deftraj (R-LUB (L-DEFSEQ A1 (L-DEPTH A1) (L-MAXN A1))
					 (L-DEFSEQ C1 (L-DEPTH A1)
						   (L-MAXN A1)))
				  CKT (S-MAKE (L-MAXN A1) 'X))
		       (R-DEFTRAJ (L-DEFSEQ A1 (L-DEPTH A1) (L-MAXN A1))
				  CKT (S-MAKE (L-MAXN A1) 'X)))
		)
	   (ste-thm ckt a1 c2))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance fundamental-theorem-of-ste
			    (a a1)
			    (c c2)
			    (ckt ckt)
			    )
		 (:instance z1))
	   ))
  )

(defthm z3
  (implies (and (l-p a2)
		(l-p c2)

		(c-p ckt)

		(EQUAL (L-DEPTH A2) (L-DEPTH C2))
		(EQUAL (L-MAXN A2) (L-MAXN C2))
		(EQUAL (LEN CKT) (L-MAXN A2))

		(EQUAL (L-MAXN A1) (L-MAXN a2))
		(EQUAL (L-DEPTH A1) (L-DEPTH a2))

		(ste-thm ckt a2 c2)
		)
	   (r-lte (L-DEFSEQ C2 (L-DEPTH A1) (L-MAXN A1))
		  (R-DEFTRAJ (L-DEFSEQ A2 (L-DEPTH A1) (L-MAXN A1))
			     CKT (S-MAKE (L-MAXN A1) 'X))))
  :rule-classes nil
  )

(defthm z4
  (implies (and (ste-wft ckt a1 c1)
		(ste-wft ckt a2 c2)
		(equal (l-depth a1) (l-depth a2))
		(equal (l-maxn  a1) (l-maxn  a2))

		(r-lte (l-defseq a2 (l-depth a2) (l-maxn a2))
		       (r-lub (l-defseq a1 (l-depth a1) (l-maxn a1))
			      (l-defseq c1 (l-depth c1) (l-maxn c1))))
		)
	   (r-lte (r-deftraj (l-defseq a2 (l-depth a1) (l-maxn a1))
			     ckt (s-make (l-maxn a1) 'x))
		  (r-deftraj (r-lub (l-defseq a1 (l-depth a1) (l-maxn a1))
				    (l-defseq c1 (l-depth a1)
					      (l-maxn a1)))
			     ckt (s-make (l-maxn a1) 'x)))))

(defthm z5
  (implies (and (ste-wft ckt a1 c1)
		(ste-thm ckt a1 c1)
		)
	   (r-lte (r-deftraj (R-LUB (L-DEFSEQ A1 (L-DEPTH A1) (L-MAXN A1))
				    (L-DEFSEQ C1 (L-DEPTH A1)
					      (L-MAXN A1)))
			     CKT (S-MAKE (L-MAXN A1) 'X))
		  (R-DEFTRAJ (L-DEFSEQ A1 (L-DEPTH A1) (L-MAXN A1))
			     CKT (S-MAKE (L-MAXN A1) 'X)))


	   )
  :hints (("Goal"
	   :in-theory (disable R-LTE-BOTH-IMPLIES-R-LTE-R-LUB
			       )
	   :use ((:instance R-LTE-BOTH-IMPLIES-R-LTE-R-LUB
			    (r1 (L-DEFSEQ A1 (L-DEPTH A1) (L-MAXN A1)))
			    (r2 (L-DEFSEQ C1 (L-DEPTH A1) (L-MAXN A1)))
			    (r (R-DEFTRAJ (L-DEFSEQ A1 (L-DEPTH A1) (L-MAXN A1))
					  CKT (S-MAKE (L-MAXN A1) 'X)))
			    )
		 )))

  )


(defthm ste-thm-transitivity-pre
  (implies (and (ste-wft ckt a1 c1)
		(ste-wft ckt a2 c2)
		(equal (l-depth a1) (l-depth a2))
		(equal (l-maxn  a1) (l-maxn  a2))

		(ste-thm ckt a1 c1)
		(ste-thm ckt a2 c2)

		(r-lte (l-defseq a2 (l-depth a2) (l-maxn a2))
		       (r-lub (l-defseq a1 (l-depth a1) (l-maxn a1))
			      (l-defseq c1 (l-depth c1) (l-maxn c1))))

		)
	   (ste-thm ckt a1 c2))
  :hints (("Goal"
	   :use ((:instance z2)
		 (:instance z3)
		 (:instance z4)
		 (:instance z5)
		 )
	   )
	  )
  )

(defthm ste-thm-transitivity
  (implies (and (ste-wf ckt (a1 c1) (a2 c2))

		(ste-thm ckt a1 c1)
		(ste-thm ckt a2 c2)

		(r-lte (defseq a2)
		       (r-lub (defseq a1)
			      (defseq c1)))
		)
	   (ste-thm ckt a1 c2))
  :hints (("Goal" :use ((:instance ste-thm-transitivity-pre)))))



(defthm ste-thm-transitivity-simple-pre
  (implies (and (ste-wft ckt a1 c1)
		(ste-wft ckt a2 c2)
		(equal (l-depth a1) (l-depth a2))
		(equal (l-maxn  a1) (l-maxn  a2))

		(ste-thm ckt a1 c1)
		(ste-thm ckt a2 c2)

		(r-lte (l-defseq a2 (l-depth a2) (l-maxn a2))
		       (l-defseq c1 (l-depth c1) (l-maxn c1)))

		)
	   (ste-thm ckt a1 c2))
  :otf-flg t
  :hints (("Goal"
	   :do-not '(generalize fertilize)
	   :in-theory (disable r-lte-transitive)
	   :use ((:instance r-lte-transitive
			    (a (l-defseq c2 (l-depth c2) (l-maxn c2)))
			    (b (l-deftraj a2 ckt))
			    (c (l-deftraj c1 ckt))
			    )
		  (:instance r-lte-transitive
			    (a (l-defseq c2 (l-depth c2) (l-maxn c2)))
			    (b (l-deftraj c1 ckt))
			    (c (l-deftraj a1 ckt))
			    )))))

(defthm ste-thm-transitivity-simple
  (implies (and (ste-wf ckt (a1 c1) (a2 c2))

		(ste-thm ckt a1 c1)
		(ste-thm ckt a2 c2)

		(r-lte (defseq a2)
		       (defseq c1))

		)
	   (ste-thm ckt a1 c2))
  :hints (("Goal" :use ((:instance ste-thm-transitivity-simple-pre)))))

;
;(in-package "ACL2");
;
;(include-book "x")

(defthm ste-thm-weaken-strengthen
  (implies (and (ste-wf ckt (a c) (a1 c1))
		(ste-thm ckt a c)
		(r-lte (defseq a) (defseq a1))
		(r-lte (defseq c1) (defseq c)))
	   (ste-thm ckt a1 c1))
  :hints (("Goal''"
	   :use ((:instance r-lte-transitive
			    (a (L-DEFSEQ C1 (L-DEPTH A) (L-MAXN A)))
			    (b (L-DEFSEQ C (L-DEPTH A) (L-MAXN A)))
			    (c (R-DEFTRAJ (L-DEFSEQ A1 (L-DEPTH A) (L-MAXN A))
					  CKT (S-MAKE (L-MAXN A) 'X))))
		 (:instance r-lte-transitive
			    (a (L-DEFSEQ C (L-DEPTH A) (L-MAXN A)))
			    (b (R-DEFTRAJ (L-DEFSEQ A (L-DEPTH A) (L-MAXN A))
					  CKT (S-MAKE (L-MAXN A) 'X)))
			    (c (R-DEFTRAJ (L-DEFSEQ A1 (L-DEPTH A) (L-MAXN A))
					  CKT (S-MAKE (L-MAXN A) 'X))))))))


(defthm ste-thm-strengthen-precondition
  (implies (and (ste-wf ckt (a c) (a1 c))
		(ste-thm ckt a c)
		(r-lte (defseq a) (defseq a1)))
	   (ste-thm ckt a1 c))
  :hints (("Goal"
	   :use ((:instance r-lte-reflexive
			    (r (L-DEFSEQ C (L-DEPTH C) (L-MAXN C))))
		 (:instance ste-thm-weaken-strengthen
			    (c1 c))))))


(defthm ste-thm-weaken-postcondition
  (implies (and (ste-wf ckt (a c) (a c1))
		(ste-thm ckt a c)
		(r-lte (defseq c1) (defseq c)))
	   (ste-thm ckt a c1))
  :hints (("Goal"
	   :use ((:instance r-lte-reflexive
			    (r (L-DEFSEQ A (L-DEPTH A) (L-MAXN A))))
		 (:instance ste-thm-weaken-strengthen
			    (a1 a)))))
  )

