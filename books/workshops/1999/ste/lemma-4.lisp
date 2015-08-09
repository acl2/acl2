(in-package "ACL2")

(include-book "assertion")

; Added for ACL2 Version  2.7:
(set-match-free-default :once)
(add-match-free-override :once t)

(defuntyped r-deftraj ((r-p r) (c-p c) (s-p s)) t
  r-p nil
  (if (consp r)
      (let ((s1 (s-lub s (car r)) ))
	(cons s1 (r-deftraj (cdr r) c (c-eval c s1))))
    nil))

(defthm s-lte-s-lub-1
 (implies (and (s-p s1)
	       (s-p s2)
	       (equal (len s1) (len s2))
	       )
	  (s-lte s1 (s-lub s1 s2))))

(defthm s-lte-s-lub-2
 (implies (and (s-p s1)
	       (s-p s2)
	       (equal (len s1) (len s2))
	       )
	  (s-lte s2 (s-lub s1 s2))))

(defthm r-nmp-len-r
  (implies (and (r-p r)
		(naturalp n)
		(naturalp m)
		(r-nmp r n m))
	   (equal (len r) n)))

(defthm r-nmp-consp-len-r1
  (implies (and (s-p s)
		(r-p r)
		(r-nmp (cons s r) n m))
	   (equal (len s) m)))

(defthm r-nmp-consp-len-r2
  (implies (and (s-p s)
		(r-p r)
		(consp r)
		(r-nmp (cons s r) n m))
	   (equal (len (car r)) m))

  :hints (("Goal" :do-not-induct t
	   :expand ((R-NMP (LIST* S R1 R2) N M))
	   ))
  )



(defthm len-s-lub
  (implies (and (s-p s1)
		(s-p s2)
		(equal (len s1) (len s2))
		)
	   (equal (len (s-lub s1 s2)) (len s1))))

(defthm len-c-eval
  (implies (and (c-p c)
		(s-p s)
		)
	   (equal (len (c-eval c s)) (len c))))

;(defthm r-deftraj-nil-c
;  (implies (and ;(c-p c)
;		(r-p r)
;		(naturalp n)
;		(r-nmp r n 0))
;	   (t-p (r-deftraj nil r nil) nil))
;  :hints (("Goal"
;	   :in-theory (disable r-nmp)))
;  )


(defthm car-r-deftraj-nil-rewrite
 (IMPLIES (AND (R-P R2)
	       (R-NMP (CONS R1 R2) (+ 1 (LEN R2)) 0))
	  (NOT (CAR (R-DEFTRAJ R2 NIL NIL)))))

(defthm r-nmp-less-1
  (implies (r-nmp (cons r1 r2) (+ 1 (len r2)) m)
	   (r-nmp r2 (len r2) m)))

(defthm r-deftraj-is-t-p
  (implies (and (c-p c)
		(s-p s)
		(equal (len c) (len s))

		(r-p r)
		(r-nmp r (len r) (len s))
		)
	   (t-p (r-deftraj r c s) c))
  :hints (("Goal"
	   :in-theory (disable r-nmp)
	   :do-not '(generalize fertilize))
	  ("Subgoal *1/5.3'''"
	   :expand ((R-DEFTRAJ R2 C (C-EVAL C (S-LUB S R1))))
	   )
	  ("Subgoal *1/5.3'4'"
	   :in-theory (disable s-lte-s-lub-1 len-c-eval len-s-lub
			       s-lub-len s-lub-s1 r-nmp-consp-len-r2)
	   :use ((:instance  s-lte-s-lub-1
			     (s1 (C-EVAL C (S-LUB S R1)))
			     (s2 (CAR R2)))
		 (:instance len-c-eval
			    (c c)
			    (s (s-lub s r1)))
		 (:instance len-s-lub
			    (s1 s)
			    (s2 r1))
		 (:instance r-nmp-consp-len-r2
			    (s r1)
			    (r r2)
			    (n (+ 1 (len r2)))
			    (m (len c)))
		 )

	   )
          ;; Added for v2-8 (just a wild guess) to deal with changes in
          ;; induction (less inhibiting of induction-hyp-terms and expansion of
          ;; induction-concl-terms:
	  ("Subgoal *1/5.1.2''"
	   :expand ((R-DEFTRAJ R2 C (C-EVAL C S)))
	   )
          ;; Added for v2-8 (see comment just above):
	  ("Subgoal *1/5.1.2'''"
	   :in-theory (disable s-lte-s-lub-1 len-c-eval len-s-lub
			       s-lub-len s-lub-s1 r-nmp-consp-len-r2)
	   :use (;(:instance  s-lte-s-lub-1
		;	     (s1 (C-EVAL C (S-LUB S R1)))
			;     (s2 (CAR R2)))
		 (:instance len-c-eval
			    (c c)
			    (s s))
		; (:instance len-s-lub
		;	    (s1 s)
		;	    (s2 r1))
		 (:instance r-nmp-consp-len-r2
			    (s r1)
			    (r r2)
			    (n (+ 1 (len r2)))
			    (m (len c)))
		 )

	   )
	  ("Subgoal *1/5.1.1'''"
	   :expand ((R-DEFTRAJ R2 C (C-EVAL C S)))
	   )
	  ("Subgoal *1/5.1.1'4'"
	   :in-theory (disable s-lte-s-lub-1 len-c-eval len-s-lub
			       s-lub-len s-lub-s1 r-nmp-consp-len-r2)
	   :use (;(:instance  s-lte-s-lub-1
		;	     (s1 (C-EVAL C (S-LUB S R1)))
			;     (s2 (CAR R2)))
		 (:instance len-c-eval
			    (c c)
			    (s s))
		; (:instance len-s-lub
		;	    (s1 s)
		;	    (s2 r1))
		 (:instance r-nmp-consp-len-r2
			    (s r1)
			    (r r2)
			    (n (+ 1 (len r2)))
			    (m (len c)))
		 )

	   )
	  ) )


(defuntyped l-deftraj ((l-p l) (c-p c)) t
  r-p nil
  (r-deftraj (l-defseq l (l-depth l) (l-maxn l))
	     c
	     (s-make (l-maxn l) 'x)))

(defthm lemma-4-1
  (implies (and (l-p l)
		(c-p c)
		(equal (len c) (l-maxn l))
		)
	   (t-p (l-deftraj l c) c)))


;(in-package "ACL2")

;(include-book "m")

(defthm r-deftraj-is-consp
  (implies (and (r-p r)
		(consp r)
		(c-p c)
		(s-p s)
		)
	   (consp (r-deftraj r c s))))

(defthm r-lte-r-deftraj-nils
 (IMPLIES (AND (R-P R2)
	       (R-NMP R2 N 0)
	       )
	  (R-LTE R2 (R-DEFTRAJ R2 NIL NIL))))

(defthm r-deftraj-r-lte
  (implies (and (r-p r)
		(c-p c)
		(s-p s)
		(equal (len c) (len s))
		(r-nmp r (LEN R) (len s))
		)
	   (r-lte r (r-deftraj r c s)))  )

(defthm r-deftraj-l-eval
  (implies (and (r-p r)
		(l-p l)
		(l-eval l r)
		(c-p c)
		(s-p s)
		(equal (len c) (len s))
		(r-nmp r (LEN R) (len s))
		)
	   (l-eval l (r-deftraj r c s)))  )

(defthm lemma-4-2
  (implies (and (c-p c)
		(l-p l)
		(equal (len c) (l-maxn l))
		)
	   (l-eval l (l-deftraj l c))) )

;(in-package "ACL2")

;(include-book "n")


(defthm s-lte-forward-equal-len
  (implies (s-lte s1 s2)
	   (equal (len s1) (len s2)))
  :rule-classes :forward-chaining)





(defthm lemma-3-a
  (implies (and (s-p s1)
		(s-p s2)
		(s-lte s1 s2)

		(c-p c)
		(equal (len c) (len s1))

		(r-p r)
		(naturalp n)
		(r-nmp r n (len s1))
		)

	   (r-lte (r-deftraj r c s1)
		  (r-deftraj r c s2))))

(defthm lemma-3
  (implies (and ;(l-p l)
		(c-p c)
		(r-p r)
		(s-p s1)
		(s-p s2)
		(s-lte s1 s2)
		)
	   (r-lte (r-deftraj r c s1)
		  (r-deftraj r c s2))))


(defthm lemma-4-3-backward
  (implies (and (l-p l)
		(c-p c)
		(equal (len c) (l-maxn l))
		(r-p r)
		(t-p r c)
		(r-lte (l-deftraj l c) r))
	   (l-eval l r))
  :hints (("Goal"
	   :use ((:instance lemma-1
			    (l l)
			    (r1 (l-deftraj l c))
			    (r2 r)))
	   ))
  )


(defuntyped r-deftraj-induct  ((r-p r) (c-p c) (s-p s) (r-p rr)) t
  booleanp nil
  (if (and (consp r) (consp rr))
      (r-deftraj-induct (cdr r) c (c-eval c (s-lub s (car r))) (cdr rr))
    nil))


(defthm r-nmp-nil-positive
  (implies (and (positivep n)
		)
	   (not (r-nmp nil n m))))


(defuntyped l-induct-rrs ((l-p l) (r-p r1) (r-p r2) (s-p s) (c-p c)) t
  boolean-listp nil
  (if (and (consp r1) (consp r2))
      (if (equal l t)
	  nil
	(case-match l
		    (('is & &)    nil)
		    (('and l1 l2) (append (l-induct-rrs l1 r1 r2 s c)
					  (l-induct-rrs l2 r1 r2 s c)))
		    (('when b l1) (if b (l-induct-rrs l1 r1 r2 s c) nil))
		    (('next l1)
		     (l-induct-rrs l1 (cdr r1) (cdr r2)
				   (c-eval c (s-lub s (car r1))) c))))
    nil))


(defthm hooyah
  (implies (and (r-p r)
		(naturalp m)
		(naturalp n)
		(r-nmp r (+ 1 n) m))
	   (r-nmp (cdr r) n m)))


(defthm hooyah-2
  (IMPLIES (AND ;(R-P R3)
		(R-P R1)
		;(S-P S)
		;(C-P C)
		(CONSP R1)
		;(EQUAL (LEN C) 0)
		;(EQUAL (LEN S) 0)
		;(EQUAL 0 (LEN R3))
		(EQUAL (LEN R1) 1)
		(R-nMP R1 1 0))
         (R-LTE (R-DEFTRAJ R1 NIL NIL) '(NIL)))
  )


(defthm hooyah-3
 (implies (and (s-p s1)
	       (s-p s2)
	       (s-lte s1 s2))
	  (equal (s-lub s1 s2) s2)))

(defuntyped induct-rrs ( (r-p r1) (r-p r2) (s-p s) (c-p c)) t
  boolean-listp nil
  (if (and (consp r1) (consp r2))
      (induct-rrs (cdr r1) (cdr r2) (c-eval c (s-lub s (car r1))) c)
    nil))



(defthm s-lte-s-lub
  (implies (and (s-p s1)
		(s-p s2)
		(s-p s)
		(s-lte s1 s)
		(s-lte s2 s))
	   (s-lte (s-lub s1 s2) s)))

(defthm s-lte-c-eval-s-lub
  (implies (and (c-p c)
		(s-p s)
		(equal (len c) (len s))
		(s-p s1)
		(s-p s2)
		(s-p s3)
		(s-lte s1 s)
		(s-lte s2 s)
		(s-lte (c-eval c s) s3)
		)
	   (s-lte (c-eval c (s-lub s1 s2)) s3))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance s-lte-c-eval-is-s-lte
			    (c c)
			    (s1 (s-lub s1 s2))
			    (s2 s))
		 (:instance s-lte-transitive
			    (a (c-eval c (s-lub s1 s2)))
			    (b (c-eval c s))
			    (c s3)))
	   ))
  )


(defthm l-eval-implies-r-deftraj-r-lte
  (implies (and (c-p c)

		(s-p s)

		(equal (len c) (len s))

		(r-p r)
		(r-nmp r (len r) (len s))

		(t-p r c)

		(s-lte s (car r))

		(r-p r1)
		(r-nmp r1 (len r1) (len s))

		(r-lte r1 r))
	   (r-lte (r-deftraj  r1 c s) r))
  :hints (("Goal" :induct (induct-rrs r1 r s c))

; The following subgoal was changed to *1/1.3.1 from *1/1.7.1 by Matt K. for
; v2-9, due to the change to rewrite-clause that avoids using forward-chaining
; facts derived from a literal that has been rewritten.

; It was then further changed to 1/1.9.1 by Matt K. upon introduction of
; rewrite-solidify-plus for making a second pass of rewriting for relieving
; hypotheses, because of which r-p-car is now disabled (in earlier file
; run.lisp).

	  ("Subgoal *1/1.9.1"
	   :use ((:instance s-lte-c-eval-s-lub
			    (s1 s)
			    (s2 (car r1))
			    (s r2)
			    (s3 r4)
			    )) ) ) )


(defthm l-eval-implies-r-deftraj-l-defseq-r-lte
  (implies (and (c-p c)

		(s-p s)
		(equal (len c) (len s))

		(r-p r)
		(r-nmp r (len r) (len s))

		(t-p r c)

		(s-lte s (car r))

		(l-p l)
		(equal (l-depth l) (len r))
		(equal (l-maxn l)  (len s))

		(l-eval l r)

		)
	   (r-lte (r-deftraj  (l-defseq l (l-depth l) (l-maxn l)) c s) r))
  )

(defthm r-nmp-foo
  (implies (r-nmp r n m)
	   (r-nmp r (len r) m)))
(defthm r-nmp-bar
  (implies (r-nmp r n m)
	   (equal (len r) n)))

(defthm r-nmp-doo
 (implies (and (s-p s) s )
	  (not (r-nmp (cons s r) n 0))))


(defthm lemma-4-3-forward
  (implies (and (l-p l)
		(c-p c)
		(equal (len c) (l-maxn l))
		(r-p r)
		(r-nmp r (l-depth l) (l-maxn l))
		(t-p r c)
		(l-eval l r))
	   (r-lte (l-deftraj l c) r))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance l-eval-implies-r-deftraj-l-defseq-r-lte
			    (c c)
			    (s (s-make (l-maxn l) 'x))
			    (r r)
			    (l l)
			    ))
	   ))
  )

(defthm lemma-4-3
  (implies (and (l-p l)
		(c-p c)
		(equal (len c) (l-maxn l))
		(r-p r)
		(r-nmp r (l-depth l) (l-maxn l))
		(t-p r c))
	   (iff (l-eval l r)
		(r-lte (l-deftraj l c) r)))
  :hints (("Goal"
	   :use ((:instance lemma-4-3-forward)
		 (:instance lemma-4-3-backward))
	   ))
  )

(defmacro deftraj (a ckt)
  `(r-deftraj (l-defseq ,a (l-depth ,a) (l-maxn ,a)) ,ckt (s-make (l-maxn ,a) 'x)))

(defthm lemma-4
  (implies (and (l-p l)
		(c-p c)
		(equal (len c) (l-maxn l))
		(r-p r)
		(r-nmp r (l-depth l) (l-maxn l))
		(t-p r c))
	   (and (t-p (deftraj l c) c)
		(l-eval l (deftraj l c))
		(iff (l-eval l r)
		     (r-lte (deftraj l c) r))))
  :hints (("Goal"
	   :use ((:instance lemma-4-1)
		 (:instance lemma-4-2)
		 (:instance lemma-4-3))))
  )
