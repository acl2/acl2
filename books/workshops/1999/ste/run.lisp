(in-package "ACL2")

(include-book "state")


(deflisttyped r-p s-p)

; Added by Matt K. for v2-9, upon introduction of rewrite-solidify-plus for
; making a second pass of rewriting for relieving hypotheses, upon seeing
; dominant usage in ste-thm-backward (file fundamental.lisp) with
; show-accumulated-persistence.
(in-theory (disable r-p-car))

(defuntyped r-nmp  ((r-p r) (naturalp n) (naturalp m)) t
  booleanp nil
  (if (and (consp r) (< 0 n))
      (and (equal (len (car r)) m)
	   (r-nmp (cdr r) (1- n) m))
    (and (equal r nil)
	 (equal n 0))))

(defthm r-nmp-nil
  (implies
   (and (equal n 0)
	(equal m 0))
   (r-nmp nil n m)))

(defthm r-nmp-cons
  (implies (and ;(r-p r)
		(s-p s)
		(positivep n)
		(r-nmp r (1- n) m)
		(equal (len s) m))
	   (r-nmp (cons s r) n m)))
;;;
;;; R_MAKE def and facts
;;;
(defuntyped r-make ((naturalp n) (s-p s)) t
  r-p nil
  (if (positivep n)
      (cons s (r-make (1- n) s))
    nil))

(defthm r-make-len
  (implies (and (s-p s)
		(naturalp n))
	   (equal (len (r-make n s)) n)))

(defthm r-make-r-nmp
  (implies (and (positivep n)
		(s-p s)
		(equal (len s) m))
	   (r-nmp (r-make n s) n m)))
;;;
;;; R-LUB
;;;
(defuntyped r-lub (r1 r2) t
  r-p nil
  (if (and (r-p r1) (r-p r2))
      (if (consp r1)
	  (if (consp r2)
	      (cons (s-lub (car r1) (car r2))
		    (r-lub (cdr r1) (cdr r2)))
	    r1)
	r2)
    nil))


(defthm r-lub-len
  (implies (and (r-p r1)
		(r-p r2)
		)
	   (equal (len (r-lub r1 r2))
		  (max (len r1) (len r2)))))

(defthm r-nmp-r-lub
  (implies (and (r-nmp r1 n m)
		(r-nmp r2 n m))
	   (r-nmp (r-lub r1 r2) n m)))

(defthm r-lub-commutes
  (equal (r-lub r1 r2) (r-lub r2 r1))
  :rule-classes nil)

;;;
;;; R-LTE
;;;
(defuntyped r-lte ((r-p r1) (r-p r2)) t
  booleanp nil
  (if (and (consp r1) (consp r2))
      (and (s-lte (car r1) (car r2))
	   (r-lte (cdr r1) (cdr r2)))
    (and (equal r1 nil)
	 (equal r2 nil))))

(defthm r-lte-reflexive
  (implies (r-p r)
	   (r-lte r r)))

(defthm r-lte-antisymmetric
  (implies (and (r-p a)
		(r-p b)
		(r-lte a b)
		(r-lte b a))
	   (equal a b))
  :rule-classes nil)

(defthm r-lte-transitive
  (implies (and (r-p a)
		(r-p b)
		(r-lte a b)
		(r-lte b c))
	   (r-lte a c)))
;;;
;;;
;;;



(defthm r-lte-r-lub-r1
  (implies (and (r-nmp r1 n m)
		(r-nmp r2 n m))
	   (r-lte r1 (r-lub r1 r2)))  )

(defthm r-lte-r-lub-r2
  (implies (and (r-nmp r1 n m)
		(r-nmp r2 n m))
	   (r-lte r2 (r-lub r1 r2)))  )

;;
;;;
;;

(defthm r-nmp-lte-0
  (IMPLIES (AND (R-P R1)
              (NOT R2)
              (CONSP R1)
              (R-NMP R1 N1 M1)
              (R-NMP R1 N M))
         (<= N1 N)))

(defthm consp-r-lub-5
  (implies (and (r-p r1)
		(r-p r2)
		(or (consp r1)
		    (consp r2))
		)
	   (consp (r-lub r1 r2))))

(defthm b-p-nth-car-r-lub-cons-6
  (IMPLIES (AND (INTEGERP L3)
		(<= 0 L3)
		(S-P R3)
		(R-P R4)
		(R-P R2)
		(EQUAL (NTH L3 R3) 'TOP))
	   (B-P (NTH L3 (CAR (R-LUB (CONS R3 R4) R2))))))

(defthm consp-r-lub-cons-4
  (implies (and (s-p s1)
		(r-p r1)
		(r-p r2)
	    )
	   (consp (r-lub (cons s1 r1) r2)))
  :hints (("Goal" :expand ((r-lub (cons s1 r1) r2))))
  )

(defthm cons-r-make-collapse
  (implies (and (naturalp n)
		)
	   (equal (cons (s-make m v)
			(r-make n (s-make m v)))
		  (r-make (1+ n) (s-make m v)))))


(defthm equal-r-make-bottom
  (implies (and (naturalp m)
		(r-p r)
		(r-lte r (r-make (len r) (s-make m 'x)))
		)
	   (equal (r-make (len r) (s-make m 'x)) r))
  :hints (("Goal" :induct (r-p r)
           ;; r-p-car re-enabled by Matt K. to compensate for v2-9 change of
           ;; disabling this rule near the top of this file.
           :in-theory (enable r-p-car))
	  ("Subgoal *1/2.2'" :use ((:instance s-lte-implies-len-equal
					      (s1 r1) (s2 (s-make m 'x)))))))

(defthm r-lte-implies-len-equal
  (implies (r-lte r1 r2)
	   (equal (len r1) (len r2)))
  :rule-classes nil)

(defthm equal-r-make-bottom-2
  (implies (and (naturalp n)
		(naturalp m)
		(r-lte r (r-make n (s-make m 'x)))
		)
	   (equal (r-make n (s-make m 'x)) r))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance equal-r-make-bottom)
		 (:instance r-lte-implies-len-equal (r1 r) (r2 (r-make n (s-make m 'x)))) )
	   ))
  )

(defthm r-lub-same
  (implies (r-p r)
	   (equal (r-lub r r) r)))

(defthm r-make-1
  (implies (s-p s)
	   (equal (r-make 1 s)
		  (list s)))
  :hints (("Goal" :expand ((r-make 1 s)))))

(defuntyped s-consistent ((s-p s)) t
  booleanp nil
  (if (consp s)
      (and (not (equal (car s) 'top))
	   (s-consistent (cdr s)))
    t))

(defuntyped r-consistent ((r-p r)) t
  booleanp nil
  (if (consp r)
      (and (s-consistent (car r))
	   (r-consistent (cdr r)))
    t))

(defthm  consp-r-make-plus-1
  (implies (and (s-p s)
		(naturalp n)
		)
	   (consp (r-make (+ 1 n) s))))




(defthm r-lub-r-lte-r-lub
  (implies (and (r-p r1)
		(r-p r2)
		(r-p r3)
		(r-p r4)
		(r-lte r1 r3)
		(r-lte r2 r4))
	   (r-lte (r-lub r1 r2)
		  (r-lub r3 r4))))


(defthm r-lub-r-lte-rewrite-1
  (implies (and (r-p r)
		(r-p r1)
		(r-lte r1 r))
	   (equal (r-lub r r1) r)))

(defthm r-lub-r-lte-rewrite-2
  (implies (and (r-p r)
		(r-p r1)
		(r-lte r1 r))
	   (equal (r-lub r1 r) r)))


(defthm r-lte-r-make-s-make-cons
  (IMPLIES (AND (CONSP (CONS R1 R2))
              (INTEGERP N)
              (< 0 N)
              (R-LTE (R-MAKE (+ -1 N) (S-MAKE (LEN R1) 'X))
                     R2)
              (S-P R1)
              (R-P R2)
              (R-NMP R2 (+ -1 N) (LEN R1))
              (< 0 (LEN R1)))
         (R-LTE (R-MAKE N (S-MAKE (LEN R1) 'X))
                (CONS R1 R2))))

(defthm r-lte-r-make
  (implies (and (r-p r)
		(naturalp n)
		(naturalp m)
		(r-nmp r n m))
	   (r-lte (r-make n (s-make m 'x)) r))
  )

(defthm r-lub-r-lte-r-lub-r-1
  (implies (and (r-p r)
		(r-p r3)
		(r-p r4)
		(r-lte r r3)
		(r-lte r r4))
	   (r-lte r
		  (r-lub r3 r4)))
   :hints (("Goal" :use ((:instance r-lub-r-lte-r-lub (r1 r) (r2 r))))))

(defthm r-lub-r-lte-r-lub-r-2
  (implies (and (r-p r1)
		(r-p r2)
		(r-p r)
		(r-lte r1 r)
		(r-lte r2 r))
	   (r-lte (r-lub r1 r2)
		  r))
  :hints (("Goal" :use ((:instance r-lub-r-lte-r-lub (r3 r) (r4 r))))) )

(defthm r-lte-both-implies-r-lte-r-lub
  (implies (and (r-p r)
		(r-p r1)
		(r-p r2)
		(r-lte r1 r)
		(r-lte r2 r)
		)
	   (r-lte (r-lub r1 r2) r)))
(defthm not-r-lte-1-implies-not-r-lte-r-lub
  (implies
   (and (r-p r)
	(r-p r1)
	(r-p r2)
	(naturalp n)
	(naturalp m)
	(r-nmp r1 n m)
	(r-nmp r2 n m)
	(r-nmp r  n m)
	(not (r-lte r1 r))
	)
   (not (r-lte (r-lub r1 r2) r)))
  :hints (("Goal" :do-not '(generalize fertilize) )) )

(defthm not-r-lte-2-implies-not-r-lte-r-lub
  (implies
   (and (r-p r)
	(r-p r1)
	(r-p r2)
	(naturalp n)
	(naturalp m)
	(r-nmp r1 n m)
	(r-nmp r2 n m)
	(r-nmp r  n m)
	(not (r-lte r2 r))
	)
   (not (r-lte (r-lub r1 r2) r)))
  :hints (("Goal"
	   :use ((:instance not-r-lte-1-implies-not-r-lte-r-lub
			    (r1 r2) (r2 r1))
		 (:instance r-lub-commutes))
	   )) )
