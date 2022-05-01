; complexity-of-linear-search.lsp                     William D. Young

(in-package "ACL2")
(include-book "asymptotic-analysis-support")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                  ;;
;;                          LINEAR SEARCH                           ;;
;;                                                                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Next up: try a more complicated program.
;; Linear Search:

; linearSearch( x, lst ):
;    i = 0
;    while (i < len(lst)):
;       if (lst[i] ==  x):
;          return i
;       else:
;          i += 1
;    return -1

(set-irrelevant-formals-ok t)

(defun linearsearch-if-else (i x lst)
  `(if-else (== (ind ,i ,lst) ,x)
	    (return ,i)
	    (assign ,i (+ ,i (lit . 1)))))

(defun linearsearch-while (i x lst)
  `(while (< ,i (len ,lst))
     ,(linearsearch-if-else i x lst)))

(defun linearsearch (i x lst )
  `(seq (assign ,i (lit . 0))
	(seq ,(linearsearch-while i  x lst)
	     (return (lit . -1)))))

(defthm linearsearch-if-else-lemma2
  (implies (and (okp stat)
		(varp i)
		(acl2-numberp (lookup (param1 i) vars))
		(exeval-status (exeval (list '== (list 'ind i lst) x) t vars))
		(not (zp count)))
	   (equal (run (linearsearch-if-else i x lst) stat vars steps count)
		  (if (exeval-value (exeval (list '== (list 'ind i lst) x) t vars))
		      (mv 'returned
			  (store 'result
				 (lookup (param1 i) vars)
				 vars)
			  (+ 6 steps
			     (exeval-steps (exeval lst t vars))
			     (exeval-steps (exeval x t vars))))
		      (mv 'ok
			  (store (param1 i)
				 (+ 1 (lookup (param1 i) vars))
				 vars)
			  (+ 8 steps
			     (exeval-steps (exeval lst t vars))
			     (exeval-steps (exeval x t vars))))))))

(in-theory (disable linearsearch-if-else))

(defun first-after (n x l)
  ;; Find the index of the first occurrence of x in l
  ;; starting at index n
  (declare (xargs :measure (nfix (- (len l) n))))
  (if (or (<= (len l) n)
	  (not (integerp n)))
      -1
    (if (equal x (nth n l))
	n
      (first-after (1+ n) x l))))

(defthm first-after-nth
  (implies (and (< n (len l))
		(natp n))
	   (equal (first-after n (nth n l) l)
		  n)))

(defthm first-after-not-nth
  (implies (and (natp n)
		(< n (len l))
		(not (equal x (nth n l))))
	   (equal (first-after n x l)
		  (first-after (1+ n) x l))))

(defthm first-after-len-lemma0
  (implies (member-equal x lst)
	   (< (first-after i x lst) (len lst)))
  :rule-classes (:linear :rewrite))

(defthm first-after-posp
  (implies (and (member-equal x lst)
		(natp i))
	   (<= -1 (first-after i x lst)))
  :rule-classes (:linear :rewrite))

(defthmd run-ls-while-expander-test-fails
  (implies (and (okp stat)
		(varp i)
		(integerp (lookup (param1 i) vars))
		(varp lst)
		(definedp (param1 lst) vars)
		(listp (lookup (param1 lst) vars))
		(natp steps)
		(not (zp count))
		(not (exeval-value (exeval (list '< i (list 'len lst)) t vars)))
		)
	   (equal (run (linearsearch-while i x lst) stat vars steps count)
		  (mv stat vars (+ 5 steps)))))

(defthmd run-ls-while-expander2
  (implies (and (okp stat)
		(varp i)
		(integerp (lookup (param1 i) vars))
		(not (zp count))
		(natp steps)
		;; lst[i] == x
		(exeval-status (exeval (list '< i (list 'len lst)) t vars)) 
		)
	   (equal (run (linearsearch-while i x lst) stat vars steps count)
		  (let ((exeval-<-steps (+ 3 steps
					   (exeval-steps (exeval i t vars))
					   (exeval-steps (exeval lst t vars)))))
		    (if (exeval-value (exeval (list '< i (list 'len lst)) t vars))
			(run (linearsearch-while i x lst) 
			     (run-status
			      (run (linearsearch-if-else i x lst)
				   'ok vars exeval-<-steps count))
			     (run-vars
			      (run (linearsearch-if-else i x lst)
				   'ok vars exeval-<-steps count))
			     (run-steps
			      (run (linearsearch-if-else i x lst)
				   'ok vars exeval-<-steps count))
			     (+ -1 count))
		      (mv stat vars exeval-<-steps))))))

(defthmd run-ls-while-expander3
  (implies (and (okp stat)
		(varp i)
		(natp (lookup (param1 i) vars))
		(varp lst)
		(definedp (param1 lst) vars)
		(listp (lookup (param1 lst) vars))
		(definedp-varp x vars)
		(natp steps)
		(not (zp count))
		;; i < len(lst)
		(exeval-value (exeval (list '< i (list 'len lst)) t vars))
		;; lst[i] == x
		(exeval-value (exeval (list '== (list 'ind i lst) x) t vars))
		)
	   (equal (run (linearsearch-while i x lst)
		       stat vars steps count)
		  (list 'returned
			(store 'result
			       (lookup (param1 i) vars)
			       vars)
			(+ 13 steps))))
  :hints (("Goal" :in-theory (e/d (run-ls-while-expander2
				   linearsearch-if-else-lemma2)
				  (linearsearch-while))
	          :do-not-induct t)))

(defthmd run-ls-while-expander4
  (implies (and (okp stat)
		(varp i)
		(natp (lookup (param1 i) vars))
		(varp lst)
		(definedp (param1 lst) vars)
		(listp (lookup (param1 lst) vars))
		(varp x)
		(definedp (param1 x) vars)
		(natp steps)
		(not (zp count))
		;; i < len(lst)
		(exeval-value (exeval (list '< i (list 'len lst)) t vars))
		;; lst[i] != x
		(not (exeval-value (exeval (list '== (list 'ind i lst) x) t vars)))
		)
	   (equal (RUN (LINEARSEARCH-WHILE I X LST)
		       STAT VARS steps COUNT)
		  (RUN (LINEARSEARCH-WHILE I X LST)
		       'ok (STORE (param1 i) (1+ (lookup (param1 i) vars)) VARS)
		       (+ 15 steps)
		       (+ -1 COUNT)))) 
  :hints (("Goal" :in-theory (e/d (RUN-LS-WHILE-EXPANDER2
				   LINEARSEARCH-IF-ELSE-LEMMA2)
				  (linearsearch-while))
	          :do-not-induct t)))

(in-theory (disable linearsearch-while))

(defun ls-while-ind0 (n i l vars steps count)
  (declare (xargs :measure (nfix (- (len l) n))))
  (if (or (>= n (len l))
	  (not (integerp n)))
      t
    (ls-while-ind0 (1+ n)
		   i
		   l
		   (store (param1 i) (1+ n) vars)
		   (+ 15 steps)
		   (1- count))))

(defthm linearsearch-while-lemma0
  (let ((ival (lookup (param1 i) vars))
	(xval (lookup (param1 x) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (okp stat)
		  (varp i)
		  (natp ival)
		  (varp lst)
		  (true-listp lstval)
		  lstval
		  (varp x)
		  (not (equal (param1 x) (param1 i)))
		  xval
		  (not (equal (param1 lst) (param1 i)))
		  (equal n ival)
		  (equal l lstval)
		  (natp steps)
		  (integerp count)
		  (not (timedoutp (run-status (run (linearsearch-while i x lst) stat vars steps count))))
		  (not (member-equal xval (nthcdr ival lstval)))
		  )
	     (equal (run (linearsearch-while i x lst) stat vars steps count)
		    (if (< ival (len lstval))
			(mv 'ok
			    (store (param1 i) (len lstval) vars)
			    (+ 5 (* (- (len lstval) ival) 15) steps))
		      (mv 'ok vars (+ 5 steps))))))
  :hints (("goal" :instructions
	   (:expand 
		    (:in-theory (disable run-ls-while-expander4))
		    (:induct (ls-while-ind0 n i l vars steps count))
		    (:prove :hints (("Goal" :use (:instance run-ls-while-expander4))))
		    (:prove :hints (("Goal" :use (:instance run-ls-while-expander-test-fails (stat 'ok)))))))))

(defun ls-while-ind1 (n i x l vars steps count)
  (declare (xargs :measure (nfix (- (len l) n))))
  (if (or (>= n (len l))
	  (not (integerp n)))
      t
    (if (equal (lookup (cadr x) vars) (nth n l))
	t
      (ls-while-ind1 (1+ n)
		     i
		     x
		     l
		     (store (param1 i) (1+ n) vars)
		     (+ 15 steps)
		     (1- count)))))

(defthmd linearsearch-while-lemma1
  (let ((ival (lookup (param1 i) vars))
	(xval (lookup (param1 x) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (okp stat)
		  (varp i)
		  (natp ival)
		  (varp lst)
		  (true-listp lstval)
		  lstval
		  (varp x)
		  (not (equal (param1 x) (param1 i)))
		  xval
		  (not (equal (param1 lst) (param1 i)))
		  (equal n ival)
		  (equal l lstval)
		  (integerp count)
		  (natp steps)
		  (not (timedoutp (run-status (run (linearsearch-while i x lst) stat vars steps count))))
		  (member-equal xval (nthcdr ival lstval))
		  (< ival (len lstval))
		  )
	     (equal (run (linearsearch-while i x lst) stat vars steps count)
		    (let ((index (first-after ival xval lstval)))
		      (mv 'returned
			  (store 'result index
				 (store (param1 i)
					index
					vars))
			  (+ 13 (* 15 (- index ival)) steps))))))
  :hints (("Goal" :INSTRUCTIONS
	   (:EXPAND
	    (:INDUCT (LS-WHILE-IND1 N I X L VARS STEPS COUNT))
	    (:PROVE :HINTS (("Goal" :USE (:INSTANCE RUN-LS-WHILE-EXPANDER4))))
	    (:PROVE :HINTS (("Goal" :USE (:INSTANCE RUN-LS-WHILE-EXPANDER3))))
	    :PROVE))))

(defthmd linearsearch-while-lemma-final
  (let ((ival (lookup (param1 i) vars))
	(xval (lookup (param1 x) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (varp i)
		  (natp ival)
		  (varp lst)
		  (true-listp lstval)
		  lstval
					;(not (equal (param1 lst) 'result))
		  (varp x)
		  (not (equal (param1 x) (param1 i)))
		  xval
		  (not (equal (param1 lst) (param1 i)))
		  (equal n ival)
		  (equal l lstval)
		  (natp steps)
		  (integerp count)
		  (not (timedoutp (run-status (run (linearsearch-while i x lst) stat vars steps count))))
		  )
	     (equal (run (linearsearch-while i x lst) stat vars steps count)
		    (let ((index (first-after ival xval lstval)))
		      (if (not (okp stat))
			  (mv stat vars steps)
			(if (member-equal xval (nthcdr ival lstval))
			    (mv 'returned
				(store 'result index
				       (store (param1 i)
					      index
					      vars))
				(+ 13 (* 15 (- index ival)) steps))
			  (if (< ival (len lstval))
			      (mv stat
				  (store (param1 i) (len lstval) vars)
				  (+ 5 (* (- (len lstval) ival) 15) steps))
			    (mv stat vars (+ 5 steps)))))))))
  :hints (("Goal" :use (:instance linearsearch-while-lemma1 (n (lookup (cadr i) vars))
				                            (l (lookup (cadr lst) vars))))))

(defthm linearsearch-while-lemma2
  (let ((ival (lookup (param1 i) vars))
	(xval (lookup (param1 x) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (okp stat)
		  (varp i)
		  (equal ival 0)
		  (varp lst)
		  (true-listp lstval)
		  lstval
		  (varp x)
		  (not (equal (param1 x) (param1 i)))
		  xval
		  (not (equal (param1 lst) (param1 i)))
		  (natp steps)
		  (integerp count)
		  (not (timedoutp (run-status (run (linearsearch-while i x lst) stat vars steps count))))
		  (member-equal xval lstval)
		  )
	     (equal (run (linearsearch-while i x lst) stat vars steps count)
		    (let ((index (first-after ival xval lstval)))
		      (mv 'returned
			  (store 'result index
				 (store (param1 i)
					index
					vars))
			  (+ 13 (* 15 (- index ival)) steps))))))
  :hints (("Goal" :use (:instance linearsearch-while-lemma1 (n (lookup (cadr i) vars))
				                            (l (lookup (cadr lst) vars)))
	          :in-theory (enable linearsearch-while-lemma-final))))

(defthm linearsearch-while-lemma3
  (let ((ival (lookup (param1 i) vars))
	(xval (lookup (param1 x) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (okp stat)
		  (varp i)
		  (equal ival 0)
		  (varp lst)
		  (true-listp lstval)
		  lstval
		  ;(not (equal (param1 lst) 'result))
		  (varp x)
		  (not (equal (param1 x) (param1 i)))
		  xval
		  (not (equal (param1 lst) (param1 i)))
		  (natp steps)
		  (integerp count)
		  (not (timedoutp (run-status (run (linearsearch-while i x lst) stat vars steps count))))
		  (not (member-equal xval lstval))
		  )
	     (equal (run (linearsearch-while i x lst) stat vars steps count)
		    (mv stat
			(store (param1 i) (len lstval) vars)
			(+ 5 (* (- (len lstval) ival) 15) steps)))))
  :hints (("Goal" :in-theory (enable linearsearch-while-lemma-final))))

(in-theory (disable linearsearch))

(defthm linearsearch-expander
  (implies (and (okp stat)
		(not (zp count))
		(varp i)
		(natp steps)
		)
	   (equal (run (linearsearch i x lst) stat vars steps count)
		  ;; If the while returns with OK, then the while breaks
		  ;; to the (return -1) statement. 
		  (if (okp (mv-nth 0 (run (linearsearch-while i x lst)
					  'ok
					  (store (cadr i) 0 vars)
					  (+ 2 steps)
					  count)))
		      (list 'returned
			    (store 'result
				   -1
				   (mv-nth 1
					   (run (linearsearch-while i x lst)
						'ok
						(store (cadr i) 0 vars)
						(+ 2 steps)
						count)))
			    (+ 2 (mv-nth 2
					 (run (linearsearch-while i x lst)
					      'ok
					      (store (cadr i) 0 vars)
					      (+ 2 steps)
					      count))))
		    (run (linearsearch-while i x lst)
			 'ok
			 (store (cadr i) 0 vars)
			 (+ 2 steps)
			 count))))
  :hints (("Goal" :in-theory (enable linearsearch run-splitter))))

(defthm linearsearch-correct
  (let ((xval (lookup (param1 x) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (okp stat)
		  (varp i)
		  (varp lst)
		  (true-listp lstval)
		  lstval
		  ;(not (equal (param1 lst) 'result))
		  (varp x)
		  (not (equal (param1 x) (param1 i)))
		  xval
		  (not (equal (param1 lst) (param1 i)))
		  (integerp count)
		  (not (timedoutp (run-status (run (linearsearch i x lst) stat vars 0 count))))
		  )
	     (equal (run (linearsearch i x lst) stat vars 0 count)
		    (if (member-equal xval lstval)
			(mv 'returned
			    (store 'result
				   (first-after 0 (lookup (cadr x) vars)
						(lookup (cadr lst) vars))
				   (store (cadr i)
					  (first-after 0 (lookup (cadr x) vars)
						       (lookup (cadr lst) vars))
					  vars))
			    (+ 15
			       (* 15
				  (first-after 0 (lookup (cadr x) vars)
					       (lookup (cadr lst) vars)))))
		      (mv 'returned
			  (store 'result
				 -1
				 (store (cadr i) (len lstval) vars))
			  (+ 9 (* 15 (len lstval))))))))
  :hints (("Goal" :INSTRUCTIONS
	          (:EXPAND 
			   :PROMOTE (:CLAIM (NOT (ZP COUNT)))
			   (:CASESPLIT (MEMBER-EQUAL (LOOKUP (CADR X) VARS)
						     (LOOKUP (CADR LST) VARS)))
			   :BASH :BASH))))

(defthm linearsearch-correct-value-corollary
  (let ((xval (lookup (param1 x) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (okp stat)
		  (varp i)
		  (varp lst)
		  (true-listp lstval)
		  lstval
		  ;(not (equal (param1 lst) 'result))
		  (varp x)
		  (not (equal (param1 x) (param1 i)))
		  xval
		  (not (equal (param1 lst) (param1 i)))
		  (integerp count)
		  (not (timedoutp (run-status (run (linearsearch i x lst) stat vars 0 count))))
		  )
	     (equal (lookup 'result (run-vars (run (linearsearch i x lst) stat vars 0 count)))
		    (if (member-equal xval lstval)
			(first-after 0 xval lstval)
		      -1))))
  :hints (("Goal" :instructions (:expand :promote (:dive 1 2 2)
					 (:rewrite linearsearch-correct)
					 :top :s))))

(defthm linearsearch-correct-steps-corollary
  (let ((xval (lookup (param1 x) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (okp stat)
		  (varp i)
		  (varp lst)
		  (true-listp lstval)
		  lstval
		  (varp x)
		  (not (equal (param1 x) (param1 i)))
		  xval
		  (not (equal (param1 lst) (param1 i)))
		  (integerp count)
		  (not (timedoutp (run-status (run (linearsearch i x lst) stat vars 0 count))))
		  )
	     (equal (run-steps (run (linearsearch i x lst) stat vars 0 count))
		    (if (member-equal xval lstval)
			(+ 15 (* 15 (first-after 0 xval lstval)))
		      (+ 9 (* 15 (len lstval)))))))
  :hints (("Goal" :instructions (:expand :promote (:dive 1 2)
					 (:rewrite linearsearch-correct)
					 :top :s))))

(defun linearsearch2 (x lst)
  ;; This version just introduces i without
  ;; parameterizing it. 
  (linearsearch '(var i) x lst))

(in-theory (disable linearsearch))

(defthm linearsearch2-correct-value-corollary
  (let ((xval (lookup (param1 x) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (varp lst)
		  (true-listp lstval)
		  lstval
		  (varp x)
		  (not (equal (param1 x) 'i))
		  xval
		  (not (equal (param1 lst) 'i))
		  (integerp count)
		  (not (timedoutp (run-status (run (linearsearch2 x lst) 'ok vars 0 count))))
		  )
	     (equal (lookup 'result (run-vars (run (linearsearch2 x lst) 'ok vars 0 count)))
		    (if (member-equal xval lstval)
			(first-after 0 xval lstval)
		      -1)))))

(defthm linearsearch2-correct-steps-corollary
  ;; This characterizes how many steps linearsearch2 takes,
  ;; in the two cases of key found and key not found. 
  (let ((xval (lookup (param1 x) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (varp lst)
		  (true-listp lstval)
		  lstval
		  ;(not (equal (param1 lst) 'result))
		  (varp x)
		  (not (equal (param1 x) 'i))
		  xval
		  (not (equal (param1 lst) 'i))
		  (integerp count)
		  (not (timedoutp (run-status (run (linearsearch2 x lst) 'ok vars 0 count))))
		  )
	     (equal (run-steps (run (linearsearch2 x lst) 'ok vars 0 count))
		    (if (member-equal xval lstval)
			(+ 15 (* 15 (first-after 0 xval lstval)))
		      (+ 9 (* 15 (len lstval))))))))


;;  COMPLEXITY OF LINEARSEARCH               

; For a given function g(n), we denote by O(g(n)) the set of
; functions:
; 
; O(g(n)) = {f(n): there exist positive constants c and n0 such
; that 0 <= f(n) <= c*g(n), for all n >= n0}.
; 
; We often write f(n) = O(g(n)) to mean f(n) element of O(g(n)).
; 
; We often write O(f(n)) = O(g(n)) to mean O(f(n)) \subseteq O(g(n)).
; 
; If f(n) = O(g(n)), then f(n) is \textitbf{asymptotically upper
; bounded} by g(n).  Think, f(n) ``is no larger than'' g(n).


;; A function f(n) is O(n) if there exist constants c and n0 such that
;;   0 <= f(n) <= c*n, for all n >= n0.

;; Want to prove that (linearsearch) is linear. 

;; There exist positive integers c and n0, such that
;;    for all n >= n, 0 <= f(n) <= c * n
;; 
;; where f(n) is (run-steps (run (linearsearch2 x lst) 'ok vars 0 count))

(defun-sk function-linear1 (program linear-in c n0 vars count)
  ;; This says that program (which is just a literal) can be run
  ;; against the variable-alist vars with count.  It says that 
  ;; the number of steps taken to run the program is linear 
  ;; in the size of parameter linear-in.  Params c and n0 are the two
  ;; variables in the definition of asymptotic complexity.
  (forall (n)
	  (implies (and (equal n (len linear-in))
			(<= n0 n))
		   (mv-let (run-stat run-vars run-steps)
			   (run program 'ok vars 0 count)
			   (declare (ignore run-stat run-vars))
			   (and (<= 0 run-steps)
				(<= run-steps (* c n)))))))

(defun-sk function-linear2 (program linear-in vars count)
  ;; Since the definition of Big-O has nested quantifiers, in ACL2
  ;; we have to have two separate defun-sk events to capture it.  This
  ;; is the top-level function. 
  (exists (c n0)
	  (and (posp c)
	       (posp n0)
	       (function-linear1 program linear-in c n0 vars count))))

(defun linearsearch2-linear (vars count)
  ;; This asserts that linearsearch2 is linear in the length of the
  ;; list, if the key and lst are placed in specific variables.
  (function-linear2 (linearsearch2 '(var key) '(var lst))
		    (lookup 'lst vars)
		    vars
		    count))

(defthm linearsearch2-linear-proof
  (let ((xval (lookup 'key vars))
	(lstval (lookup 'lst vars)))
    (implies (and (true-listp lstval)
		  lstval
		  xval
		  (integerp count)
		  (not (timedoutp (run-status (run (linearsearch2 '(var key) '(var lst)) 'ok vars 0 count))))
		  )
	     (linearsearch2-linear vars count)))
   :instructions (:expand :promote (:rewrite linearsearch2-linear)
                        (:rewrite function-linear2-suff ((c (+ 9 15)) (n0 1)))
                        (:in-theory (disable linearsearch2 (linearsearch2)))
                        :s :bash))

(in-theory (disable linearsearch-if-else-lemma2 run-ls-while-expander4
		    linearsearch-while-lemma0 linearsearch-while-lemma1
		    linearsearch-while-lemma-final linearsearch-while-lemma2
		    linearsearch-while-lemma3 linearsearch-expander linearsearch-correct
		    linearsearch-correct-value-corollary
		    linearsearch-correct-steps-corollary
		    linearsearch2-correct-value-corollary
		    linearsearch2-correct-steps-corollary linearsearch2-linear-proof))

