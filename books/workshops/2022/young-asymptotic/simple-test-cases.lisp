; simple-test-cases.lisp                     William D. Young

(in-package "ACL2")
(include-book "asymptotic-analysis-support")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                  ;;
;;                         SOME TEST CASES                          ;;
;;                                                                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This contains some very simple test cases to investigate how the
;; asymptotic analysis support stuff is used. 

;; TESTPROG1
;; Simple first program with an assign and return:

(defun testprog1 (i)
  ;; A first, very simple program
  `(seq (assign ,i (lit . 10))
	(return ,i)))

(defthm testprog1-correct
  (implies (and (okp stat)
		(varp i)
		(not (zp count)))
	   (equal (lookup 'result (run-vars  (run (testprog1 i) stat vars steps count)))
		  10)))

(defthm testprog1-steps
  (implies (and (okp stat)
		(varp i)
		(not (zp count)))
	   (equal (run-steps  (run (testprog1 i) stat vars steps count))
		  (+ steps 4))))

;; TESTPROG2
;; Generalize testprog1 to add a variable:

(defun testprog2 (i exp)
  `(seq (assign ,i ,exp)
	(return ,i)))

(defthm testprog2-correct
  (implies (and (okp stat)
		(varp i)
		(not (zp count)))
	   (equal (run (testprog2 i exp) stat vars steps count)
		  (if (mv-nth 0 (exeval exp t vars))
		      (list 'returned
			    (store 'result
				   (mv-nth 1 (exeval exp t vars))
				   (store (cadr i)
					  (mv-nth 1 (exeval exp t vars))
					  vars))
			    (+ 3 steps (mv-nth 2 (exeval exp t vars))))
		    (run-error vars)))))

(defthm testprog2-correct2
  ;; Running testprog2 gives the following results:
  ;; 1. the variable 'result contains the evaluation of exp
  ;; 2. it took the number of steps to evaluate exp + 3 total steps.
  (implies (and (okp stat)
		(varp i)
		(mv-nth 0 (exeval exp t vars))
		(not (zp count)))
	   (and (equal (lookup 'result (run-vars (run (testprog2 i exp) stat vars 0 count)))
		       (exeval-value (exeval exp t vars)))
		(equal (run-steps (run (testprog2 i exp) stat vars 0 count))
		       (+ 3 (exeval-steps (exeval exp t vars)))))))

(in-theory (disable testprog2-correct testprog2-correct2))

;; FINDMIN
;; Simple program to compute the minimum of two expressions.

; if (x < y):
;    return x
; else:
;    return y

;; I'm currently assuming that x and y are variables.  Can
;; we generalize this to other expressions

(defun findmin (x y)
  `(if-else (< ,x ,y)
	    (return ,x)
	    (return ,y)))

;; >>> Notice that this shows that the analysis is naive.  For example, 
;;     (if (< x y) x y) evaluates x (or y) twice.  A compiler wouldn't do
;;     that. 

(defthm findmin-correct
  (implies (and (okp stat)
		(not (zp count)))
	   (equal (run (findmin x y) stat vars steps count)
		  (if (and (exeval-status (exeval x t vars))
			   (exeval-status (exeval y t vars))
			   (acl2-numberp (exeval-value (exeval x t vars)))
			   (acl2-numberp (exeval-value (exeval y t vars))))
		      ;; Does the test succeed?
		      (if (< (exeval-value (exeval x t vars))
			     (exeval-value (exeval y t vars)))
			  (list 'returned
				(store 'result
				       (mv-nth 1 (exeval x t vars))
				       vars)
				(+ 3 steps
				   (exeval-steps (exeval x t vars))
				   (exeval-steps (exeval x t vars))
				   (exeval-steps (exeval y t vars))))
			(list 'returned
			      (store 'result
				     (mv-nth 1 (exeval y t vars))
				     vars)
			      (+ 3 steps
				 (exeval-steps (exeval x t vars))
				 (exeval-steps (exeval y t vars))
				 (exeval-steps (exeval y t vars)))))
		    (run-error vars)))))

(defthm findmin-correct2
  (implies (and (okp stat)
		;; evaluating the test didn't raise an error
		(exeval-status (exeval (list '< x y) t vars))
		(not (zp count)))
	   (and (equal (lookup 'result (run-vars (run (findmin x y) stat vars steps count)))
		       (min (exeval-value (exeval x t vars))
			    (exeval-value (exeval y t vars))))
		(equal (run-steps (run (findmin x y) stat vars steps count))
		       (if (< (exeval-value (exeval x t vars))
			     (exeval-value (exeval y t vars)))
			   (+ 3 steps
				   (exeval-steps (exeval x t vars))
				   (exeval-steps (exeval x t vars))
				   (exeval-steps (exeval y t vars)))
			 (+ 3 steps
				   (exeval-steps (exeval x t vars))
				   (exeval-steps (exeval y t vars))
				   (exeval-steps (exeval y t vars))))))))
			   
(in-theory (disable findmin-correct findmin-correct2))

;; COUNTDOWN
;; Simple program involving a while statement:

;; Note that the test takes 4 steps and the assign takes 4 steps:

(defun countdown (i)
  `(while (< (lit . 0) ,i)
     (assign ,i (- ,i (lit . 1)))))

(set-irrelevant-formals-ok t)

(defun countdown-ind (n i vars steps count)
  (if (zp n)
      t
    (countdown-ind (1- n)
		   i
		   (store (param1 i) (1- n) vars)
		   (+ 8 steps)
		   (1- count))))

(defthm countdown-correct
  (implies (and (okp stat)
		(varp i)
		(equal n (lookup (param1 i) vars))
		(integerp n)
		(natp steps)
		(not (zp count))
		(< n count)
		)
	   (equal (run (countdown i) stat vars steps count)
		  (mv 'ok
			(store (param1 i) (if (>= n 0) 0 n) vars)
			(if (> n 0)
			    (+ (* n 8) 4 steps)
			  (+ 4 steps)))))
  :hints (("Goal" :induct (countdown-ind n i vars steps count))))

(defthm countdown-correct-corollary
  (let ((n (lookup (param1 i) vars)))
    (implies (and (okp stat)
		  (varp i)
		  (integerp n)
		  (< n count)
		  (not (zp count))
		  )
	     (equal (run (countdown i) stat vars 0 count)
		    (mv 'ok
			(store (param1 i) (if (>= n 0) 0 n) vars)
			(if (> n 0)
			    (+ (* n 8) 4)
			  4)))))
  :hints (("Goal" :use (:instance countdown-correct (n (lookup (param1 i) vars))
				                    (steps 0)))))

(in-theory (disable countdown-correct countdown-correct-corollary))

