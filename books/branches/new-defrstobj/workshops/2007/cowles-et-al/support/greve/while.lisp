#|==================================================================|#
#|                                                                  |#
#| Copyright © 2005-7 Rockwell Collins, Inc.  All Rights Reserved.  |#
#|                                                                  |#
#|==================================================================|#
;;
;; Following is a possible solution to Bill Young's challenge problem
;; using "defminterm"
#|
Sent by: owner-acl2-help@lists.cc.utexas.edu 06/22/2007 05:31 PM

Subject: would DEFPUN work here?
	
Hi All,

I would like to define an interpreter for a simple language such as 
below.  Clearly ACL2 won't accept this because
of the clause for the statement (while e c).  My question: is this the 
type of function I could define using a DEFPUN.  I
haven't used them enough to have a sense whether they're appropriate 
here.  The other, much less desirable
alternative is to add a clock arg.    Everything is acceptable if I 
leave out the while clause.

Bill

(defun run (stmt mem)
  (case (op stmt)
    (skip     (run-skip stmt mem))
    (assign   (run-assignment stmt mem))
    (if       (if (zerop (evaluate (arg1 stmt) mem))
              (run (arg3 stmt) mem)
            (run (arg3 stmt) mem)))
    (while    (if (zerop (evaluate (arg1 stmt) mem))
              mem
            (run stmt
             (run (arg2 stmt) mem))))
    (sequence (run (arg2 stmt)
               (run (arg1 stmt) mem)))
    (otherwise mem)))
 
|#

(in-package "ACL2")
(include-book "defminterm")
(include-book "ack")

(defstub run-skip (stmt mem) nil)
(defstub run-assignment (stmt mem) nil)
(defstub evaluate (value mem) nil)
(defstub op   (stmt) nil)
(defstub arg1 (stmt) nil)
(defstub arg2 (stmt) nil)
(defstub arg3 (stmt) nil)

;; Define a tail recursive version of run w/stack

(defun base (stmt mem)
  (case (op stmt)
    (skip t)
    (assign t)
    (if nil)
    (while (zerop (evaluate (arg1 stmt) mem)))
    (sequence nil)
    (otherwise t)))
      
(defun base-computation (stmt mem)
  (case (op stmt)
    (skip (run-skip stmt mem))
    (assign (run-assignment stmt mem))
    (while  mem)
    (otherwise mem)))

(defminterm run-stk (stmt mem stk)
  (if (and (base stmt mem) (not (consp stk)))
      (base-computation stmt mem)
    (if (base stmt mem)
	(let ((mem (base-computation stmt mem)))
	  (run-stk (car stk) mem (cdr stk)))
      (case (op stmt)
	(if       (if (zerop (evaluate (arg1 stmt) mem))
		      (run-stk (arg2 stmt) mem stk)
		    (run-stk (arg3 stmt) mem stk)))
	(while    (run-stk (arg2 stmt) mem (cons stmt stk)))
	(sequence (run-stk (arg1 stmt) mem (cons (arg2 stmt) stk)))))))

(defun run-stk_induction (stmt mem stk zed)
  (declare (xargs :measure (run-stk_measure stmt mem stk)))
  (if (run-stk_terminates stmt mem stk)
      (if (and (base stmt mem) (not (consp stk)))
	  (base-computation stmt mem)
	(if (base stmt mem)
	    (let ((mem (base-computation stmt mem)))
	      (run-stk_induction (car stk) mem (cdr stk) (cdr zed)))
	  (case (op stmt)
	    (if       (if (zerop (evaluate (arg1 stmt) mem))
			  (run-stk_induction (arg2 stmt) mem stk zed)
			(run-stk_induction (arg3 stmt) mem stk zed)))
	    (while    (run-stk_induction (arg2 stmt) mem (cons stmt stk) (cons stmt zed)))
	    (sequence (run-stk_induction (arg1 stmt) mem (cons (arg2 stmt) stk) (cons (arg2 stmt) zed))))))
    (list stk zed)))

(defthm run-stk_terminates_from_run-stk_terminates
  (implies (and (run-stk_terminates x y s)
                (head-equal r s)
                (<= (len r) (len s)))
           (run-stk_terminates x y r))
  :hints (("goal" :do-not '(generalize eliminate-destructors)
	   :induct (run-stk_induction x y s r))))

(encapsulate
    ()

  (local
   (encapsulate
       ()

     (defthm run-stk_terminates_list_equal
       (implies (and (run-stk_terminates x y s)
                     (list-equal r s))
                (run-stk_terminates x y r)))
     
     (defthm not_run-stk_terminates_list_equal
       (implies (and (not (run-stk_terminates x y r))
                     (list-equal r s))
                (not (run-stk_terminates x y s))))

     ))
     
  (defcong list-equal iff (run-stk_terminates x y r) 3)
  
  )

(defthm run-stk_terminates_nil
  (implies (and (run-stk_terminates x y s)
                (syntaxp (not (quotep s))))
           (run-stk_terminates x y nil))
  :rule-classes (:forward-chaining))

(defcong list-equal equal (run-stk x y r) 3
  :hints (("goal" :induct (run-stk_induction x y r r-equiv))))

(defthm run-stk_termiantes_on_run-stk
  (implies
   (and
    (consp r)
    (run-stk_terminates x y (append s r)))
   (run-stk_terminates (car r) (run-stk x y s) (cdr r)))
  :hints (("goal" :do-not '(generalize eliminate-destructors)
	   :do-not-induct t
	   :in-theory (enable OPEN_RUN-STK_TERMINATES_stk)
	   :induct (run-stk x y s))))


;; Obviously the defminterm library is deficient here.  The problem is
;; that the stack is growing on some recursive calls. This causes the
;; base test to fail and results in ACL2 wanting to open up the
;; function even more.  To fix this, I have defined a new opener for
;; "_terminates" and then, in the theorem below, I restrict the
;; application of the original opener (the first time I have ever done
;; that!)
;; 

(DEFTHM OPEN_RUN-STK_MEASURE_check
  (IMPLIES
   (syntaxp (and (symbolp stmt) (symbolp mem) (symbolp stk)))
   (implies
    (RUN-STK_TERMINATES STMT MEM STK)
    (AND
     (IMPLIES
      (NOT (RUN-STKTEST_BODY STMT MEM STK))
      (EQUAL
       (RUN-STK_MEASURE STMT MEM STK)
       (LET
	((STMT (CAR (RUN-STKSTEP_BODY_1 (LIST STMT MEM STK))))
	 (MEM
	  (CAR (CDR (RUN-STKSTEP_BODY_1 (LIST STMT MEM STK)))))
	 (STK
	  (CAR
	   (CDR
	    (CDR (RUN-STKSTEP_BODY_1 (LIST STMT MEM STK)))))))
	(+ 1 (RUN-STK_MEASURE STMT MEM STK)))))
     (IMPLIES (RUN-STKTEST_BODY STMT MEM STK)
	      (EQUAL (RUN-STK_MEASURE STMT MEM STK)
		     (O)))))))
   
(defthm run-stk_measure_on_run-stk
  (implies
   (and
    (consp r)
    (run-stk_terminates x y (append s r)))
   (equal (run-stk_measure x y (append s r))
	  (+ (run-stk_measure x y s)
	     (run-stk_measure (car r) (run-stk x y s) (cdr r)))))
  :rule-classes nil
  :hints (("goal" :do-not '(eliminate-destructors generalize)
	   :do-not-induct t
	   :in-theory (enable OPEN_RUN-STK_TERMINATES_STK)
	   :restrict ((OPEN_RUN-STK_MEASURE ((stk (append s r)))))
	   :induct (run-stk x y s))))

(defthm run-stk_measure_reduction
  (implies
   (run-stk_terminates x y (cons a r))
   (equal (run-stk_measure x y (cons a r))
	  (+ (run-stk_measure x y nil)
	     (run-stk_measure a (run-stk x y nil) r))))
  :hints (("goal" :in-theory (disable OPEN_RUN-STK_MEASURE)
	   :use (:instance run-stk_measure_on_run-stk
			   (s nil)
			   (r (cons a r))))))

(defthm run-stk_on_run-stk
  (implies
   (and
    (consp r)
    (run-stk_terminates x y (append s r)))
   (equal (run-stk x y (append s r))
	  (run-stk (car r) (run-stk x y s) (cdr r))))
  :rule-classes nil
  :hints (("goal" :in-theory (enable open_run-stk_terminates_stk)
	   :induct (run-stk x y s))))

(defthm run-stk_reduction
  (implies
   (run-stk_terminates x y (cons a r))
   (equal (run-stk x y (cons a r))
	  (run-stk a (run-stk x y nil) r)))
  :hints (("goal" :use (:instance run-stk_on_run-stk
				  (s nil)
				  (r (cons a r))))))
(defun run (x y)
  (run-stk x y nil))

(defun run_terminates (x y)
  (run-stk_terminates x y nil))

(defun run_measure (x y)
  (run-stk_measure x y nil))

;;
;; Here is our final product.
;;
;; If we had made the defminterm above executable (by giving
;; executable bodies to the encapsulated functions and adding guards),
;; this function (run) could be executable as well.

(defthm run_spec
  (equal (run stmt mem)
	 (if (run_terminates stmt mem)
	     (case (op stmt)
	       (skip     (run-skip stmt mem))
	       (assign   (run-assignment stmt mem))
	       (if       (if (zerop (evaluate (arg1 stmt) mem))
			     (run (arg2 stmt) mem)
			   (run (arg3 stmt) mem)))
	       (while    (if (zerop (evaluate (arg1 stmt) mem))
			     mem
			   (run stmt
				(run (arg2 stmt) mem))))
	       (sequence (run (arg2 stmt)
			      (run (arg1 stmt) mem)))
	       (otherwise mem))
	   mem))
  :rule-classes nil)

(defthm run_measure_spec
  (implies
   (run_terminates stmt mem)
   (equal (run_measure stmt mem)
	  (case (op stmt)
	    (skip     (O))
	    (assign   (O))
	    (if       (+ 1 (if (zerop (evaluate (arg1 stmt) mem))
			       (run_measure (arg2 stmt) mem)
			     (run_measure (arg3 stmt) mem))))
	    (while    (if (zerop (evaluate (arg1 stmt) mem))
			  (O)
			(+ 1 (run_measure (arg2 stmt) mem)
			   (run_measure stmt 
					(run (arg2 stmt) mem)))))
	    (sequence (+ 1 (run_measure (arg1 stmt) mem)
			 (run_measure (arg2 stmt)
				      (run (arg1 stmt) mem))))
	    (otherwise (O))))))
