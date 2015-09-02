; Contributed by John Cowles, July, 2007.

;ACL2 While Language Interpreter book
;; This book provides an answer to a challenge from Bill Young: to define
;; a total function that is an interpreter for a programming language
;; with while loops. (The solution is necessarily not computable: no
;; solution to the halting problem here!)
; Copyright (C) 2007  John R. Cowles, University of Wyoming

; This book is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This book is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this book; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:
; John Cowles
; Department of Computer Science
; University of Wyoming
; Laramie, WY 82071  U.S.A.

; Last modified July 2007.

(in-package "ACL2")

(include-book "arithmetic/top-with-meta" :dir :system)

#|
To certify this book:

(certify-book "while-loop-alt"
	      0
              nil   ;;compile-flg
	      )
|#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Bill Young's challenge:
;;    Construct an ACL2 function that satisfies

;; (equal run (stmt mem)
;;        (case (op stmt)
;;              (skip     (run-skip stmt mem))
;;              (assign   (run-assignment stmt mem))
;;              (if       (if (zerop (evaluate (arg1 stmt) mem))
;;                            (run (arg3 stmt) mem)
;;                            (run (arg2 stmt) mem)))
;;              (while    (if (zerop (evaluate (arg1 stmt) mem))
;;                            mem
;;                            (run stmt (run (arg2 stmt) mem))))
;;              (sequence (run (arg2 stmt)(run (arg1 stmt) mem)))
;;              (otherwise mem)))

;; stmt
;;   (skip)
;;   (assign var expr)
;;   (if exp stmt1 stmt2)
;;   (while exp stmt1)
;;   (sequence stmt1 stmt2)

;; This book constructs an ACL2 function that satisfies

;; (equal (run stmt mem)
;;        (if (null mem)
;;            nil
;;            (case (op stmt)
;;                  (skip      mem)
;;                  (assign    (run-assignment stmt mem))
;;                  (sequence  (run (arg2 stmt)(run (arg1 stmt) mem)))
;;                  (if        (if (zerop (eval-expr (arg1 stmt) mem))
;;                                 (run (arg3 stmt) mem)
;;                                 (run (arg2 stmt) mem)))
;;                  (while     (if (zerop (eval-expr (arg1 stmt) mem))
;;                                  mem
;;                                  (run stmt (run (arg2 stmt) mem))))
;;                  (otherwise mem))))

;; Start with some of Bill's defs

(defun
  op (stmt)
  (first stmt))

(defun
  arg1 (stmt)
  (second stmt))

(defun
  arg2 (stmt)
  (third stmt))

(defun
  arg3 (stmt)
  (fourth stmt))

(defmacro
  val (key alist)
  `(cdr (assoc-equal ,key ,alist)))

(defmacro
  tlistp (x n)
  `(and (true-listp ,x)
	(equal (len ,x) ,n)))

(defun
  definedp (x alist)
  (if (endp alist)
      nil
      (if (equal x (caar alist))
	  t
	  (definedp x (cdr alist)))))

(defun
  varp (x alist)
  (and (symbolp x)
       (definedp x alist)))

(defun
  exprp (x alist)
  (or (integerp x)
      (varp x alist)))

(defun
  eval-expr (expr alist)
  (if (integerp expr)
      expr
      (val expr alist)))

;; An assignment statement has form: (assign var expr)

(defun run-assignment (stmt alist)
  (let* ((v (arg1 stmt))
	 (e (arg2 stmt))
	 (val (eval-expr e alist)))
        (put-assoc-equal v val alist)))

;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Here are John C's defs:

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; stmt
;;   (skip)
;;   (assign var expr)
;;   (sequence stmt1 stmt2)
;;   (if exp stmt1 stmt2)
;;   (while exp stmt1)

;; Booleans
;;   0 represents false
;;   Any value other than 0 represents true

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; In this model, termination is guaranteed by limiting the maximum number of
;; recursive calls that can be made.

(defun
  run-limit (stmt mem limit)
  "Return (mv new-mem new-limit) when run-limit terminates.
   Here new-mem is the memory and new-limit is the number
   of recursive calls remaining, when run-limit terminates.

   The inputs: stmt  is a statement of the while-language,
               mem   is state of the memory, and
               limit is the maximum number of recursive
                     calls that can be made.

   A value of new-mem equal to nil means that stmt did not
   terminate with the given limit."
  (declare (xargs :measure (nfix limit)))
  (let ((limit (nfix limit)))
       (if (null mem)
	   (mv nil limit)
	   (case (op stmt)
		 (skip      (mv mem limit))
		 (assign    (mv (run-assignment stmt mem) limit))
		 (sequence  (if (zp limit)
				(mv nil 0)
			        (mv-let (mem1 limit1)
					(run-limit (arg1 stmt) mem (- limit 1))
					(if (>= limit1 limit) ;; ALWAYS FALSE
					    (mv nil limit1)
					    (if (zp limit1)
						(mv nil 0)
					        (run-limit (arg2 stmt)
							   mem1
							   (- limit1 1)))))))
		 (if        (if (zp limit)
				(mv nil 0)
			        (if (zerop (eval-expr (arg1 stmt) mem))
				    (run-limit (arg3 stmt) mem (- limit 1))
				    (run-limit (arg2 stmt) mem (- limit 1)))))
		 (while     (if (zerop (eval-expr (arg1 stmt) mem))
				(mv mem limit)
			        (if (zp limit)
				    (mv nil 0)
				    (mv-let (mem1 limit1)
					    (run-limit (arg2 stmt) mem (- limit 1))
					    (if (>= limit1 limit) ;; ALWAYS FALSE
						(mv nil limit1)
					        (if (zp limit1)
						    (mv nil 0)
						    (run-limit stmt
							       mem1
							       (- limit1 1))))))))
		 (otherwise (mv mem limit))))))

(in-theory (disable (:definition eval-expr)
		    (:definition run-assignment)))

(defthm
  Natp-mv-nth-1-run-limit
  (natp (mv-nth 1 (run-limit stmt mem limit)))
  :rule-classes :type-prescription)

(defthm
  Mv-nth-1-run-limit-<=-limit
  (<= (mv-nth 1 (run-limit stmt mem limit))(nfix limit))
  :rule-classes :linear)

(defthm
  Run-limit-simpler-definition
  (equal (run-limit stmt mem limit)
	 (let ((limit (nfix limit)))
	   (if (null mem)
	       (mv nil limit)
	       (case (op stmt)
		     (skip      (mv mem limit))
		     (assign    (mv (run-assignment stmt mem) limit))
		     (sequence  (if (zp limit)
				(mv nil 0)
			        (mv-let (mem1 limit1)
					(run-limit (arg1 stmt) mem (- limit 1))
					(if (zp limit1)
					    (mv nil 0)
					    (run-limit (arg2 stmt)
						       mem1
						       (- limit1 1))))))
		     (if        (if (zp limit)
				    (mv nil 0)
				    (if (zerop (eval-expr (arg1 stmt) mem))
					(run-limit (arg3 stmt) mem (- limit 1))
				        (run-limit (arg2 stmt) mem (- limit 1)))))
		     (while     (if (zerop (eval-expr (arg1 stmt) mem))
				    (mv mem limit)
				    (if (zp limit)
					(mv nil 0)
				        (mv-let (mem1 limit1)
						(run-limit (arg2 stmt)
							   mem
							   (- limit 1))
						(if (zp limit1)
						    (mv nil 0)
						    (run-limit stmt
							       mem1
							       (- limit1 1)))))))
		     (otherwise (mv mem limit))))))
  :rule-classes nil)

(defun
  induct-hint (stmt mem i j)
  (declare (xargs :measure (+ (nfix i)(nfix j))))
  (if (null mem)
      t
      (case (op stmt)
	    (skip      t)
	    (assign    t)
	    (sequence  (if (or (zp i)(zp j))
			   t
			   (and (induct-hint (arg1 stmt) mem (- i 1)(- j 1))
				(mv-let (memi i1)
					(run-limit (arg1 stmt) mem (- i 1))
					(mv-let (memj j1)
						(run-limit (arg1 stmt)
							   mem
							   (- j 1))
						(declare (ignore memj))
						(if (or (zp i1)(zp j1))
						    t
						    (induct-hint (arg2 stmt)
								 memi
								 (- i1 1)
								 (- j1 1))))))))
	    (if        (if (or (zp i)(zp j))
			   t
			   (if (zerop (eval-expr (arg1 stmt) mem))
			       (induct-hint (arg3 stmt) mem (- i 1)(- j 1))
			       (induct-hint (arg2 stmt) mem (- i 1)(- j 1)))))
	    (while     (cond ((zerop (eval-expr (arg1 stmt) mem))
			      t)
			     ((or (zp i)(zp j))
			      t)
			     (t (and (induct-hint (arg2 stmt)
						  mem
						  (- i 1)
						  (- j 1))
				     (mv-let (memi i1)
					     (run-limit (arg2 stmt)
							mem
							(- i 1))
					     (mv-let (memj j1)
						     (run-limit (arg2 stmt)
								mem
								(- j 1))
						     (declare (ignore memj))
						     (if (or (zp i1)(zp j1))
							 t
						       (induct-hint stmt
								    memi
								    (- i1 1)
								    (- j1 1)))))))))
	    (otherwise t))))

(defthm
  Termination-implies-same-result
  (implies (and (mv-nth 0 (run-limit stmt mem i))
		(mv-nth 0 (run-limit stmt mem j)))
	   (equal (mv-nth 0 (run-limit stmt mem i))
		  (mv-nth 0 (run-limit stmt mem j))))
  :rule-classes nil
  :hints (("Goal"
	   :induct (induct-hint stmt mem i j))))

(defthm
  While-termination-implies-body-termination
  (implies (and (mv-nth 0 (run-limit stmt mem i))
		(equal (car stmt) 'while)
		(not (equal (eval-expr (cadr stmt) mem) 0)))
	   (mv-nth 0 (run-limit (caddr stmt) mem (+ -1 i))))
  :rule-classes nil)

(defthm
  Sequence-termination-implies-first-stmt-termination
  (implies (and (mv-nth 0 (run-limit stmt mem i))
		(equal (car stmt) 'sequence))
	   (mv-nth 0 (run-limit (cadr stmt) mem (+ -1 i))))
  :rule-classes nil)

(defthm
  Termination-implies-same-nbr-recursive-calls
  (implies (and (mv-nth 0 (run-limit stmt mem i))
		(mv-nth 0 (run-limit stmt mem j))
		(natp i)
		(natp j))
	   (equal (- i (mv-nth 1 (run-limit stmt mem i)))
		  (- j (mv-nth 1 (run-limit stmt mem j)))))
  :rule-classes nil
  :hints (("Goal"
	   :induct (induct-hint stmt mem i j))
	  ("Subgoal *1/14"
	   :use (While-termination-implies-body-termination
		 (:instance
		  While-termination-implies-body-termination
		  (i j))
		 (:instance
		  Termination-implies-same-result
		  (stmt (caddr stmt))
		  (i (+ -1 i))
		  (j (+ -1 j)))))
	  ("Subgoal *1/6"
	   :use (Sequence-termination-implies-first-stmt-termination
		 (:instance
		  Sequence-termination-implies-first-stmt-termination
		  (i j))
		 (:instance
		  Termination-implies-same-result
		  (stmt (cadr stmt))
		  (i (+ -1 i))
		  (j (+ -1 j)))))))

(defthm
  Termination-implies-bigger-limit-termination
  (implies (and (mv-nth 0 (run-limit stmt mem i))
		(integerp j)
		(>= j i))
	   (mv-nth 0 (run-limit stmt mem j)))
  :rule-classes nil
  :hints (("Goal"
	   :induct (induct-hint stmt mem i j))
	  ("Subgoal *1/14"
	   :use (While-termination-implies-body-termination
		 (:instance
		  Termination-implies-same-nbr-recursive-calls
		  (stmt (caddr stmt))
		  (i (+ -1 i))
		  (j (+ -1 j)))
		 (:instance
		  Termination-implies-same-result
		  (stmt (caddr stmt))
		  (i (+ -1 i))
		  (j (+ -1 j)))))
	  ("Subgoal *1/13"
	   :use (While-termination-implies-body-termination
		 (:instance
		  Termination-implies-same-nbr-recursive-calls
		  (stmt (caddr stmt))
		  (i (+ -1 i))
		  (j (+ -1 j)))))
	  ("Subgoal *1/6"
	   :use (Sequence-termination-implies-first-stmt-termination
		 (:instance
		  Termination-implies-same-nbr-recursive-calls
		  (stmt (cadr stmt))
		  (i (+ -1 i))
		  (j (+ -1 j)))
		 (:instance
		  Termination-implies-same-result
		  (stmt (cadr stmt))
		  (i (+ -1 i))
		  (j (+ -1 j)))))
	  ("Subgoal *1/5"
	   :use (Sequence-termination-implies-first-stmt-termination
		 (:instance
		  Termination-implies-same-nbr-recursive-calls
		  (stmt (cadr stmt))
		  (i (+ -1 i))
		  (j (+ -1 j)))))))

(defchoose
  choose-limit limit (stmt mem)
  (not (equal (mv-nth 0 (run-limit stmt mem limit))
	      nil)))

(defthm
  Run-limit-nfix-limit=run-limit-limit
  (equal (run-limit stmt mem (nfix limit))
	 (run-limit stmt mem limit))
  :rule-classes nil)

(defthm
  Nfix-choose-limit
  (implies (mv-nth 0 (run-limit stmt mem limit))
	   ((lambda (limit mem stmt)
	            (mv-nth 0 (run-limit stmt mem limit)))
	    (nfix (choose-limit stmt mem))
	    mem
	    stmt))
  :rule-classes nil
  :hints (("goal"
	   :use (choose-limit
		 (:instance
		  run-limit-nfix-limit=run-limit-limit
		  (limit (choose-limit stmt mem)))))))

(defun
  run (stmt mem)
  (mv-let (mem1 limit1)
	  (run-limit stmt mem (nfix (choose-limit stmt mem)))
	  (declare (ignore limit1))
	  mem1))

(defthm
  Subgoal-5-lemma-a
  (implies (and (mv-nth 0 (run-limit stmt mem (nfix (choose-limit stmt mem))))
		(equal (car stmt) 'if)
		(not (equal (eval-expr (cadr stmt) mem) 0)))
	   (equal (mv-nth 0 (run-limit stmt
				       mem
				       (nfix (choose-limit stmt mem))))
		  (mv-nth 0 (run-limit (caddr stmt)
				       mem
				       (nfix (choose-limit (caddr stmt) mem))))))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance
		  Nfix-choose-limit
		  (stmt (caddr stmt))
		  (limit (+ -1 (nfix (choose-limit stmt mem)))))
		 (:instance
		  Termination-implies-same-result
		  (stmt (caddr stmt))
		  (i (+ -1 (nfix (choose-limit stmt mem))))
		  (j (nfix (choose-limit (caddr stmt) mem))))))))

(defthm
  Subgoal-4-lemma-a
  (implies (and (mv-nth 0 (run-limit stmt mem (nfix (choose-limit stmt mem))))
		(equal (car stmt) 'if)
		(equal (eval-expr (cadr stmt) mem) 0))
	   (equal (mv-nth 0 (run-limit stmt
				       mem
				       (nfix (choose-limit stmt mem))))
		  (mv-nth 0 (run-limit (cadddr stmt)
				       mem
				       (nfix (choose-limit (cadddr stmt) mem))))))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance
		  Nfix-choose-limit
		  (stmt (cadddr stmt))
		  (limit (+ -1 (nfix (choose-limit stmt mem)))))
		 (:instance
		  Termination-implies-same-result
		  (stmt (cadddr stmt))
		  (i (+ -1 (nfix (choose-limit stmt mem))))
		  (j (nfix (choose-limit (cadddr stmt) mem))))))))

(defthm
  Then-termination-implies-if-termination
  (implies (and (mv-nth 0 (run-limit (caddr stmt) mem i))
		(equal (car stmt) 'if)
		(not (equal (eval-expr (cadr stmt) mem) 0))
		(natp i))
	   (mv-nth 0 (run-limit stmt mem (+ 1 i))))
  :rule-classes nil)

(defthm
  Else-termination-implies-if-termination
  (implies (and (mv-nth 0 (run-limit (cadddr stmt) mem i))
		(equal (car stmt) 'if)
		(equal (eval-expr (cadr stmt) mem) 0)
		(natp i))
	   (mv-nth 0 (run-limit stmt mem (+ 1 i))))
  :rule-classes nil)

(defthm
  Then-termination-implies-if-termination-nfix-choose-limit
  (implies (and (mv-nth 0 (run-limit (caddr stmt)
				     mem
				     (nfix (choose-limit (caddr stmt)
							 mem))))
		(equal (car stmt) 'if)
		(not (equal (eval-expr (cadr stmt) mem) 0)))
	   (mv-nth 0 (run-limit stmt mem (nfix (choose-limit stmt mem)))))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance
		  Then-termination-implies-if-termination
		  (i (nfix (choose-limit (caddr stmt) mem))))
		 (:instance
		  Nfix-choose-limit
		  (limit (+ 1 (nfix (choose-limit (caddr stmt) mem)))))))))

(defthm
  Else-termination-implies-if-termination-nfix-choose-limit
  (implies (and (mv-nth 0 (run-limit (cadddr stmt)
				     mem
				     (nfix (choose-limit (cadddr stmt)
							 mem))))
		(equal (car stmt) 'if)
		(equal (eval-expr (cadr stmt) mem) 0))
	   (mv-nth 0 (run-limit stmt mem (nfix (choose-limit stmt mem)))))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance
		  Else-termination-implies-if-termination
		  (i (nfix (choose-limit (cadddr stmt) mem))))
		 (:instance
		  Nfix-choose-limit
		  (limit (+ 1 (nfix (choose-limit (cadddr stmt) mem)))))))))

(defthm
  Subgoal-5-lemma-b
  (implies (and (not (mv-nth 0 (run-limit stmt mem (nfix (choose-limit stmt mem)))))
		(equal (car stmt) 'if)
		(not (equal (eval-expr (cadr stmt) mem) 0)))
	   (equal (mv-nth 0 (run-limit stmt
				       mem
				       (nfix (choose-limit stmt mem))))
		  (mv-nth 0 (run-limit (caddr stmt)
				       mem
				       (nfix (choose-limit (caddr stmt) mem))))))
  :rule-classes nil
  :hints (("Goal"
	   :use Then-termination-implies-if-termination-nfix-choose-limit)))

(defthm
  Subgoal-4-lemma-b
  (implies (and (not (mv-nth 0 (run-limit stmt mem (nfix (choose-limit stmt mem)))))
		(equal (car stmt) 'if)
		(equal (eval-expr (cadr stmt) mem) 0))
	   (equal (mv-nth 0 (run-limit stmt
				       mem
				       (nfix (choose-limit stmt mem))))
		  (mv-nth 0 (run-limit (cadddr stmt)
				       mem
				       (nfix (choose-limit (cadddr stmt) mem))))))
  :rule-classes nil
  :hints (("Goal"
	   :use Else-termination-implies-if-termination-nfix-choose-limit)))

(defthm
  Subgoal-5-lemma
  (implies (and (equal (car stmt) 'if)
		(not (equal (eval-expr (cadr stmt) mem) 0)))
	   (equal (mv-nth 0 (run-limit stmt
				       mem
				       (nfix (choose-limit stmt mem))))
		  (mv-nth 0 (run-limit (caddr stmt)
				       mem
				       (nfix (choose-limit (caddr stmt) mem))))))
  :rule-classes nil
  :hints (("Goal"
	   :use (Subgoal-5-lemma-a
		 Subgoal-5-lemma-b))))

(defthm
  Subgoal-4-lemma
  (implies (and (equal (car stmt) 'if)
		(equal (eval-expr (cadr stmt) mem) 0))
	   (equal (mv-nth 0 (run-limit stmt
				       mem
				       (nfix (choose-limit stmt mem))))
		  (mv-nth 0 (run-limit (cadddr stmt)
				       mem
				       (nfix (choose-limit (cadddr stmt) mem))))))
  :rule-classes nil
  :hints (("Goal"
	   :use (Subgoal-4-lemma-a
		 Subgoal-4-lemma-b))))

(defthm
  Termination-implies-sequence-def
  (implies (and (mv-nth 0 (run-limit stmt mem limit))
		(equal (car stmt) 'sequence))
	   (equal (run-limit stmt mem limit)
		  (run-limit (caddr stmt)
			     (mv-nth 0 (run-limit (cadr stmt) mem (+ -1 limit)))
			     (+ -1 (mv-nth 1
					   (run-limit (cadr stmt)
						      mem
						      (+ -1 limit)))))))
  :rule-classes nil)

(defthm
  Termination-implies-while-def
  (implies (and (mv-nth 0 (run-limit stmt mem limit))
		(equal (car stmt) 'while)
		(not (equal (eval-expr (cadr stmt) mem) 0)))
	   (equal (run-limit stmt mem limit)
		  (run-limit stmt
			     (mv-nth 0 (run-limit (caddr stmt) mem (+ -1 limit)))
			     (+ -1 (mv-nth 1
					   (run-limit (caddr stmt)
						      mem
						      (+ -1 limit)))))))
  :rule-classes nil)

(defthm
  Subgoal-6-lemma-a
  (implies (and (mv-nth 0 (run-limit stmt mem (nfix (choose-limit stmt mem))))
		(equal (car stmt) 'sequence))
	   (equal (mv-nth 0 (run-limit stmt
				       mem
				       (nfix (choose-limit stmt mem))))
		  (mv-nth 0 (run-limit (caddr stmt)
				       (mv-nth 0 (run-limit (cadr stmt)
							    mem
							    (nfix
							     (choose-limit
							      (cadr stmt)
							      mem))))
				       (nfix (choose-limit
					      (caddr stmt)
					      (mv-nth 0 (run-limit (cadr stmt)
								   mem
								   (nfix
								    (choose-limit
								     (cadr stmt)
								     mem))))))))))
  :rule-classes nil
  :hints (("goal"
	   :in-theory
	   (disable (:definition nfix))
	   :use ((:instance
		  Termination-implies-sequence-def
		  (limit (nfix (choose-limit stmt mem))))
		 (:instance
		  nfix-choose-limit
		  (stmt (cadr stmt))
		  (limit (+ -1 (nfix (choose-limit stmt mem)))))
		 (:instance
		  termination-implies-same-result
		  (stmt (cadr stmt))
		  (i (+ -1 (nfix (choose-limit stmt mem))))
		  (j (nfix (choose-limit (cadr stmt) mem))))
		 (:instance
		  nfix-choose-limit
		  (stmt (caddr stmt))
		  (mem  (mv-nth 0 (run-limit (cadr stmt)
					     mem
					     (+ -1 (nfix (choose-limit stmt
								       mem))))))
		  (limit (+ -1 (mv-nth 1
				       (run-limit (cadr stmt)
						  mem
						  (+ -1
						     (nfix (choose-limit stmt
									 mem))))))))
		 (:instance
		  termination-implies-same-result
		  (stmt (caddr stmt))
		  (mem (mv-nth 0
			       (run-limit (cadr stmt)
					  mem
					  (+ -1 (nfix (choose-limit stmt
								    mem))))))
		  (i (+ -1 (mv-nth 1
				   (run-limit (cadr stmt)
					      mem
					      (+ -1 (nfix (choose-limit stmt
									mem)))))))
		  (j (nfix
		      (choose-limit
		       (caddr stmt)
		       (mv-nth 0
			       (run-limit (cadr stmt)
					  mem
					  (+ -1
					     (nfix (choose-limit stmt
								 mem)))))))))))))

(defthm
  Subgoal-3-lemma-a
  (implies (and (mv-nth 0 (run-limit stmt mem (nfix (choose-limit stmt mem))))
		(equal (car stmt) 'while)
		(not (equal (eval-expr (cadr stmt) mem) 0)))
	   (equal (mv-nth 0 (run-limit stmt
				       mem
				       (nfix (choose-limit stmt mem))))
		  (mv-nth 0 (run-limit stmt
				       (mv-nth 0 (run-limit (caddr stmt)
							    mem
							    (nfix
							     (choose-limit
							      (caddr stmt)
							      mem))))
				       (nfix (choose-limit
					      stmt
					      (mv-nth 0 (run-limit (caddr stmt)
								   mem
								   (nfix
								    (choose-limit
								     (caddr stmt)
								     mem))))))))))
  :rule-classes nil
  :hints (("goal"
	   :in-theory
	   (disable (:definition nfix))
	   :use ((:instance
		  Termination-implies-while-def
		  (limit (nfix (choose-limit stmt mem))))
		 (:instance
		  nfix-choose-limit
		  (stmt (caddr stmt))
		  (limit (+ -1 (nfix (choose-limit stmt mem)))))
		 (:instance
		  termination-implies-same-result
		  (stmt (caddr stmt))
		  (i (+ -1 (nfix (choose-limit stmt mem))))
		  (j (nfix (choose-limit (caddr stmt) mem))))
		 (:instance
		  nfix-choose-limit
		  (mem  (mv-nth 0 (run-limit (caddr stmt)
					     mem
					     (+ -1 (nfix (choose-limit stmt
								       mem))))))
		  (limit (+ -1 (mv-nth 1
				       (run-limit (caddr stmt)
						  mem
						  (+ -1
						     (nfix (choose-limit stmt
									 mem))))))))
		 (:instance
		  termination-implies-same-result
		  (mem (mv-nth 0
			       (run-limit (caddr stmt)
					  mem
					  (+ -1 (nfix (choose-limit stmt
								    mem))))))
		  (i (+ -1 (mv-nth 1
				   (run-limit (caddr stmt)
					      mem
					      (+ -1 (nfix (choose-limit stmt
									mem)))))))
		  (j (nfix
		      (choose-limit
		       stmt
		       (mv-nth 0
			       (run-limit (caddr stmt)
					  mem
					  (+ -1
					     (nfix (choose-limit stmt
								 mem)))))))))))))

(defthm
  Subgoal-6-lemma-b
  (implies (and (not (mv-nth 0
			     (run-limit stmt
					mem
					(nfix (choose-limit stmt mem)))))
		(not (mv-nth 0 (run-limit (cadr stmt)
					  mem
					  (nfix
					   (choose-limit (cadr stmt) mem)))))
		(equal (car stmt) 'sequence))
	   (equal (mv-nth 0 (run-limit stmt
				       mem
				       (nfix (choose-limit stmt mem))))
		  (mv-nth 0 (run-limit (caddr stmt)
				       (mv-nth 0 (run-limit (cadr stmt)
							    mem
							    (nfix
							     (choose-limit
							      (cadr stmt)
							      mem))))
				       (nfix (choose-limit
					      (caddr stmt)
					      (mv-nth 0 (run-limit (cadr stmt)
								   mem
								   (nfix
								    (choose-limit
								     (cadr stmt)
								     mem))))))))))
  :rule-classes nil)

(defthm
  Subgoal-3-lemma-b
  (implies (and (not (mv-nth 0 (run-limit stmt mem (nfix (choose-limit stmt
								       mem)))))
		(not (mv-nth 0 (run-limit (caddr stmt)
					  mem
					  (nfix (choose-limit (caddr stmt)
							      mem)))))
		(equal (car stmt) 'while)
		(not (equal (eval-expr (cadr stmt) mem) 0)))
	   (equal (mv-nth 0 (run-limit stmt
				       mem
				       (nfix (choose-limit stmt mem))))
		  (mv-nth 0 (run-limit stmt
				       (mv-nth 0 (run-limit (caddr stmt)
							    mem
							    (nfix
							     (choose-limit
							      (caddr stmt)
							      mem))))
				       (nfix (choose-limit
					      stmt
					      (mv-nth 0 (run-limit (caddr stmt)
								   mem
								   (nfix
								    (choose-limit
								     (caddr stmt)
								     mem))))))))))
  :rule-classes nil)

(defthm
  Sequence-lemma-1
  (implies (and (equal (car stmt) 'sequence)
		(mv-nth 0 (run-limit (cadr stmt) mem i))
		(posp (mv-nth 1 (run-limit (cadr stmt) mem i)))
		(mv-nth 0 (run-limit (caddr stmt)
				     (mv-nth 0 (run-limit (cadr stmt)
							  mem
							  i))
				     (+ -1 (mv-nth 1 (run-limit (cadr stmt)
								mem
								i)))))
		(natp i))
	   (mv-nth 0 (run-limit stmt mem (+ 1 i))))
  :rule-classes nil)

(defthm
  While-lemma-1
  (implies (and (equal (car stmt) 'while)
		(mv-nth 0 (run-limit (caddr stmt) mem i))
		(posp (mv-nth 1 (run-limit (caddr stmt) mem i)))
		(mv-nth 0 (run-limit stmt
				     (mv-nth 0 (run-limit (caddr stmt)
							  mem
							  i))
				     (+ -1 (mv-nth 1 (run-limit (caddr stmt)
								mem
								i)))))
		(natp i))
	   (mv-nth 0 (run-limit stmt mem (+ 1 i))))
  :rule-classes nil)

;; ====================================
;; Assume there is an i and a j so that

;; (and (equal (car stmt) 'sequence)
;;      (mv-nth 0 (run-limit (cadr stmt) mem i))
;;      (mv-nth 0 (run-limit (caddr stmt
;;                                  (mv-nth 0 (run-limit (cadr stmt)
;;                                                       mem
;;                                                       i))
;;                                  j)))
;;      (natp i)
;;      (natp j))
;; -----------------------
;; Construct a k such that

;; (and (mv-nth 0 (run-limit (cadr stmt) mem k))
;;      (posp (mv-nth 1 (run-limit (cadr stmt) mem k)))
;;      (mv-nth 0 (run-limit (caddr stmt)
;;                           (mv-nth 0 (run-limit (cadr stmt)
;;                                                mem
;;                                                k))
;;                           (+ -1 (mv-nth 1 (run-limit (cadr stmt)
;;                                                      mem
;;                                                      k)))))
;;      (natp k))
;; ---------------------------------
;; Then Sequence-lemma-1 applies, so

;;    (mv-nth 0 (run-limit stmt mem (+ 1 k)))
;; ---------------------
;; Let k be  (+ (max i
;;                   (+ 1 j))
;;              (- i (mv-nth 1 (run-limit (cadr stmt)
;;                                        mem
;;                                        i))))
;; ===========================================

(defthm
  Sequence-lemma-2
  (implies (and (natp i)
		(natp j)
		(mv-nth 0 (run-limit (cadr stmt) mem i)))
	   (let ((k (+ (max i
			    (+ 1 j))
		       (- i (mv-nth 1 (run-limit (cadr stmt)
						 mem
						 i))))))
	     (and (mv-nth 0 (run-limit (cadr stmt) mem k))
		  (equal (mv-nth 0 (run-limit (cadr stmt) mem i))
			 (mv-nth 0 (run-limit (cadr stmt) mem k)))
		  (equal (- i
			    (mv-nth 1 (run-limit (cadr stmt) mem i)))
			 (- k
			    (mv-nth 1 (run-limit (cadr stmt) mem k))))
		  (equal (max i (+ 1 j))
			 (mv-nth 1 (run-limit (cadr stmt) mem k))))))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance
		  termination-implies-bigger-limit-termination
		  (stmt (cadr stmt))
		  (j (+ (max i
			     (+ 1 j))
			(- i (mv-nth 1 (run-limit (cadr stmt)
						  mem
						  i))))))
		 (:instance
		  termination-implies-same-result
		  (stmt (cadr stmt))
		  (j (+ (max i
			     (+ 1 j))
			(- i (mv-nth 1 (run-limit (cadr stmt)
						  mem
						  i))))))
		 (:instance
		  termination-implies-same-nbr-recursive-calls
		  (stmt (cadr stmt))
		  (j (+ (max i
			     (+ 1 j))
			(- i (mv-nth 1 (run-limit (cadr stmt)
						  mem
						  i))))))))))

(defthm
  While-lemma-2
  (implies (and (natp i)
		(natp j)
		(mv-nth 0 (run-limit (caddr stmt) mem i)))
	   (let ((k (+ (max i
			    (+ 1 j))
		       (- i (mv-nth 1 (run-limit (caddr stmt)
						 mem
						 i))))))
	     (and (mv-nth 0 (run-limit (caddr stmt) mem k))
		  (equal (mv-nth 0 (run-limit (caddr stmt) mem i))
			 (mv-nth 0 (run-limit (caddr stmt) mem k)))
		  (equal (- i
			    (mv-nth 1 (run-limit (caddr stmt) mem i)))
			 (- k
			    (mv-nth 1 (run-limit (caddr stmt) mem k))))
		  (equal (max i (+ 1 j))
			 (mv-nth 1 (run-limit (caddr stmt) mem k))))))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance
		  termination-implies-bigger-limit-termination
		  (stmt (caddr stmt))
		  (j (+ (max i
			     (+ 1 j))
			(- i (mv-nth 1 (run-limit (caddr stmt)
						  mem
						  i))))))
		 (:instance
		  termination-implies-same-result
		  (stmt (caddr stmt))
		  (j (+ (max i
			     (+ 1 j))
			(- i (mv-nth 1 (run-limit (caddr stmt)
						  mem
						  i))))))
		 (:instance
		  termination-implies-same-nbr-recursive-calls
		  (stmt (caddr stmt))
		  (j (+ (max i
			     (+ 1 j))
			(- i (mv-nth 1 (run-limit (caddr stmt)
						  mem
						  i))))))))))

(defthm
  Sequence-lemma-3
  (implies (and (mv-nth 0 (run-limit (cadr stmt) mem i))
		(mv-nth 0 (run-limit (caddr stmt)
				     (mv-nth 0 (run-limit (cadr stmt)
							  mem
							  i))
				     j))
		(natp i)
		(natp j))
	   (let ((k (+ (max i
			    (+ 1 j))
		       (- i (mv-nth 1 (run-limit (cadr stmt)
						 mem
						 i))))))
	     (mv-nth 0 (run-limit (caddr stmt)
				  (mv-nth 0 (run-limit (cadr stmt)
						       mem
						       k))
				  (+ -1 (mv-nth 1 (run-limit (cadr stmt)
							     mem
							     k)))))))
  :rule-classes nil
  :hints (("Goal"
	   :use (Sequence-lemma-2
		 (:instance
		  termination-implies-bigger-limit-termination
		  (stmt (caddr stmt))
		  (mem (let ((k (+ (max i
					(+ 1 j))
				   (- i (mv-nth 1 (run-limit (cadr stmt)
							     mem
							     i))))))
			 (mv-nth 0 (run-limit (cadr stmt) mem k))))
		  (i j)
		  (j (let ((k (+ (max i
				      (+ 1 j))
				 (- i (mv-nth 1 (run-limit (cadr stmt)
							   mem
							   i))))))
		       (+ -1 (mv-nth 1 (run-limit (cadr stmt)
						  mem
						  k))))))))))

(defthm
  While-lemma-3
  (implies (and (mv-nth 0 (run-limit (caddr stmt) mem i))
		(mv-nth 0 (run-limit stmt
				     (mv-nth 0 (run-limit (caddr stmt)
							  mem
							  i))
				     j))
		(natp i)
		(natp j))
	   (let ((k (+ (max i
			    (+ 1 j))
		       (- i (mv-nth 1 (run-limit (caddr stmt)
						 mem
						 i))))))
	     (mv-nth 0 (run-limit stmt
				  (mv-nth 0 (run-limit (caddr stmt)
						       mem
						       k))
				  (+ -1 (mv-nth 1 (run-limit (caddr stmt)
							     mem
							     k)))))))
  :rule-classes nil
  :hints (("Goal"
	   :use (While-lemma-2
		 (:instance
		  termination-implies-bigger-limit-termination
		  (mem (let ((k (+ (max i
					(+ 1 j))
				   (- i (mv-nth 1 (run-limit (caddr stmt)
							     mem
							     i))))))
			 (mv-nth 0 (run-limit (caddr stmt) mem k))))
		  (i j)
		  (j (let ((k (+ (max i
				      (+ 1 j))
				 (- i (mv-nth 1 (run-limit (caddr stmt)
							   mem
							   i))))))
		       (+ -1 (mv-nth 1 (run-limit (caddr stmt)
						  mem
						  k))))))))))

(defthm
  Args-terminate-implies-sequence-terminates
  (implies (and (equal (car stmt) 'sequence)
		(mv-nth 0 (run-limit (cadr stmt) mem i))
		(mv-nth 0 (run-limit (caddr stmt)
				     (mv-nth 0 (run-limit (cadr stmt)
							  mem
							  i))
				     j))
		(natp i)
		(natp j))
	   (let ((k (+ (max i
			    (+ 1 j))
		       (- i (mv-nth 1 (run-limit (cadr stmt)
						 mem
						 i))))))
	     (mv-nth 0 (run-limit stmt mem (+ 1 k)))))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance
		  Sequence-lemma-1
		  (i (+ (max i
			     (+ 1 j))
			(- i (mv-nth 1 (run-limit (cadr stmt)
						  mem
						  i))))))
		 Sequence-lemma-2
		 Sequence-lemma-3))))

(defthm
  Body-&-subwhile-terminate-implies-while-terminates
  (implies (and (equal (car stmt) 'while)
		(mv-nth 0 (run-limit (caddr stmt) mem i))
		(mv-nth 0 (run-limit stmt
				     (mv-nth 0 (run-limit (caddr stmt)
							  mem
							  i))
				     j))
		(natp i)
		(natp j))
	   (let ((k (+ (max i
			    (+ 1 j))
		       (- i (mv-nth 1 (run-limit (caddr stmt)
						 mem
						 i))))))
	     (mv-nth 0 (run-limit stmt mem (+ 1 k)))))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance
		  While-lemma-1
		  (i (+ (max i
			     (+ 1 j))
			(- i (mv-nth 1 (run-limit (caddr stmt)
						  mem
						  i))))))
		 While-lemma-2
		 While-lemma-3))))

(defthm
  Args-terminate-implies-sequence-terminates-nfix-choose-limit
  (implies (and (equal (car stmt) 'sequence)
		(mv-nth 0 (run-limit (cadr stmt)
				     mem
				     (nfix (choose-limit (cadr stmt)
							 mem))))
		(mv-nth 0 (run-limit
			   (caddr stmt)
			   (mv-nth 0 (run-limit (cadr stmt)
						mem
						(nfix (choose-limit (cadr stmt)
								    mem))))
			   (nfix
			    (choose-limit
			     (caddr stmt)
			     (mv-nth 0 (run-limit (cadr stmt)
						  mem
						  (nfix (choose-limit (cadr stmt)
								      mem)))))))))
	   (mv-nth 0 (run-limit stmt
				mem
				(nfix (choose-limit stmt mem)))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition nfix))
	   :use ((:instance
		  Args-terminate-implies-sequence-terminates
		  (i (nfix (choose-limit (cadr stmt) mem)))
		  (j (nfix
		      (choose-limit
		       (caddr stmt)
		       (mv-nth 0 (run-limit (cadr stmt)
					    mem
					    (nfix (choose-limit (cadr stmt)
								mem))))))))
		 (:instance
		  nfix-choose-limit
		  (limit (+ 1
			    (let ((i (nfix (choose-limit (cadr stmt) mem)))
				  (j (nfix
				      (choose-limit
				       (caddr stmt)
				       (mv-nth 0
					       (run-limit (cadr stmt)
							  mem
							  (nfix (choose-limit
								 (cadr stmt)
								 mem))))))))
			      (+ (max i
				      (+ 1 j))
				 (- i (mv-nth 1 (run-limit (cadr stmt)
							   mem
							   i))))))))))))
(defthm
  Body-&-subwhile-terminate-implies-while-terminates-nfix-choose-limit
  (implies (and (equal (car stmt) 'while)
		(mv-nth 0 (run-limit (caddr stmt)
				     mem
				     (nfix (choose-limit (caddr stmt)
							 mem))))
		(mv-nth 0 (run-limit
			   stmt
			   (mv-nth 0 (run-limit (caddr stmt)
						mem
						(nfix (choose-limit (caddr stmt)
								    mem))))
			   (nfix
			    (choose-limit
			     stmt
			     (mv-nth 0 (run-limit (caddr stmt)
						  mem
						  (nfix (choose-limit (caddr stmt)
								      mem)))))))))
	   (mv-nth 0 (run-limit stmt
				mem
				(nfix (choose-limit stmt mem)))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition nfix))
	   :use ((:instance
		  Body-&-subwhile-terminate-implies-while-terminates
		  (i (nfix (choose-limit (caddr stmt) mem)))
		  (j (nfix
		      (choose-limit
		       stmt
		       (mv-nth 0 (run-limit (caddr stmt)
					    mem
					    (nfix (choose-limit (caddr stmt)
								mem))))))))
		 (:instance
		  nfix-choose-limit
		  (limit (+ 1
			    (let ((i (nfix (choose-limit (caddr stmt) mem)))
				  (j (nfix
				      (choose-limit
				       stmt
				       (mv-nth 0
					       (run-limit (caddr stmt)
							  mem
							  (nfix (choose-limit
								 (caddr stmt)
								 mem))))))))
			      (+ (max i
				      (+ 1 j))
				 (- i (mv-nth 1 (run-limit (caddr stmt)
							   mem
							   i))))))))))))

(defthm
  Subgoal-6-lemma-c
  (implies (and (not (mv-nth 0
			     (run-limit stmt
					mem
					(nfix (choose-limit stmt mem)))))
		(mv-nth 0 (run-limit (cadr stmt)
				     mem
				     (nfix (choose-limit (cadr stmt) mem))))
		(equal (car stmt) 'sequence))
	   (equal (mv-nth 0 (run-limit stmt
				       mem
				       (nfix (choose-limit stmt mem))))
		  (mv-nth 0 (run-limit (caddr stmt)
				       (mv-nth 0 (run-limit (cadr stmt)
							    mem
							    (nfix
							     (choose-limit
							      (cadr stmt)
							      mem))))
				       (nfix (choose-limit
					      (caddr stmt)
					      (mv-nth 0 (run-limit (cadr stmt)
								   mem
								   (nfix
								    (choose-limit
								     (cadr stmt)
								     mem))))))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition nfix))
	   :use Args-terminate-implies-sequence-terminates-nfix-choose-limit)))

(defthm
  Subgoal-3-lemma-c
  (implies (and (not (mv-nth 0 (run-limit stmt mem (nfix (choose-limit stmt
								       mem)))))
		(mv-nth 0 (run-limit (caddr stmt)
				     mem
				     (nfix (choose-limit (caddr stmt)
							 mem))))
		(equal (car stmt) 'while)
		(not (equal (eval-expr (cadr stmt) mem) 0)))
	   (equal (mv-nth 0 (run-limit stmt
				       mem
				       (nfix (choose-limit stmt mem))))
		  (mv-nth 0 (run-limit stmt
				       (mv-nth 0 (run-limit (caddr stmt)
							    mem
							    (nfix
							     (choose-limit
							      (caddr stmt)
							      mem))))
				       (nfix (choose-limit
					      stmt
					      (mv-nth 0 (run-limit (caddr stmt)
								   mem
								   (nfix
								    (choose-limit
								     (caddr stmt)
								     mem))))))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition nfix))
	   :use
	   Body-&-subwhile-terminate-implies-while-terminates-nfix-choose-limit)))

(defthm
  Subgoal-6-lemma
  (implies (equal (car stmt) 'sequence)
	   (equal (mv-nth 0 (run-limit stmt
				       mem
				       (nfix (choose-limit stmt mem))))
		  (mv-nth 0
			  (run-limit
			   (caddr stmt)
			   (mv-nth 0 (run-limit (cadr stmt)
						mem
						(nfix (choose-limit (cadr stmt)
								    mem))))
			   (nfix (choose-limit
				  (caddr stmt)
				  (mv-nth 0 (run-limit (cadr stmt)
						       mem
						       (nfix
							(choose-limit (cadr stmt)
								      mem))))))))))
  :rule-classes nil
  :hints (("Goal"
	   :use (Subgoal-6-lemma-a
		 Subgoal-6-lemma-b
		 Subgoal-6-lemma-c))))

(defthm
  Subgoal-3-lemma
  (implies (and (equal (car stmt) 'while)
		(not (equal (eval-expr (cadr stmt) mem) 0)))
	   (equal (mv-nth 0 (run-limit stmt
				       mem
				       (nfix (choose-limit stmt mem))))
		  (mv-nth 0
			  (run-limit
			   stmt
			   (mv-nth 0 (run-limit (caddr stmt)
						mem
						(nfix (choose-limit (caddr stmt)
								    mem))))
			   (nfix (choose-limit
				  stmt
				  (mv-nth 0 (run-limit (caddr stmt)
						       mem
						       (nfix
							(choose-limit (caddr stmt)
								      mem))))))))))
  :rule-classes nil
  :hints (("Goal"
	   :use (Subgoal-3-lemma-a
		 Subgoal-3-lemma-b
		 Subgoal-3-lemma-c))))

(defthm
  Run-satisfies-specification
  (equal (run stmt mem)
	 (if (null mem)
	     nil
	     (case (op stmt)
		   (skip      mem)
		   (assign    (run-assignment stmt mem))
		   (sequence  (run (arg2 stmt)(run (arg1 stmt) mem)))
		   (if        (if (zerop (eval-expr (arg1 stmt) mem))
				  (run (arg3 stmt) mem)
				  (run (arg2 stmt) mem)))
		   (while     (if (zerop (eval-expr (arg1 stmt) mem))
				  mem
				  (run stmt (run (arg2 stmt) mem))))
		   (otherwise mem))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition nfix)))
; fcd/Satriani v3.7 Moore - used to be Subgoal 6
	  ("Subgoal 7"
	   :use Subgoal-6-lemma)
; fcd/Satriani v3.7 Moore - used to be Subgoal 5
	  ("Subgoal 4"
	   :use Subgoal-5-lemma)
; fcd/Satriani v3.7 Moore - used to be Subgoal 4
	  ("Subgoal 3"
	   :use Subgoal-4-lemma)
; fcd/Satriani v3.7 Moore - used to be Subgoal 3
	  ("Subgoal 2"
	   :use Subgoal-3-lemma)))
