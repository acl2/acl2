; WyoM1 Correctness Without a Clock book
; Copyright (C) 2004 John R. Cowles, University of Wyoming

; This program is free software; you can redistribute it and/or
; modify it under the terms of the GNU General Public License as
; published by the Free Software Foundation; either version 2 of
; the License, or (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free
; Software Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139,
; USA.

; Written by: John R. Cowles
; email:      cowles@uwyo.edu
; Department of Computer Science
; University of Wyoming
; Laramie, WY 82071 U.S.A.

; Based on earlier work and ideas of
;            J Strother Moore      and  Panagiotis Manolios
; email:     Moore@cs.utexas.edu        manolios@cc.gatech.edu
; Department of Computer Sciences  College of Computing
; University of Texas at Austin    Georgia Institute of Technology
; Austin, TX 78712-1188 U.S.A.     Atlanta Georgia 30332-0280 U.S.A.
;==================================================================
#|
(include-book "WyoM1-utilities")

(certify-book "WyoM1-correct" 1)
|#

; The following was changed from "WyoM1" by Matt K. for ACL2 2.9.3 because
; package names may no longer contain lower case characters.
(in-package "WYO-M1")

; Use the Defpun book by Manolios and Moore.
(include-book "../../../../misc/defpun")

; Defpun is not part of the WyoM1-utilities, so it is added by macro.
(defmacro defpun (g args &rest tail)
  `(acl2::defpun ,g ,args ,@tail))

;; The clocked interpreter for WyoM1 is

;;  (DEFUN RUN (S N)
;;    (IF (ZP N)
;;        S
;;        (RUN (STEP S) (- N 1))))

;; An interpreter without a clock for WyoM1 is given below by run-w.

;; (run-w s) runs state s to termination, if a halted state can be
;; reached by repeated steps of WyoM1. The value of (run-w s) on
;; states that do not terminate is not specified.

(defun haltedp (s)
  (equal s (step s)))

(defpun run-w (s)
  (if (haltedp s)
      s
      (run-w (step s))))

;; The following equivalence relation holds between two terminating
;; states precisely when they terminate in the same state.

(defun == (s1 s2)
  (equal (run-w s1)
	 (run-w s2)))

;; ==-IS-AN-EQUIVALENCE
(defequiv ==)

(in-theory (disable step-opener))

;; Any state is related by == to the state obtained by stepping
;; M1 once.

(defthm ==-step
  (== s (step s))
  :rule-classes nil)

(defthm ==-stepper
  (implies (and (consp (next-inst
			(make-state call-stack defs)))
		(not (equal
		      (op-code (next-inst
				(make-state call-stack defs)))
		      'call)))
	   (== (make-state call-stack defs)
	       (step (make-state call-stack defs)))))

(defthm general-==-stepper
  (implies (equal call-stack call-stack) ; not an abbreviation rule!
           (== (make-state call-stack defs)
               (step (make-state call-stack defs)))))

(defthm ==-run
  (== (run s n) s)
  :hints (("Goal"
	   :in-theory (enable run))))

;; The next theorem implies that if the execution paths from s1
;; s2  intersect, then (== s1 s2).
(defthm ==-Y
  (implies (== (run s1 n)
               (run s2 m))
           (== s1 s2))
  :rule-classes nil)

(defthm run-w-run
  (implies (haltedp (run s n))
	   (equal (run-w s)
		  (run s n)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (enable run))))

(defthm haltedp-==
  (implies (and (haltedp s1)
		(haltedp s2)
		(== s1 s2))
	   (equal s1 s2))
  :rule-classes nil)

(in-theory (disable == general-==-stepper))
(in-theory (enable step))
;;-----------------------------------------------------
;; Square

(defconst *sq-def*
  '(sq (n)
       (load n)
       (dup)
       (mul)
       (ret)))

(defabbrev sq (x)
  (* x  x))

(defun execute-SQ (s)
  (modify s
	  :pc (+ 1 (pc s))                  ;; (pc s) = pc of
                                            ;;       (top-frame s)
	  :stack (push (sq (top (stack s))) ;; (stack s) = stack
		       (pop (stack s)))))   ;;    of (top-frame s)

;; The WyoM1 program for the function sq behaves as expected:

(defthm ==-sq
  (implies (equal (bound? 'sq (defs s))
		  *sq-def*)
	   (== (do-inst '(call sq) s)
	       (execute-sq s))))
;;----------------------------------------------------
;; Max

(defconst *max-def*
  '(max (x y)
	(load x)
	(load y)
	(sub)
	(ifle 3)
	(load x)
	(ret)
	(load y)
	(ret)))

(defun execute-MAX (s)
  (modify s
	  :pc (+ 1 (pc s))                  ;; (pc s) = pc of
                                            ;;       (top-frame s)
	  :stack (push (max (top (pop (stack s)))
			    (top (stack s)));; (stack s) = stack
		       (pop (pop (stack s))))));; of (top-frame s)

;; The WyoM1 program for the function max behaves as expected:

(defthm ==-max
  (implies (equal (bound? 'max (defs s))
		  *max-def*)
	   (== (do-inst '(call max) s)
	       (execute-max s))))
;;---------------------------------------------------
;; Recursive factorial

(defconst *fact-def*
  '(fact (n)
	 (load n)       ;;  0
	 (ifgt 3)       ;;  1
	 (push 1)       ;;  2
	 (ret)          ;;  3
	 (load n)       ;;  4
	 (load n)       ;;  5
	 (push 1)       ;;  6
	 (sub)          ;;  7
	 (call fact)    ;;  8
	 (mul)          ;;  9
	 (ret)))        ;; 10

(defun ! (n)
  (if (zp n)
      1
      (* n (! (- n 1)))))

(defun execute-FACT (s)
  (modify s
	  :pc (+ 1 (pc s))                 ;; (pc s) = pc of
                                           ;;       (top-frame s)
	  :stack (push (! (top (stack s))) ;; (stack s) = stack
		       (pop (stack s)))))  ;;    of (top-frame s)

(in-theory (disable (:EXECUTABLE-COUNTERPART MAKE-FRAME)))

;; This induction-hint was created from the failed proof
;; of ==-fact-lemma without the induction hint.

(defun ==-fact-hint (call-stack defs n)
  (if (zp n)
      (list call-stack defs)
      (==-fact-hint
       (push (make-frame 8
			 (list (cons 'n
				     (top (stack
					   (make-state call-stack
						       defs)))))
			 (push (+ -1 (top (stack
					   (make-state call-stack
						       defs))))
			       (push (top (stack
					   (make-state call-stack
						       defs)))
				     nil))
			  (cddr *fact-def*))
	      (push (make-frame (+ 1 (pc (make-state call-stack
						     defs)))
				(locals (make-state call-stack
						    defs))
				(pop (stack (make-state call-stack
							defs)))
				(program (make-state call-stack
						     defs)))
		    (pop call-stack)))
       defs
       (- n 1))))

;; Note the :restrict hint below.
;; This hint restricts the application of the rewrite rule,
;; general-==-stepper.
;; Please look up the :restrict hint in ACL2's documentation.
;; Look under HINTS.

(defthm ==-fact-lemma
 (implies (and (equal (bound? 'fact defs)
		      *fact-def*)
	       (equal (next-inst (make-state call-stack
					     defs))
		      '(call fact))
	       (equal n (top (stack (make-state call-stack
						defs))))
	       (integerp n)
	       (>= n 0))
	  (== (make-state call-stack defs)
	      (execute-FACT (make-state call-stack defs))))
 :hints (("Goal"
	  :in-theory (enable general-==-stepper)
	  :restrict ((general-==-stepper
		      ((call-stack call-stack)
		       (defs defs))))
	  :induct (==-fact-hint call-stack defs n))))

;; The WyoM1 program for the function fact behaves as expected:

(defthm ==-fact
 (implies (and (equal (bound? 'fact (defs s))
		      *fact-def*)
	       (integerp (top (stack s)))
	       (>= (top (stack s)) 0))
	  (== (do-inst '(call fact) s)
	      (execute-FACT s))))

(in-theory (disable ==-fact-lemma))
;;----------------------------------------------------

;; Use the interpreter without a clock for WyoM1, run-w, to
;; state and prove an WyoM1 program correctness result.

;; Informal Correctness Result

;; Let s be the following state

;;  (modify nil
;; 	 :pc 0
;; 	 :locals local-vars
;; 	 :stack s0
;; 	 :program '((load x)      ;; 0
;; 		    (call sq)     ;; 1
;; 		    (call fact)   ;; 2
;; 		    (load x)      ;; 3
;; 		    (call fact)   ;; 4
;; 		    (call sq)     ;; 5
;; 		    (call max)    ;; 6
;; 		    (store y)     ;; 7
;; 		    (halt))       ;; 8
;; 	 :defs (list *sq-def*
;; 		     *max-def*
;; 		     *fact-def*)).

;; Let x be the value of the variable 'x in (locals s).

;; If x is a nonnegative integer and s is run to
;; termination, then WyoM1 ends in the following state:

;;    (modify s
;; 	   :pc 8
;; 	   :locals (bind 'y (max (! (sq x))
;; 				 (sq (! x)))
;; 			 (locals s)))

;; First  we show that the initial state above is related
;; by == to the final state above.

(defthm ==-s-halt-state
  (let* ((s (modify nil
		    :pc 0
		    :locals local-vars
		    :stack s0
		    :program '((load x)      ;; 0
			       (call sq)     ;; 1
			       (call fact)   ;; 2
			       (load x)      ;; 3
			       (call fact)   ;; 4
			       (call sq)     ;; 5
			       (call max)    ;; 6
			       (store y)     ;; 7
			       (halt))       ;; 8
		    :defs (list *sq-def*
				*max-def*
				*fact-def*)))
	 (x (binding 'x (locals s))))
    (implies (and (integerp x)
		  (>= x 0))
	     (== s
		 (modify s
			 :pc 8
			 :locals (bind 'y (max (! (sq x))
					       (sq (! x)))
				       (locals s))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (enable general-==-stepper))))

;; Formal Correctness Result

(defthm prog-is-correct-with-run-w
  (let* ((s (modify nil
		    :pc 0
		    :locals local-vars
		    :stack s0
		    :program '((load x)      ;; 0
			       (call sq)     ;; 1
			       (call fact)   ;; 2
			       (load x)      ;; 3
			       (call fact)   ;; 4
			       (call sq)     ;; 5
			       (call max)    ;; 6
			       (store y)     ;; 7
			       (halt))       ;; 8
		    :defs (list *sq-def*
				*max-def*
				*fact-def*)))
	 (x (binding 'x (locals s))))
    (implies (and (integerp x)
		  (>= x 0))
	     (equal (run-w s)
		    (modify s
			    :pc 8
			    :locals (bind 'y (max (! (sq x))
						  (sq (! x)))
					  (locals s))))))
  :hints (("Goal"
	   :in-theory (enable ==)
	   :use ==-s-halt-state)))

(defthm haltedp-state
  (let* ((s (modify nil
		    :pc 0
		    :locals local-vars
		    :stack s0
		    :program '((load x)      ;; 0
			       (call sq)     ;; 1
			       (call fact)   ;; 2
			       (load x)      ;; 3
			       (call fact)   ;; 4
			       (call sq)     ;; 5
			       (call max)    ;; 6
			       (store y)     ;; 7
			       (halt))       ;; 8
		    :defs (list *sq-def*
				*max-def*
				*fact-def*)))
	 (x (binding 'x (locals s))))
    (haltedp (modify s
		     :pc 8
		     :locals (bind 'y (max (! (sq x))
					   (sq (! x)))
				   (locals s))))))

;; ==================================================================
;; We now illustrate the meta-theorem that says if ACL2 can prove
;; prog-is-correct-with-run-w, then ACL2 can also prove that there
;; is a nonnegative integer n such that the statement of the
;; prog-is-correct-with-run-w remains true when (run-w s) is replaced
;; by (run s n).

;; Let s be the state (modify nil
;; 			   :pc 0
;; 			   :locals local-vars
;; 			   :stack s0
;; 			   :program '((load x)      ;; 0
;; 				      (call sq)     ;; 1
;; 				      (call fact)   ;; 2
;; 				      (load x)      ;; 3
;; 				      (call fact)   ;; 4
;; 				      (call sq)     ;; 5
;; 				      (call max)    ;; 6
;; 				      (store y)     ;; 7
;; 				      (halt))       ;; 8
;; 			   :defs (list *sq-def*
;; 				       *max-def*
;; 				       *fact-def*))
;; and let x be the (binding 'x (locals s)).

;; We now show that there is an nonnegative integer n such that
;;  (run s n) =  (modify s
;; 		      :pc 8
;; 		      :locals (bind 'y (max (! (sq x))
;; 					    (sq (! x)))
;; 				    (locals s))))))
;;= = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;; The PROOF of THEOREM 4 is carefully followed.
;;    Notation in           Notation in
;; Proof of THEOREM 4        THIS proof
;;     test4  --------------- haltedp
;;     base4  --------------- identity ie., (identity x) = x
;;     step4  --------------- step
;;     step4n --------------- run
;;      (a)   --------------- Let s = (modify nil
;;                                            :pc 0
;;                                            :locals local-vars
;;                                            :stack s0
;;                                            :program '((load x)      ;; 0
;;                                                       (call sq)     ;; 1
;;                                                       (call fact)   ;; 2
;;                                                       (load x)      ;; 3
;;                                                       (call fact)   ;; 4
;;                                                       (call sq)     ;; 5
;;                                                       (call max)    ;; 6
;;                                                       (store y)     ;; 7
;;                                                       (halt))       ;; 8
;;                                            :defs (list *sq-def*
;;                                                        *max-def*
;;                                                        *fact-def*))
;;       (b)    --------------- (modify s
;;                                      :pc 8
;;                                      :locals (bind 'y (max (! (sq x))
;;                                                            (sq (! x)))
;;						   (locals s)))

;; (defchoose
;;   nbr-step4 (n)(x)
;;   (test4 (step4n x n)))

(defchoose
  nbr-steps-to-halt (n)(s)
  (haltedp (run s n)))

;; (defun
;;   f4n (x n)
;;   (declare (xargs :measure (nfix n)))
;;   (if (or (zp n) (test4 x))
;;       (base4 x)
;;       (f4n (step4 x)(- n 1))))

(defun
  clocked-run-w1 (s n)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n)
	  (haltedp s))
      s
      (clocked-run-w1 (step s)(- n 1))))

;; (defun
;;   f4a (x)
;;   (if (test4 (step4n x (nbr-step4 x)))
;;       (f4n x (nbr-step4 x))
;;       (if (equal (b) nil)
;;           t
;;           nil)))

(defun
  run-w1 (s)
  (if (haltedp (run s (nbr-steps-to-halt s)))
      (clocked-run-w1 s (nbr-steps-to-halt s))
      nil))

;; This encapsulate merely hides some tedious details of the proof.
(encapsulate
 nil

 (local (in-theory (disable step haltedp run-opener)))
 (local (in-theory (enable run)))

;;  (local
;;   (defthm
;;     test4-nbr-step4
;;     (implies (test4 x)
;;              (test4 (step4n x (nbr-step4 x))))
;;     :hints (("Goal"
;;              :use (:instance
;;                    nbr-step4
;;                    (n 0))))))

 (local
  (defthm
    haltedp-nbr-steps-to-halt
    (implies (haltedp s)
	     (haltedp (run s (nbr-steps-to-halt s))))
    :hints (("Goal"
	     :use (:instance
		   nbr-steps-to-halt
		   (n 0))))))

;;  (local
;;   (defthm
;;     test4-f4a-def
;;     (implies (test4 x)
;;              (equal (f4a x)(base4 x)))))

 (local
  (defthm
    haltedp-run-w1-def
    (implies (haltedp s)
	     (equal (run-w1 s) s))))

;;  (local
;;   (defthm
;;     open-step4n
;;     (implies (and (integerp n)
;;                   (> n 0))
;;              (equal (step4n x n)
;;                     (step4n (step4 x)(- n 1))))))

;;  (local
;;   (defthm +1-1
;;     (equal (+ -1 +1 x) (fix x))))

;;  (local
;;   (defthm
;;     step4-step4n-nbr-step4
;;     (implies (test4 (step4n (step4 x)(nbr-step4 (step4 x))))
;;              (test4 (step4n x (nbr-step4 x))))
;;     :hints (("Goal"
;;              :use (:instance
;;                    nbr-step4
;;                    (n (+ 1 (nfix (nbr-step4 (step4 x))))))))
;;     :rule-classes :forward-chaining))

 (local (defthm step-stepn-nbr-steps-to-halt
          (implies (haltedp (run (step s)(nbr-steps-to-halt
					  (step s))))
                   (haltedp (run s (nbr-steps-to-halt s))))
          :hints
          (("goal"
	    :use ((:instance
		   nbr-steps-to-halt
		   (n (+ 1 (nfix (nbr-steps-to-halt (step s))))))
		  (:instance
		   nbr-steps-to-halt
		   (n 1)))))
          :rule-classes :forward-chaining))

;;  (local
;;   (defthm
;;     not-test4-nbr-step4
;;     (implies (not (test4 x))
;;              (iff (test4 (step4n (step4 x)(nbr-step4 (step4 x))))
;;                   (test4 (step4n x (nbr-step4 x)))))
;;     :hints (("Subgoal 2"
;;              :use (:instance
;;                    nbr-step4
;;                    (x (step4 x))
;;                    (n (+ -1 (nbr-step4 x))))))))

 (local (defthm haltedp-nil-nbr-steps-to-halt
          (implies (not (haltedp s))
                   (iff (haltedp
			 (run (step s)
			      (nbr-steps-to-halt (step s))))
                        (haltedp
			 (run s (nbr-steps-to-halt s)))))
          :hints
          (("subgoal 2"
	    :expand (run s (nbr-steps-to-halt s))
            :use
            ((:instance
	      nbr-steps-to-halt (s (step s))
	      (n (+ -1 (nbr-steps-to-halt s)))))))))

;;  (local
;;   (defthm
;;     f4n-step4
;;     (implies (and (test4 (step4n x n))
;;                   (test4 (step4n x m)))
;;              (equal (f4n x n)(f4n x m)))
;;     :rule-classes nil))

 (local (defthm clocked-run-w1-step
          (implies (and (haltedp (run s n))
			(haltedp (run s m)))
                   (equal (clocked-run-w1 s n)
			  (clocked-run-w1 s m)))
          :rule-classes nil))

;;  (defthm
;;    f4a-f4-def
;;    (equal (f4a x)
;;           (if (test4 x)
;;               (base4 x)
;;               (f4a (step4 x))))
;;    :hints (("Subgoal 3"
;;             :expand (f4n x (nbr-step4 x)))
;;            ("Subgoal 3.2"
;;             :use (:instance
;;                   f4n-step4
;;                   (x (step4 x))
;;                   (n (+ -1 (nbr-step4 x)))
;;                   (m (nbr-step4 (step4 x))))))
;;    :rule-classes nil)

 (defthm run-w1-sat-run-w-def
   (equal (run-w1 s)
          (if (haltedp s) s (run-w1 (step s))))
   :hints
   (("subgoal 1" :expand (clocked-run-w1 s (nbr-steps-to-halt s)))
    ("subgoal 1.2'"
     :use ((:instance
	    clocked-run-w1-step
	    (s (step s))
	    (n (+ -1 (nbr-steps-to-halt s)))
	    (m (nbr-steps-to-halt (step s)))))))
   :rule-classes :definition)
 ) ;; end encapsulate

;; (defthm
;;   f4a-a=b
;;   (equal (f4a (a))
;;          (b))
;;   :rule-classes nil
;;   :hints (("Goal"
;;            :by (:functional-instance
;;                 f4-a=b
;;                 (f4 f4a)))
;;           ("Goal'"
;;            :by f4a-f4-def)))

(defthm prog-is-correct-with-run-w1
  (let* ((s (modify nil
		    :pc 0
		    :locals local-vars
		    :stack s0
		    :program '((load x)      ;; 0
			       (call sq)     ;; 1
			       (call fact)   ;; 2
			       (load x)      ;; 3
			       (call fact)   ;; 4
			       (call sq)     ;; 5
			       (call max)    ;; 6
			       (store y)     ;; 7
			       (halt))       ;; 8
		    :defs (list *sq-def*
				*max-def*
				*fact-def*)))
	 (x (binding 'x (locals s))))
    (implies (and (integerp x)
		  (>= x 0))
	     (equal (run-w1 s)
		    (modify s
			    :pc 8
			    :locals (bind 'y (max (! (sq x))
						  (sq (! x)))
					  (locals s))))))
  :hints (("Goal"
	   :in-theory (disable step haltedp run-w1)
	   :use (:functional-instance
		 prog-is-correct-with-run-w
		 (run-w run-w1)))))

;; (defthm
;;   recursion-halts
;;   (test4 (step4n (a)(nbr-step4 (a))))
;;   :hints (("Goal"
;;            :use f4a-a=b)))

(defthm prog-halts
  (let* ((s (modify nil
		    :pc 0
		    :locals local-vars
		    :stack s0
		    :program '((load x)      ;; 0
			       (call sq)     ;; 1
			       (call fact)   ;; 2
			       (load x)      ;; 3
			       (call fact)   ;; 4
			       (call sq)     ;; 5
			       (call max)    ;; 6
			       (store y)     ;; 7
			       (halt))       ;; 8
		    :defs (list *sq-def*
				*max-def*
				*fact-def*)))
	 (x (binding 'x (locals s)))
	 (n (nfix (nbr-steps-to-halt s))))
    (implies (and (integerp x)
		  (>= x 0))
	     (and (haltedp (run s n))
		  (integerp n)
		  (>= n 0))))
  :hints (("Goal"
	   :in-theory (e/d (run)(run-opener step haltedp))
	   :use prog-is-correct-with-run-w1)))

(defthm prog-is-correct-with-run
  (let* ((s (modify nil
		    :pc 0
		    :locals local-vars
		    :stack s0
		    :program '((load x)      ;; 0
			       (call sq)     ;; 1
			       (call fact)   ;; 2
			       (load x)      ;; 3
			       (call fact)   ;; 4
			       (call sq)     ;; 5
			       (call max)    ;; 6
			       (store y)     ;; 7
			       (halt))       ;; 8
		    :defs (list *sq-def*
				*max-def*
				*fact-def*)))
	 (x (binding 'x (locals s)))
	 (n (nfix (nbr-steps-to-halt s))))
    (implies (and (integerp x)
		  (>= x 0))
	     (equal (run s n)
		    (modify s
			    :pc 8
			    :locals (bind 'y (max (! (sq x))
						  (sq (! x)))
					  (locals s))))))
  :hints (("Goal"
           :in-theory (disable run-opener haltedp prog-halts
			       prog-is-correct-with-run-w)
	   :use (prog-halts
		 prog-is-correct-with-run-w
		 (:instance
		  run-w-run
		  (s (modify nil
			     :pc 0
			     :locals local-vars
			     :stack s0
			     :program '((load x)      ;; 0
					(call sq)     ;; 1
					(call fact)   ;; 2
					(load x)      ;; 3
					(call fact)   ;; 4
					(call sq)     ;; 5
					(call max)    ;; 6
					(store y)     ;; 7
					(halt))       ;; 8
			     :defs (list *sq-def*
					 *max-def*
					 *fact-def*)))
		  (n (nfix (nbr-steps-to-halt (modify nil
						      :pc 0
						      :locals local-vars
						      :stack s0
						      :program '((load x)      ;; 0
								 (call sq)     ;; 1
								 (call fact)   ;; 2
								 (load x)      ;; 3
								 (call fact)   ;; 4
								 (call sq)     ;; 5
								 (call max)    ;; 6
								 (store y)     ;; 7
								 (halt))       ;; 8
						      :defs (list *sq-def*
								  *max-def*
								  *fact-def*)))))
		  )))))
