;;; This is a supporting file for Chapter 11, "Using Macros to Mimic
;;; VHDL", by Dominique Borrione, Philippe Georgelin, and Vanderlei
;;; Rodrigues, in "Computer-Aided Reasoning: ACL2 Case Studies",
;;; edited by M. Kaufmann, P. Manolios, J Moore (Kluwer, 2000,
;;; p.167-182).

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;; fact-proof.lisp
;;;
;;; This file contains proofs for the validation of fact.lisp
;;; August 17, 1999
;;; The path to the arithmetic book has to be adjusted according
;;; to each installation
;;; ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "ACL2")

(include-book "../../../arithmetic/top")

(include-book "fact")

(defthm insert-value_consp
  (implies (consp st)
	   (consp (insert-value n new_value st))))

(defthm length_insert-value
  (equal (len (insert-value n new_value st))
	 (len st)))

;;; These two theorems allow to decompose insert-value in later proofs

(defthm lemma_nth_insert-value1
  (implies (and (integerp n) (<= 0 n) (consp st) (< n (len st)))
	   (equal (nth n (insert-value n val st))
		  val)))

(defthm lemma_nth_insert-value2
  (implies (and (integerp n) (<= 0 n)
		(< n (len st))
		(not (equal n m)))
	   (equal (nth n (insert-value m val st))
		  (nth n st))))

; ------------------------------------------
;;; Basic properties on fact.doit-cycle
; ------------------------------------------

(defthm len_fact.doit-cycle
  (equal (len (fact.doit-cycle st))
	 (len st)))

; ------------------------------------------
;   State properties about fact.doit-cycle
; ------------------------------------------

(defthm fact.doit-cycle_not_modified
  (implies (and (equal (len st) 20)
		(member i '(0 1 5 6 14 16)))
	   (equal (nth i (fact.doit-cycle st))
		  (nth i st))))

(defthm startmult_not_modified1
  (implies (and (equal (len st) 20)
		(equal (nth 17 st) 1)
		(equal (nth 8 st) 0)
		(not (equal (nth 18 st) 1)))
	   (not (equal (nth 8 (fact.doit-cycle st))
		       1))))

;;;  result+ takes the value of doit.f or not after one cycle of fact.doit-cycle

(defthm lemma_fact.doit-cycle1
  (implies (equal (len st) 20)
	   (equal (nth 10 (fact.doit-cycle st))
		  (if (equal (nth 17 st) 1)
		      (if (equal (nth 18 st) 1)
			  (nth 19 st)
			(nth 10 st))
		    (nth 10 st)))))

;;; The value of 'done+ is equal to 1 after one cycle of fact.doit-cycle
;;; if doit.r is equal to 1

(defthm lemma_fact.doit-cycle2
  (implies (equal (len st) 20)
	   (equal (nth 11 (fact.doit-cycle st))
		  (if (equal (nth 17  st) 1)
		      (if (equal (nth 18 st) 1)
			  1
			(nth 11  st))
		    (nth 11 st)))))

;;; The value of 'op1+ is equal to 'doit.r if doit.r is not equal
;;; to 1 and 'doit.mystate is equal to 1

(defthm lemma_fact.doit-cycle3
  (implies (equal (len st) 20)
	   (equal (nth 12 (fact.doit-cycle st))
		  (if (equal (nth 17 st) 1)
		      (if (equal (nth 18 st) 1)
			  (nth 12 st)
			(nth 18 st))
		    (nth 12 st)))))

;;; The value of 'op2+ is equal to 'doit.f if doit.r is not equal
;;; to 1 and 'doit.mystate is equal to 1

(defthm lemma_fact.doit-cycle4
  (implies (equal (len st) 20)
	   (equal (nth 13 (fact.doit-cycle st))
		  (if (equal (nth 17 st) 1)
		      (if (equal (nth 18 st) 1)
			  (nth 13 st)
			(nth 19 st))
		    (nth 13 st)))))

;;; The value of 'startmult+ can be equal to 1 or 0 after one cycle
;;; of fact.doit-cycle

(defthm len-consp
  (implies (< 0 (len st))
	   (consp st)))

(defthm lemma_fact.doit-cycle5
  (implies (equal (len st) 20)
	   (equal (nth 15 (fact.doit-cycle st))
		  (if (equal (nth 17 st) 1)
		      (if (equal (nth 18 st) 1)
			  (nth 15 st)
			1)
		    (if (equal (nth 17 st) 2)
			(if (equal (nth 9 st) 1)
			    0
			  (nth 15 st))
		      (nth 15 st))))))

;;; The value of 'doit.r can be equal to (1- doit.r) or
;;; arg

(defthm lemma_fact.doit-cycle6
  (implies (equal (len st) 20)
	   (equal (nth 18 (fact.doit-cycle st))
		  (if (equal (nth 17 st) 2)
		      (if (equal (nth 9 st) 1)
			  (1- (nth 18 st))
			(nth 18 st))
		    (if (equal (nth 17 st) 0)
			(nth 0 st)
		      (nth 18 st))))))

;;; The value of doir.f can be equal to resmult or 1 after one cycle
;;; of fact.doit-cycle

(defthm lemma_fact.doit-cycle7
  (implies (equal (len st) 20)
	   (equal (nth 19 (fact.doit-cycle st))
		  (if (equal (nth 17 st) 2)
		      (if (equal (nth 9  st) 1)
			  (nth 7 st)
			(nth 19 st))
		    (if (equal (nth 17 st) 0)
			1
		      (nth 19 st))))))

;;; Lemma about new values of doit.mystate after one cycle
;;; of fact.doit-cycle

(defthm lemma_fact.doit-cycle8
  (implies (equal (len st) 20)
	   (equal (nth 17 (fact.doit-cycle st))
		  (if (equal (nth 17 st) 0)
		      (if (equal (nth 1 st) 1) 1 0)
		    (if (equal (nth 17 st) 1)
			(if (equal (nth 18 st) 1) 0 2)
		      (if (equal (nth 17 st) 2)
			  (if (equal (nth 9  st) 1)
			      1 2)
			(nth 17 st)))))))

; ------------------------------------------
;;; Basic properties of fact.multiplier-cycle
; ------------------------------------------

(defthm len_fact.multiplier-cycle
  (equal (len (fact.multiplier-cycle st))
	 (len st)))

; ------------------------------------------
;   State properties about fact.multiplier-cycle
; ------------------------------------------

(defthm fact-multiplier-cycle_not_modified
  (implies (and (equal (len st) 20)
		(member i '(0 1 10 11 12 13 15 17 18 19)))
	   (equal (nth i (fact.multiplier-cycle st))
		  (nth i st))))

(defthm endmult+_takes_startmult
  (implies (equal (len st) 20)
	   (equal (nth 16 (fact.multiplier-cycle st))
		  (nth 8 st))))

;;; resmult+ takes the result of (* op1 op2)

(defthm lemma_fact.multiplier-cycle1
   (implies (equal (len st) 20)
            (equal (nth 14 (fact.multiplier-cycle st))
                   (if (equal (nth 8 st) 1)
                       (* (nth 5 st) (nth 6 st))
                       (nth 14 st)))))

; ------------------------------------------
;;; Basic properties about fact-cycle
; ------------------------------------------

(defthm length_fact-cycle_lemma
              (equal (len (fact-cycle st))
                     (len st))
     :hints (("Goal"
            :in-theory (disable fact.multiplier-cycle fact.doit-cycle))))

; ------------------------------------------
;   State properties about fact-cycle
; ------------------------------------------

(defthm start_not_modified3
  (implies (and (equal (len st) 20)
		(member i '(0 1)))
	   (equal (nth i (fact-cycle st))
		  (nth i st)))
  :hints (("Goal"
	   :in-theory (disable fact.doit-cycle fact.multiplier-cycle))))

;;; This lemma introduces rewriting rules on the updating of signals

(defthm lemma_update-signals
  (implies (equal (len st) 20)
	   (and (equal (nth 3 (fact-cycle st))
		       (nth 10 (fact-cycle st)))
		(equal (nth 4 (fact-cycle st))
		       (nth 11 (fact-cycle st)))
		(equal (nth 5 (fact-cycle st))
		       (nth 12 (fact-cycle st)))
		(equal (nth 6 (fact-cycle st))
		       (nth 13 (fact-cycle st)))
		(equal (nth 7 (fact-cycle st))
		       (nth 14 (fact-cycle st)))
		(equal (nth 8 (fact-cycle st))
		       (nth 15 (fact-cycle st)))
		(equal (nth 9 (fact-cycle st))
		       (nth 16 (fact-cycle st)))))
  :hints (("Goal"
	   :in-theory (disable fact.doit-cycle fact.multiplier-cycle))))

;;; The value of op1+ after one cycle of simulation

(defthm lemma_fact-cycle3
   (implies (equal (len st) 20)
            (equal (nth 12 (fact-cycle st))
                   (if (equal (nth 17 st) 1)
                       (if (equal (nth 18 st) 1)
                           (nth 12 st)
                           (nth 18 st))
                       (nth 12 st))))
 :hints (("Goal"
           :in-theory (disable fact.doit-cycle fact.multiplier-cycle))))

;;; The value of op2+ after one cycle of simulation

(defthm lemma_fact-cycle4
   (implies (equal (len st) 20)
            (equal (nth 13 (fact-cycle st))
                   (if (equal (nth 17 st) 1)
                       (if (equal (nth 18 st) 1)
                           (nth 13 st)
                           (nth 19 st))
                       (nth 13 st))))
:hints (("Goal"
           :in-theory (disable fact.doit-cycle fact.multiplier-cycle))))

;;; The value of startmult+ after one cycle of simulation

(defthm lemma_fact-cycle5
   (implies (equal (len st) 20)
            (equal (nth 15 (fact-cycle st))
                   (if (equal (nth 17 st) 1)
                       (if (equal (nth 18 st) 1)
                           (nth 15 st)
                           1)
                       (if (equal (nth 17 st) 2)
                           (if (equal (nth 9 st) 1)
                               0
                               (nth 15 st))
                           (nth 15 st)))))
  :hints (("Goal"
           :in-theory (disable fact.doit-cycle fact.multiplier-cycle))))

;;; The value of doit.r after one cycle of simulation

(defthm lemma_fact-cycle6
   (implies (equal (len st) 20)
            (equal (nth 18 (fact-cycle st))
                   (if (equal (nth 17 st) 2)
                       (if (equal (nth 9 st) 1)
                           (1- (nth 18 st))
                           (nth 18  st))
                       (if (equal (nth 17 st) 0)
                           (nth 0 st)
                           (nth 18 st)))))
  :hints (("Goal"
           :in-theory (disable fact.doit-cycle fact.multiplier-cycle))))

;;; The value of doit.f after one cycle of simulation

(defthm lemma_fact-cycle7
  (implies (equal (len st) 20)
	   (equal (nth 19 (fact-cycle st))
		  (if (equal (nth 17 st) 2)
		      (if (equal (nth 9 st) 1)
			  (nth 7 st)
			(nth 19 st))
		    (if (equal (nth 17 st) 0)
			1
		      (nth 19 st)))))
  :hints (("Goal"
           :in-theory (disable fact.doit-cycle fact.multiplier-cycle))))

;;; The value of doit.mystate after one cycle of simulation

(defthm  lemma_fact-cycle8
  (implies (equal (len st) 20)
	   (equal (nth 17 (fact-cycle st))
		  (if (equal (nth 17 st) 0)
		      (if (equal (nth 1 st) 1) 1 0)
		    (if (equal (nth 17 st) 1)
			(if (equal (nth 18 st) 1) 0 2)
		      (if (equal (nth 17 st) 2)
			  (if (equal (nth 9 st) 1)
			      1 2)
			(nth 17 st))))))
  :hints (("Goal"
           :in-theory (disable fact.doit-cycle fact.multiplier-cycle))))

;;; The value of resmult+ after one cycle of simulation

(defthm intermed1
  (implies (and (equal (len st) 20)
		(equal (nth 8 (fact.doit-cycle st)) 1)
		(not (equal (nth 8 st) 1)))
	   (equal (* (nth 5 st) (nth 6 st))
		  (nth 14 st))))

(defthm intermed2
  (implies (and (equal (len st) 20)
		(not (equal (nth 8 (fact.doit-cycle st)) 1))
		(equal (nth 8 st) 1))
	   (equal (nth 14 st)
		  (* (nth 5 st) (nth 6 st)))))

(defthm lemma_fact-cycle9
  (implies (equal (len st) 20)
	   (equal (nth 14 (fact-cycle st))
		  (if (equal (nth 8 st) 1)
		      (* (nth 5 st) (nth 6 st))
		    (nth 14 st))))
  :hints (("Goal"
           :in-theory (disable fact.doit-cycle fact.multiplier-cycle))))

;;; The value of endmult+

(defthm lemma_fact-cycle10
  (implies (equal (len st) 20)
	   (equal (nth 16 (fact-cycle st))
		  (nth 8 (fact.doit-cycle st))))
  :hints (("Goal"
           :in-theory (disable fact.doit-cycle fact.multiplier-cycle))))

; -----------------------------------------------------
;;; This function represents one step of computation ;;;
;;; A basic computation takes 3 simulation cycles    ;;;
; -----------------------------------------------------

(defun computation-step (st)
    (fact-cycle (fact-cycle (fact-cycle st))))

; ------------------------------------------
;;; Basics properties
; ------------------------------------------

(defthm length_computation-step_lemma
  (equal (len (computation-step st))
	 (len st))
  :hints (("Goal"
	   :in-theory (disable fact-cycle))))

; ------------------------------------------
;   State properties about computation-step
; ------------------------------------------

;;; The value of doit.mystate after one cycle of computation

(defthm inter1
  (implies (and (equal (len st) 20)
		(equal (nth 17 st) 1)
		(equal (nth 8 st) 0)
		(not (equal (nth 18 st) 1)))
	   (equal (nth 8 (fact.doit-cycle (fact-cycle st)))
		  1)))

(defthm lemma_computation1
  (implies (and (equal (len st) 20)
		(equal (nth 17 st) 1)
		(equal (nth 8 st) 0))
	   (equal (nth 17 (computation-step st))
		  (if (equal (nth 18 st) 1)
		      (if (equal (nth 1 st) 1)
			  (if (equal (nth 0 st) 1)
			      0
			    2)
			0)
		    1)))
  :hints (("Goal"
	   :in-theory (disable fact-cycle fact.doit-cycle fact.multiplier-cycle))))

;;; The value of startmult after one cycle of computation

(defthm lemma_computation2
  (implies (and (equal (len st) 20)
		(equal (nth 17 st) 1)
		(equal (nth 8 st) 0)
		(not (equal (nth 18 st) 1)))
	   (equal (nth 8 (computation-step st))
		  0))
  :hints (("Goal"
	   :in-theory (disable fact-cycle  fact.doit-cycle fact.multiplier-cycle))))

;;; The value of doit.r after one cycle of simulation

(defthm lemma_computation4
  (implies (and (equal (len st) 20)
		(equal (nth 17 st) 1)
		(equal (nth 8 st) 0))
	   (equal (nth 18 (computation-step st))
		  (if (equal (nth 18 st) 1)
		      (nth 0 st)
		    (1- (nth 18 st)))))
  :hints (("Goal"
	   :in-theory (disable fact-cycle))))

;;; The value of doit.f after one cycle of computation

(defthm lemma_computation5
  (implies (and (equal (len st) 20)
		(equal (nth 17 st) 1)
		(equal (nth 8 st) 0))
	   (equal (nth 19 (computation-step st))
		  (if (equal (nth 18 st) 1)
		      1
		    (* (nth 18 st) (nth 19 st)))))
  :hints (("Goal"
	   :in-theory (disable fact-cycle))))

; ---------------------------------------------------------------------
;;; This function runs recursively and calls computation-step on doit.r
; ---------------------------------------------------------------------

(defun execute (st)
  (declare (xargs :measure (nfix (nth 18 st))
                  :hints (("Goal"
			   :in-theory (disable computation-step)))))
  (if (and (integerp (nth 18 st))
	   (equal (len st) 20)
	   (equal (nth 17 st) 1)
	   (equal (nth 8 st) 0))
      (if (< (nth 18 st) 2)
          (nth 19 st)
	(execute (computation-step st)))
    st))

;;;  Example :
;;;  ACL2 !>(execute '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 7 1))
;;;  5040

(defun factorial (n)
  (if (zp n)
      1
    (* n (factorial (1- n)))))

; ---------------------------------------------------------------------
;;;  Final correctness theorem
; ---------------------------------------------------------------------

(defthm equivalence_fact_execute
  (implies (and (integerp (nth 18 st))
		(equal (len st) 20)
		(equal (nth 17 st) 1)
		(equal (nth 8 st) 0)
		(<= 2  (nth 18 st)))
	   (equal (execute st)
		  (* (nth 19 st)
		     (factorial (nth 18 st)))))
  :hints (("Goal"
	   :in-theory (disable computation-step))))

