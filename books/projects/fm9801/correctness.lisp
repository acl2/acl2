;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; correctness.lisp: 
; Author  Jun Sawada, University of Texas at Austin
;
;  This book provides the proof of our correctness criteria.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "ACL2")

(include-book "MAETT-lemmas")
(include-book "wk-inv")
(include-book "invariant-proof")

(deflabel begin-exintr)
; This file contains the high level proof of our correctness criterion.
;
; Index
;   Def of various predicates.
;    map-inputs
;    zero-intr-lst
;    exintr-free-p
;    MT-len MT-num-commit-insts
;    num-insts
;    MT-all-retired-p
;   Lemmas related to input signal mapping and number of instructions.
;   Lemmas about ISA-stepn-fetched-from and ISA-self-modify-p
;   Invariant Proofs
;     inv-initial-MT
;     inv-stepn
;    MA-flushed-implies-MT-all-retired-p and lemmas about MT-all-retired-p
;    flushed-MA-=-MT-final-ISA
;      with matching lemma of individual MA components
;    exintr-correctness-criteria
;    correctness-criteria

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Construction of Witness functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; We construct the ISA input sequence for the final theorem from the
; initial MA state and MA input sequence.  MT-exintr-lst
; extracts an input sequence from the MAETT, by collecting values at
; INST-exintr? field of each MAETT entry. Function map-inputs first
; constructs the MAETT for the final MA state and then extracts
; external interrupt signals from it.
(defun trace-exintr-lst (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace)
      nil
      (cons (ISA-input (INST-exintr? (car trace)))
	    (trace-exintr-lst (cdr trace)))))

(defun MT-exintr-lst (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-exintr-lst (MT-trace MT)))

(in-theory (disable MT-exintr-lst))

; The witness function for the corresponding ISA sequence. 
(defun map-inputs (MA sigs-lst n)
  (declare (xargs :guard (and (MA-state-p MA) (MA-input-listp sigs-lst)
			      (integerp n) (<= 0 n))))
  (MT-exintr-lst (MT-stepn (init-MT MA) MA sigs-lst n)))

(in-theory (disable map-inputs))

; MT-exintr-lst constructs a list of external interrupt input signals
; for all instructions in the MAETT, while another function
; MT-inputs-for-committed extracts external input signal for only
; committed instructions in a MAETT.  Since instructions commit in
; order, inputs-for-committed returns an initiating sublist of the
; input sequence which would be returned by MT-exintr-lst.  When all
; the instructions in a MAETT are committed, inputs-for-committed and
; MT-exintr-lst return the same input list.
(defun trace-inputs-for-committed (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace)
      nil
      (if (or (commit-stg-p (INST-stg (car trace)))
	      (retire-stg-p (INST-stg (car trace))))
	  (cons (ISA-input (INST-exintr? (car trace)))
		(trace-inputs-for-committed (cdr trace)))
	  nil)))

(defun MT-inputs-for-committed (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-inputs-for-committed (MT-trace MT)))

(in-theory (disable MT-inputs-for-committed))

; Each ISA input contains a bit indicating whether an external
; interrupt occurs during the execution of a current instruction; bit
; 1 indicates that an external interrupt takes place in this cycle
; while 0 corresponds to normal execution is performed. zero-intr-lst
; returns a list of n 0's, which is the input signal sequence that
; makes the ISA run without external interrupts.
(defun zero-intr-lst (n)
  (declare (xargs :guard (and (integerp n) (<= 0 n))))
  (if (zp n) nil (cons (ISA-input 0) (zero-intr-lst (1- n)))))

; A bit-level predicate to check whether a list of MA inputs contains
; no external interrupts at the MA level.
(defun exintr-free-p (sigs-lst)
  (declare (xargs :guard (and (MA-input-listp sigs-lst))))
  (if (endp sigs-lst)
      T
      (and (b1p (b-not (MA-input-exintr (car sigs-lst))))
	   (exintr-free-p (cdr sigs-lst)))))

(defun trace-num-commit-insts (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace)
      0
    (if (or (retire-stg-p (INST-stg (car trace)))
	    (commit-stg-p (INST-stg (car trace))))
	(1+ (trace-num-commit-insts (cdr trace)))
      0)))
      
; MT-num-commit-insts returns the number of committed instruction in
; a MAETT.  More precisely, it is the number of consecutively committed
; instructions from the beginning of a MAETT.
; 
; Note that MT-num-commit-insts and MT-len return the same number
; for a MAETT whose instructions are all retired.
(defun MT-num-commit-insts (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-num-commit-insts (MT-trace MT)))

; MT-len returns the number of instructions in a MAETT
(defun MT-len (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (len (MT-trace MT)))

(in-theory (disable MT-len))

; The witness function.
;
; Num-insts returns the number of instructions which are completely or
; partially executed by the MA during the n cycle execution from an
; initial state MA.  If the MA state after n clock cycles is flushed,
; num-insts returns the exact number of instructions that have been
; completely executed. 
;  
; It first constructs the MAETT for the MA state after n clock cycles, 
; and then count the instructions in the MAETT.
(defun num-insts (MA sigs-lst n)
  (declare (xargs :guard (and (MA-state-p MA) (MA-input-listp sigs-lst)
			      (integerp n) (<= 0 n)
			      (<= n (len sigs-lst)))
; Matt K. mod: Avoid :measure for non-recursive definition.
		  ;; :measure (nfix n)
                  ))
  (MT-len (MT-stepn (init-MT MA) MA sigs-lst n)))

(in-theory (disable MT-num-commit-insts num-insts))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Following are lemmas about the number of instructions in a MAETT
;;; and input sequence  extracted from a MAETT.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(encapsulate nil 
(local
 (defthm len-MT-exintr-lst-help
     (equal (len (trace-exintr-lst trace))
	    (len trace))))

; The length of the input sequence returned by MT-exintr-lst.
(defthm len-MT-exintr-lst
    (equal (len (MT-exintr-lst MT)) (MT-len MT))
  :hints (("goal" :do-not-induct t
		  :in-theory (enable MT-exintr-lst MT-len))))

)

(encapsulate nil
(local
(defthm len-trace-inputs-for-committed
    (equal (len (trace-inputs-for-committed trace))
	   (trace-num-commit-insts trace))))

; The length of the input sequence returned by MT-inputs-for-committed.
(defthm len-MT-inputs-for-committed
    (equal (len (MT-inputs-for-committed MT)) (MT-num-commit-insts MT))
  :hints (("Goal" :in-theory
		  (enable MT-inputs-for-committed MT-num-commit-insts))))
)

(defthm MT-exintr-lst-init-MT
    (equal (MT-exintr-lst (init-MT MA)) nil)
  :hints (("Goal" :in-theory (enable MT-exintr-lst))))

; The number of instructions at the initial MAETT is 0.
(defthm MT-len-init-MT
    (equal (MT-len (init-MT MA)) 0)
  :hints (("Goal" :in-theory (enable MT-len))))

; The number of instructions recorded in a MAETT may decrease as
; partially executed instructions can be abandoned.  However,
; committed instructions are never eliminated from a MAETT, so the
; number of committed instructions in a MAETT never decreases.
(encapsulate nil
(local
 (defthm MT-num-commit-insts-MT-step->=-MT-num-commit-insts-help
     (<= (trace-num-commit-insts trace)
	 (trace-num-commit-insts (step-trace trace MT MA sigs ISA spc smc)))))

; Monotonicity of the committed instructions. 
(defthm MT-num-commit-insts-MT-step->=-MT-num-commit-insts
    (<= (MT-num-commit-insts MT)
	(MT-num-commit-insts (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable MT-step MT-num-commit-insts)
		  :do-not-induct t))
  :rule-classes :linear)
)

(defthm MT-num-commit-insts-MT-stepn->=-MT-num-commit-insts
    (<= (MT-num-commit-insts MT)
	(MT-num-commit-insts (MT-stepn MT MA sigs-lst n)))
  :rule-classes :linear)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Properties about ISA-stepn-fetches-from and
;;;; ISA-self-modify-p.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(local
 (defun induction-scheme1 (ISA ol1 ol2 n1 n2)
   (if (or (zp n1) (zp n2)) (list ISA ol1 ol2 n1 n2)
       (induction-scheme1 (ISA-step ISA (car ol1))
			  (cdr ol1) (cdr ol2) (1- n1) (1- n2)))))

; Suppose n1 <= n2.  If the ISA fetches an instruction from a certain
; address, addr, during the first n1 steps, it certainly fetches the
; same instruction in the first n2 steps.
(defthm ISA-stepn-fetches-from-head-p
    (implies (and (head-p sl1 sl2) (<= n1 n2)
		  (<= n1 (len sl1)) (<= n2 (len sl2))
		  (integerp n1) (integerp n2)
		  (ISA-stepn-fetches-from addr ISA sl1 n1))
	     (ISA-stepn-fetches-from addr ISA sl2 n2))
  :hints (("goal" :induct (induction-scheme1 ISA sl1 sl2 n1 n2))))

; N step version.
(defthm ISA-self-modify-p-head-p
    (implies (and (head-p sl1 sl2) (<= n1 n2)
		  (integerp n1) (integerp n2)
		  (<= n1 (len sl1)) (<= n2 (len sl2))
		  (ISA-self-modify-p ISA sl1 n1))
	     (ISA-self-modify-p ISA sl2 n2))
  :hints (("goal" :induct (induction-scheme1 ISA sl1 sl2 n1 n2)
		  :restrict ((ISA-stepn-fetches-from-head-p
			      ((sl1 (cdr sl1)) (n1 (1- n1))))))))

(encapsulate nil
(local  
(defthm head-p-MT-inputs-for-committed-MT-step-help
    (head-p (trace-inputs-for-committed trace)
	    (trace-inputs-for-committed (step-trace trace
						    MT MA sigs ISA spc smc)))))

; The input sequence for the committed instructions is extended when
; the MAETT is updated.  Head-p is a predicate to check if a list is
; an initiating sublist.
(defthm head-p-MT-inputs-for-committed-MT-step
    (head-p (MT-inputs-for-committed MT)
	    (MT-inputs-for-committed (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (e/d (MT-inputs-for-committed MT-step)
				  (head-p trace-inputs-for-committed))
		  :do-not-induct t)))
)

; If a MAETT contains a self-modifying sequence of committed
; instructions, the updated MAETT also contains a self-modifying
; sequence of committed instructions.  This is because committed
; instructions will never undo a commit, and the sequence of committed
; instructions in an MAETT only grows, but never shrinks.
(defthm ISA-self-modify-p-MT-step
    (implies (and (MAETT-p MT)
		  (MA-state-p MA)
		  (ISA-self-modify-p ISA
				     (MT-inputs-for-committed MT)
				     (MT-num-commit-insts MT)))
	     (ISA-self-modify-p ISA
				(MT-inputs-for-committed (MT-step MT MA sigs))
				(MT-num-commit-insts (MT-step MT MA sigs))))
  :hints (("Goal" :restrict ((ISA-self-modify-p-head-p
			      ((sl1  (MT-inputs-for-committed MT))
			       (n1  (MT-num-commit-insts MT))))))))

; N-step version of the previous theorem.
(defthm ISA-self-modify-p-MT-stepn
    (implies (and (MAETT-p MT)
		  (MA-state-p MA)
		  (MA-input-listp sigs-lst)
		  (ISA-self-modify-p ISA
				     (MT-inputs-for-committed MT)
				     (MT-num-commit-insts MT)))
	     (ISA-self-modify-p ISA
			(MT-inputs-for-committed (MT-stepn MT MA sigs-lst n))
			(MT-num-commit-insts (MT-stepn MT MA sigs-lst n)))))

(encapsulate nil
(local
(defthm ISA-stepn-fetches-INST-if-INST-is-committed
    (implies (and (weak-inv MT)
		  (MAETT-p MT) 
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (member-equal i trace)
		  (INST-p i)
		  (trace-all-commit-before i trace)
		  (or (commit-stg-p (INST-stg i))
		      (retire-stg-p (INST-stg i)))
		  (not (b1p (INST-exintr? i)))
		  (equal (ISA-pc (INST-pre-ISA i)) addr))
	     (ISA-stepn-fetches-from addr
				     (INST-pre-ISA (car trace))
				     (trace-inputs-for-committed trace)
				     (trace-num-commit-insts trace)))
  :rule-classes
  ((:rewrite :corollary 
	     (implies (and (weak-inv MT)
			   (MAETT-p MT) 
			   (member-equal i trace)
			   (INST-listp trace) (INST-p i)
			   (subtrace-p trace MT)
			   (trace-all-commit-before i trace)
			   (or (commit-stg-p (INST-stg i))
			       (retire-stg-p (INST-stg i)))
			   (not (b1p (INST-exintr? i)))
			   (equal (INST-pre-ISA (car trace)) ISA)
			   (equal (ISA-pc (INST-pre-ISA i)) addr))
		      (ISA-stepn-fetches-from addr
					  ISA
					  (trace-inputs-for-committed trace)
					  (trace-num-commit-insts trace)))))
  :hints (("goal" :induct t
		  :in-theory (enable ISA-FETCHES-FROM))
	  (when-found (ISA-stepn-FETCHES-FROM ADDR
					      (INST-PRE-ISA (CAR (CDR TRACE)))
               (TRACE-INPUTS-FOR-COMMITTED (CDR TRACE))
               (TRACE-NUM-COMMIT-INSTS (CDR TRACE)))
		      (:cases ((consp (cdr trace))))))))

(local
(defthm ISA-self-modify-p-if-MT-modify-p-help
    (implies (and (weak-inv MT)
		  (subtrace-p trace MT)
		  (MAETT-p MT)
		  (consp trace)
		  (member-equal i trace)
		  (INST-p i)
		  (INST-listp trace)
		  (or (commit-stg-p (INST-stg i))
		      (retire-stg-p (INST-stg i)))
		  (trace-all-commit-before i trace)
		  (trace-modify-p i trace))
	     (ISA-self-modify-p (INST-pre-ISA (car trace))
				(trace-inputs-for-committed trace)
				(trace-num-commit-insts trace)))
  :hints (("goal" :induct t
		  :in-theory (e/d (INST-MODIFY-P)
				  (ISA-chained-trace-p)))
	  (when-found (ISA-self-modify-P
		       (INST-PRE-ISA (CAR (CDR TRACE)))
		       (TRACE-INPUTS-FOR-COMMITTED (CDR TRACE))
		       (TRACE-NUM-COMMIT-INSTS (CDR TRACE)))
		      (:cases ((consp (cdr trace))))))
  :rule-classes nil))

(local
(defthm ISA-self-modify-p-if-MT-modify-p
    (implies (and (weak-inv MT)
		  (MAETT-p MT)
		  (MT-modify-p i MT)
		  (INST-in i MT)
		  (INST-p i)
		  (or (commit-stg-p (INST-stg i))
		      (retire-stg-p (INST-stg i)))
		  (MT-all-commit-before i MT))
	     (ISA-self-modify-p (MT-init-ISA MT)
				(MT-inputs-for-committed MT)
				(MT-num-commit-insts MT)))
  :hints (("Goal" :in-theory (enable INST-in MT-modify-p
				     MT-inputs-for-committed
				     MT-all-commit-before
				     MT-num-commit-insts)
		  :cases ((consp (MT-trace MT)))
		  :do-not-induct t)
	  (when-found-multiple
	   ((CONSP (MT-TRACE MT))
	    (ISA-SELF-MODIFY-P (MT-INIT-ISA MT)
			       (TRACE-INPUTS-FOR-COMMITTED (MT-TRACE MT))
			       (TRACE-NUM-COMMIT-INSTS (MT-TRACE MT))))
	   (:use
	    (:instance ISA-self-modify-p-if-MT-modify-p-help
		       (trace (MT-trace MT)))))))
) ; local

(local
(encapsulate nil
(local
 (defthm commit-stg-MI1-if-all-commit-before-MI2-help
    (implies (and (distinct-member-p trace)
		  (member-in-order MI1 MI2 trace)
		  (trace-all-commit-before MI2 trace)
		  (not (commit-stg-p (INST-stg MI1))))
	     (retire-stg-p (INST-stg MI1)))
   :hints (("Goal" :in-theory (enable member-in-order*)))))

(defthm commit-stg-MI1-if-all-commit-before-MI2
    (implies (and (weak-inv MT)
		  (INST-in-order-p MI1 MI2 MT)
		  (MT-all-commit-before MI2 MT)
		  (not (commit-stg-p (INST-stg MI1))))
	     (retire-stg-p (INST-stg MI1)))
  :Hints (("Goal" :in-theory (enable INST-in-order-p MT-all-commit-before
				     weak-inv MT-distinct-INST-p)))
  :rule-classes nil)
))

(local
(encapsulate nil
(local
(defthm all-commit-before-MI1-if-all-commit-before-MI2-help
     (implies (and (distinct-member-p trace)
		   (member-in-order MI1 MI2 trace)
		   (trace-all-commit-before MI2 trace))
	      (trace-all-commit-before MI1 trace))
  :hints (("Goal" :in-theory (enable member-in-order*)))))

(defthm all-commit-before-MI1-if-all-commit-before-MI2
     (implies (and (weak-inv MT)
		   (INST-in-order-p MI1 MI2 MT)
		   (MT-all-commit-before MI2 MT))
	      (MT-all-commit-before MI1 MT))
  :hints (("Goal" :in-theory (enable MT-all-commit-before INST-in-order-p
				     weak-inv MT-distinct-INST-p)))
   :rule-classes nil)
))
 
(local
(defthm ISA-self-modify-p-if-INST-modified-help
    (implies (and (weak-inv MT)
		  (MAETT-p MT) 
		  (trace-correct-modified-flgs-p trace MT 0)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (member-equal i trace)
		  (INST-p i)
		  (MT-all-commit-before i MT)
		  (or (commit-stg-p (INST-stg i))
		      (retire-stg-p (INST-stg i)))
		  (b1p (INST-modified? i)))
	     (ISA-self-modify-p (MT-init-ISA MT)
				(MT-inputs-for-committed MT)
				(MT-num-commit-insts MT)))
  :hints (("Goal" :induct t)
	  (when-found (TRACE-CORRECT-MODIFIED-FLGS-P (CDR TRACE) MT '1)
	      (:use ((:instance commit-stg-MI1-if-all-commit-before-MI2
				(MI1 (car trace)) (MI2 i))
		     (:instance all-commit-before-MI1-if-all-commit-before-MI2
				(MI1 (car trace)) (MI2 i))))))
  :rule-classes nil))
				  

(local
 (defthm ISA-self-modify-p-if-INST-modified
     (implies (and (weak-inv MT)
		   (MAETT-p MT)
		   (INST-in i MT)
		   (INST-p i)
		   (or (commit-stg-p (INST-stg i))
		       (retire-stg-p (INST-stg i)))
		   (MT-all-commit-before i MT)
		   (b1p (INST-modified? i)))
	      (ISA-self-modify-p (MT-init-ISA MT)
				 (MT-inputs-for-committed MT)
				 (MT-num-commit-insts MT)))
   :Hints (("Goal" :in-theory (enable weak-inv
				      CORRECT-modified-FLGS-P
				      INST-in)
	   :use (:instance ISA-self-modify-p-if-INST-modified-help
			   (trace (MT-trace MT)))
	   :do-not-induct t))))

(local
(defthm trace-all-commit-before-cadr-help
    (implies (and (distinct-member-p trace2)
		  (tail-p trace trace2)
		  (trace-all-commit-before (car trace) trace2)
		  (consp trace)
		  (or (commit-stg-p (INST-stg (car trace)))
		      (retire-stg-p (INST-stg (car trace)))))
	     (trace-all-commit-before (cadr trace) trace2))))

(local
(defthm trace-all-commit-before-cadr
    (implies (and (weak-inv MT)
		  (MAETT-p MT)
		  (subtrace-p trace MT)
		  (consp trace)
		  (trace-all-commit-before (car trace) (MT-trace MT))
		  (or (commit-stg-p (INST-stg (car trace)))
		      (retire-stg-p (INST-stg (car trace)))))
	     (trace-all-commit-before (cadr trace) (MT-trace MT)))
  :hints (("Goal" :in-theory (enable weak-inv MT-distinct-INST-p
				     subtrace-p))))
)

(local
(defthm ISA-self-modify-p-if-MT-CMI-help
    (implies (and (weak-inv MT)
		  (MAETT-p MT)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (implies (consp trace) (MT-all-commit-before (car trace) MT))
		  (not (ISA-self-modify-p (MT-init-ISA MT)
					  (MT-inputs-for-committed MT)
					  (MT-num-commit-insts MT))))
	     (not (trace-CMI-p trace)))
  :hints (("goal" :in-theory (enable MT-CMI-p
				     committed-p
				     MT-all-commit-before)
	  :restrict ((ISA-self-modify-p-if-INST-modified
		      ((i (car trace)))))
	  :induct t))))

; MT-CMI-p and ISA-self-modify-p present the same concept of
; self-modification in different forms.  MT-CMI-p determines whether a
; MAETT records a self-modifying program.  ISA-self-modify-p
; determines from the initial ISA state whether the ISA executes
; self-modifying instructions in a certain number of steps.  The lemma
; states that, whenever MT-CMI-p is true suggesting the MAETT contains
; a self-modifying program, the ISA executes self-modifying program.
(defthm ISA-self-modify-p-if-MT-CMI
    (implies (and (weak-inv MT)
		  (MAETT-p MT)
	 	  (not (ISA-self-modify-p (MT-init-ISA MT)
					  (MT-inputs-for-committed MT)
					  (MT-num-commit-insts MT))))
	     (not (MT-CMI-p MT)))
  :hints (("goal" :in-theory (enable MT-CMI-p
				     MT-all-commit-before))))
)

; An initial MAETT does not contain any committed instructions. 
(defthm not-MT-CMI-p-init-MT
    (implies (MA-state-p MA)
	     (not (MT-CMI-p (init-MT MA))))
  :hints (("goal" :in-theory (enable init-MT MT-CMI-p))))

(local
 (defun induction-scheme3 (ISA trace)
   (if (endp trace)
       (list ISA trace)
       (induction-scheme3 (ISA-step ISA (ISA-input (INST-exintr? (car trace))))
			  (cdr trace)))))

(local
(defthm ISA-stepn-fetches-from-trace-num-commit-insts
    (implies (not (ISA-stepn-fetches-from addr ISA
					  (trace-exintr-lst trace)
					  (len trace)))
	     (not (ISA-stepn-fetches-from addr ISA
					  (trace-inputs-for-committed trace)
					  (trace-num-commit-insts trace))))
  :hints (("Goal" :induct (induction-scheme3 ISA trace)))))

(local
(defthm ISA-self-modify-p-trace-num-commit-insts
    (implies (not (ISA-self-modify-p ISA (trace-exintr-lst trace)
				     (len trace)))
	     (not (ISA-self-modify-p ISA
				     (trace-inputs-for-committed trace)
				     (trace-num-commit-insts trace))))
  :hints (("Goal" :induct (induction-scheme3 ISA trace)))))

; Since (MT-len MT) >= (MT-num-commit-insts MT),
; the self-modification of the program that occurs during the first
; (MT-num-commit-insts MT) cycles of ISA execution occurs
; in the first (MT-len MT) cycles of execution.

(defthm ISA-self-modify-p-MT-inputs-for-committed
    (implies (not (ISA-self-modify-p ISA (MT-exintr-lst MT)
				     (MT-len MT)))
	     (not (ISA-self-modify-p ISA (MT-inputs-for-committed MT)
				     (MT-num-commit-insts MT))))
  :hints (("Goal" :in-theory (enable MT-inputs-for-committed
				     MT-num-commit-insts
				     MT-exintr-lst
				     MT-len))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Invariant Proofs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
; These lemmas are proved in invariant-proof.lisp
; We need two major lemmas to prove our correctness criterion.

; Initial execution trace satisfies invariants.
(defthm inv-initial-MT
    (implies (and (MA-state-p MA) (flushed-p MA))
	     (inv (init-MT MA) MA)))

; The invariants are preserved as far as no modified
; instructions are committed.  This proof takes an extensive 
; verification analysis.
(defthm inv-step
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (MA-input-p sigs)
		  (not (MT-CMI-p (MT-step MT MA sigs))))
	     (inv (MT-step MT MA sigs)
			 (MA-step MA sigs)))
  :hints (("Goal" :in-theory (enable inv)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (MAETT-p MT)
			   (MA-state-p MA)
			   (MA-input-p sigs)
			   (not (inv (MT-step MT MA sigs)
					    (MA-step MA sigs))))
		      (MT-CMI-p (MT-step MT MA sigs))))))

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; stepn version of invariant lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Stepn version of weak-inv lemma.
(defthm weak-inv-stepn
    (implies (and (weak-inv MT)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (MA-input-listp sigs-lst)
		  (<= n (len sigs-lst)))
	     (weak-inv (MT-stepn MT MA sigs-lst n)))
  :hints (("goal" :in-theory (enable MA-stepn))))

; Stepn version of strong invariant lemma.
; Strong invariants are preserved during n cycles of MA execution as
; far as no modified instructions are committed during the execution.
(defthm inv-stepn
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (MA-input-listp sigs-lst)
		  (<= n (len sigs-lst))
		  (not (MT-CMI-p (MT-stepn MT MA sigs-lst n))))
	     (inv (MT-stepn MT MA sigs-lst n)
		  (MA-stepn MA sigs-lst n)))
  :hints (("goal" :in-theory (enable MA-stepn)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	      (implies (and (inv MT MA)
			    (MAETT-p MT)
			    (MA-state-p MA)
			    (MA-input-listp sigs-lst)
			    (<= n (len sigs-lst))
			    (not (inv (MT-stepn MT MA sigs-lst n)
					     (MA-stepn MA sigs-lst n))))
		       (MT-CMI-p (MT-stepn MT MA sigs-lst n))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  MA-flushed-implies-MT-all-retired-p and other lemmas with MT-all-retied
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(encapsulate nil
(local
(defthm trace-all-retired-implies-not-trace-specultv
    (implies (and (INST-listp trace)
		  (trace-no-specultv-commit-p trace)
		  (trace-all-retired trace))
	     (not (b1p (trace-specultv? trace))))
  :hints (("goal" :in-theory (enable invariants-def lift-b-ops)))))

;; An MAETT whose instructions are all retired does not
;; contain any speculative instruction.
(defthm MT-all-retired-p-implies-not-MT-specultv-help
    (implies (and (MAETT-p MT)
		  (no-specultv-commit-p MT)
		  (MT-all-retired-p MT))
	     (not (MT-specultv-p MT)))
  :hints (("Goal"  :in-theory (enable invariants-def MT-specultv?
				      MT-specultv-p MT-specultv?
				      MT-all-retired-p))))

(defthm MT-all-retired-p-implies-not-MT-specultv
    (implies (and (MAETT-p MT)
		  (inv MT MA)
		  (MT-all-retired-p MT))
	     (not (MT-specultv-p MT)))
  :hints (("Goal"  :in-theory (enable inv))))
)

(encapsulate  nil
(local
(defthm MT-all-retired-p-implies-not-MT-self-modify-help
    (implies (and (not (trace-CMI-p trace))
		  (trace-all-retired trace))
	     (equal (trace-self-modify? trace) 0))))

(defthm MT-all-retired-p-implies-not-MT-self-modify
    (implies (and (not (MT-CMI-p MT))
		  (MT-all-retired-p MT))
	     (not (MT-self-modify-p MT)))
  :hints (("Goal" :in-theory (enable MT-all-retired-p MT-self-modify?
				     MT-self-modify-p
				     MT-self-modify?
				     MT-CMI-p))))
)

(encapsulate nil
(local
(defthm MT-CMI-p-implies-MT-self-modify-help
    (implies (trace-CMI-p trace)
	     (equal (trace-self-modify? trace) 1))))

(defthm MT-CMI-p-implies-MT-self-modify
    (implies (MT-CMI-p MT)
	     (MT-self-modify-p MT))
  :hints (("goal" :in-theory (enable MT-CMI-p
				     MT-self-modify-p
				     MT-self-modify?))))
)

; If an MA state is flushed, the corresponding MAETT contains only
; retired instructions.
; 
; Note: consistent-MA-p is one of the conjuncts used in the
; definition of inv.
(defthm MA-flushed-implies-INST-retired
    (implies (and (INST-p i)
		  (MA-state-p MA)
		  (flushed-p MA)
		  (INST-inv i MA)
		  (consistent-MA-p MA))
	     (retire-stg-p (INST-stg i)))
  :hints (("goal" :in-theory (enable inst-inv-def
				     MA-flushed-def lift-b-ops
				     consistent-rob-p-forward)))
  :rule-classes
  ((:rewrite :corollary (implies (and (INST-p i)
				      (MA-state-p MA)
				      (flushed-p MA)
				      (not (retire-stg-p (INST-stg i)))
				      (consistent-MA-p MA))
				 (not (INST-inv i MA))))))

;; Using the previous lemma, we can prove that all the instructions in an
;; MAETT are retired if the corresponding MA is flushed. 
(encapsulate nil
(local
(defthm MA-flushed-implies-trace-all-retired
    (implies (and (trace-INST-inv trace MA)
		  (consistent-MA-p MA)
		  (INST-listp trace)
		  (MA-state-p MA)
		  (flushed-p MA))
	     (trace-all-retired trace))))

(defthm MA-flushed-implies-MT-all-retired-p
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (flushed-p MA))
	     (MT-all-retired-p MT))
  :hints (("goal" :In-theory (enable inv weak-inv
				     MT-INST-inv
				     MT-all-retired-p))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Proof of flushed-MA-=-MT-final-ISA
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; In this section, we prove flushed-MA-=-MT-final-ISA, which shows
;; that a final MA state is equivalent to the ISA state after executing
;; m instructions, where m = (MT-len MT). 
; 
;; We prove the lemma by showing that the states of individual
;; programmer visible components are the same in the MA and ISA.
; 
(defthm ISA-pc-ISA-stepn-MT-pc-help
    (implies (ISA-chained-trace-p trace ISA)
	     (equal (ISA-pc (ISA-stepn ISA
				       (trace-exintr-lst trace)
				       (len trace)))
		    (trace-pc trace (ISA-pc ISA))))
  :hints (("goal" :in-theory (enable ISA-stepn))))

; This theorem shows that the pc in ISA_m is correctly represented 
; by (MT-pc MT) if all instructions are retired.
(defthm ISA-pc-ISA-stepn-MT-pc
    (implies (weak-inv MT)
	     (equal (ISA-pc (ISA-stepn (MT-init-ISA MT)
				       (MT-exintr-lst MT)
				       (MT-len MT)))
		    (MT-pc MT)))
  :hints (("goal" :in-theory (enable MT-pc MT-exintr-lst MT-len
				     weak-inv ISA-step-chain-p
				     MT-all-retired-p))))
		   
(defthm ISA-RF-ISA-stepn-MT-RF-help
    (implies (and (ISA-chained-trace-p trace ISA)
		  (trace-all-retired trace))
	     (equal (ISA-RF (ISA-stepn ISA
				       (trace-exintr-lst trace)
				       (len trace)))
		    (trace-RF trace (ISA-RF ISA))))
  :hints (("goal" :in-theory (enable ISA-stepn))))

; This theorem shows that the RF in ISA_m is correctly represented 
; by (MT-RF MT) if all instructions are retired.
(defthm ISA-RF-ISA-stepn-MT-RF
    (implies (and (weak-inv MT)
		  (MT-all-retired-p MT))
	     (equal (ISA-RF (ISA-stepn (MT-init-ISA MT)
				       (MT-exintr-lst MT)
				       (MT-len MT)))
		    (MT-RF MT)))
  :hints (("goal" :in-theory (enable MT-RF MT-exintr-lst MT-len
				     weak-inv ISA-step-chain-p
				     MT-all-retired-p))))

(defthm ISA-SRF-ISA-stepn-MT-SRF-help
    (implies (and (ISA-chained-trace-p trace ISA)
		  (trace-all-retired trace))
	     (equal (ISA-SRF (ISA-stepn ISA
					(trace-exintr-lst trace)
					(len trace)))
		    (trace-SRF trace (ISA-SRF ISA))))
  :hints (("goal" :in-theory (enable ISA-stepn))))

; This theorem shows that the SRF in ISA_m is correctly represented 
; by (MT-SRF MT) if all instructions are retired.
(defthm ISA-SRF-ISA-stepn-MT-SRF
    (implies (and (weak-inv MT)
		  (MT-all-retired-p MT))
	     (equal (ISA-SRF (ISA-stepn (MT-init-ISA MT)
					(MT-exintr-lst MT)
					(MT-len MT)))
		    (MT-SRF MT)))
  :hints (("goal" :in-theory (enable MT-SRF MT-exintr-lst MT-len
				     weak-inv ISA-step-chain-p
				     MT-all-retired-p))))

(defthm ISA-mem-ISA-stepn-MT-mem-help
    (implies (and (ISA-chained-trace-p trace ISA)
		  (trace-all-retired trace))
	     (equal (ISA-mem (ISA-stepn ISA
					(trace-exintr-lst trace)
					(len trace)))
		    (trace-mem trace (ISA-mem ISA))))
  :hints (("goal" :in-theory (enable ISA-stepn))))

; This theorem shows that the memory in ISA_m is correctly represented 
; by (MT-mem MT) if all instructions are retired.
(defthm ISA-mem-ISA-stepn-MT-mem
    (implies (and (weak-inv MT)
		  (MT-all-retired-p MT))
	     (equal (ISA-mem (ISA-stepn (MT-init-ISA MT)
					(MT-exintr-lst MT)
					(MT-len MT)))
		    (MT-mem MT)))
  :hints (("goal" :in-theory (enable MT-mem MT-exintr-lst MT-len
				     weak-inv ISA-step-chain-p
				     MT-all-retired-p))))

(encapsulate nil
(local
(defthm MT-pc-MA-pc
    (implies (and (inv MT MA)
		  (not (MT-specultv-p MT))
		  (not (MT-self-modify-p MT)))
	     (equal (MT-pc MT) (MA-pc MA)))
  :hints (("goal" :in-theory (enable inv pc-match-p)))))

(local
(defthm MT-RF-MA-RF
    (implies (inv MT MA)
	     (equal (MT-RF MT) (MA-RF MA)))
  :hints (("goal" :in-theory (enable inv RF-match-p)))))

(local
(defthm MT-SRF-MA-SRF
    (implies (inv MT MA)
	     (equal (MT-SRF MT) (MA-SRF MA)))
  :hints (("goal" :in-theory (enable inv SRF-match-p)))))

(local
(defthm MT-mem-MA-mem
    (implies (inv MT MA)
	     (equal (MT-mem MT) (MA-mem MA)))
  :hints (("goal" :in-theory (enable inv mem-match-p)))))
	     

;; Suppose the final state MA is flushed, and MA and its MAETT MT
;; satisfies the invariants.  Furthermore, assume there is no
;; committed instruction in MT which is self-modified by the program.
;; Then the projection of MA is equal to the post-ISA of the last
;; instruction in MT.  In other words, state MA is equivalent to the
;; final ISA state after executing the last instruction in MT

;; The right hand side represents the post-ISA of the last instruction.
;; Instead of representing the state as:
;; (post-ISA (car (last (MT-trace MT)))),
;; we expressed it as in the lemma.  The idea is as follows.  In a
;; well-formed MAETT, pre-ISA and post-ISA builds a chain of ISA state 
;; transitions, as specified by a weak invariant ISA-step-chain-p.
;; If I_i and I_j are instructions in a well-formed MAETT, and I_i
;; immediately follows I_j.  Then
;; (pre-ISA I_j) = (post-ISA I_i) = (ISA-step (pre-ISA I_i) (INST-exintr? I_i))
;; Hence we can calculate the post-ISA of n'th entry of a well-formed
;; MAETT by  (ISA-stepn (pre-ISA (car MT)) intr-list n),  where
;; intr-list = (MT-exintr-lst MT).
(defthm flushed-MA-=-MT-final-ISA
    (implies (and (inv MT MA)
		  (not (MT-CMI-p MT))
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (flushed-p MA))
	     (equal (proj MA)
		    (ISA-stepn (MT-init-ISA MT)
			       (MT-exintr-lst MT)
			       (MT-len MT))))
  :hints (("goal" :use (:instance ISA-extensionality
				  (s1 (proj MA))
				  (s2 (ISA-stepn (MT-init-ISA MT)
						 (MT-exintr-lst MT)
						 (MT-len MT)))))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; MAIN THEOREM
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; This is a main result of our verification work.  The
;; microarchitectural design satisfies a commutative diagram which
;; shows the equivalence of MA implementation and ISA spec; in one
;; path of the diagram, we run the MA design for n clock cycles and
;; then project the final MA state to ISA machine; on the other path,
;; we project the initial MA state to an ISA state, then run the
;; machine for (num-insts MA sigs-lst n) cycles with an appropriate
;; input sequence give by (map-inputs MA sigs-lst n).  Num-insts
;; returns the number of instructions in the MAETT, which is actually
;; the number of instructions executed and committed in the n
;; clock-cycle MA execution.  The appropriate input sequence for the
;; ISA state transitions is constructed by function (map-inputs MA
;; sigs-lst n).
(defthm exintr-correctness-criteria
    (implies (and (MA-state-p MA)
 		  (MA-input-listp sigs-lst)
		  (<= n (len sigs-lst))
		  (flushed-p MA)
		  (flushed-p (MA-stepn MA sigs-lst n))
		  (not (ISA-self-modify-p (proj MA)
					  (map-inputs MA sigs-lst n)
					  (num-insts MA sigs-lst n))))
	     (equal (proj (MA-stepn MA sigs-lst n))
		    (ISA-stepn (proj MA)
			       (map-inputs MA sigs-lst n)
			       (num-insts MA sigs-lst n))))
  :hints (("Goal" :in-theory (e/d (map-inputs num-insts)
				  (inv-initial-MT
				   inv-stepn))
		  :use ((:instance inv-initial-MT)
			(:instance inv-stepn (MT (init-MT MA))))
		  :restrict ((flushed-MA-=-MT-final-ISA
			      ((MA (MA-STEPN MA SIGS-LST N)))))
		  :do-not-induct t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Proof of correctness-criteria without interrupts.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm trace-exintr-lst-step-trace
    (implies (and (MA-state-p MA)
		  (MA-input-p sigs)
		  (MAETT-p MT)
		  (not (b1p (MA-input-exintr sigs)))
		  (not (b1p (exintr-flag? MA)))
		  (equal (trace-exintr-lst trace)
			 (zero-intr-lst (len trace))))
     (equal (trace-exintr-lst (step-trace trace MT MA sigs ISA spc smc))
	    (zero-intr-lst (len (step-trace trace MT MA sigs ISA spc smc))))))
					    
(defthm MT-exintr-lst-MT-step
    (implies (and (MA-state-p MA) (MA-input-p sigs)
		  (MAETT-p MT)
		  (not (b1p (MA-input-exintr sigs)))
		  (not (b1p (exintr-flag? MA)))
		  (equal (MT-exintr-lst MT)
			 (zero-intr-lst (MT-len MT))))
	     (equal (MT-exintr-lst (MT-step MT MA sigs))
		    (zero-intr-lst
		     (MT-len (MT-step MT MA sigs)))))
  :hints (("Goal" :in-theory (enable MT-step MT-exintr-lst
				     MT-len))))

(defthm MT-exintr-lst-MT-stepn-induction
    (implies (and (MA-state-p MA) (MA-input-listp sigs-lst)
		  (MAETT-p MT)
		  (not (b1p (exintr-flag? MA)))
		  (exintr-free-p sigs-lst)
		  (equal (MT-exintr-lst MT)
			 (zero-intr-lst (MT-len MT))))
	     (equal (MT-exintr-lst (MT-stepn MT MA sigs-lst n))
		    (zero-intr-lst
		     (MT-len (MT-stepn MT MA sigs-lst n)))))
  :hints (("Goal" :induct (MT-stepn MT MA sigs-lst n)
		  :in-theory (enable lift-b-ops))))

;; The following lemma shows that the ISA input sequence constructed
;; from function map-inputs is a sequence of sigs-lst with 0's if the
;; MA input sequence contains no external interrupts.
(defthm map-MA-input-lst-=-zero-intr-lst
    (implies (and (MA-state-p MA)
		  (MA-input-listp sigs-lst)
		  (flushed-p MA)
		  (flushed-p (MA-stepn MA sigs-lst n))
		  (exintr-free-p sigs-lst))
	     (equal (map-inputs MA sigs-lst n)
		    (zero-intr-lst (num-insts MA sigs-lst n))))
  :hints (("Goal" :in-theory (enable map-inputs num-insts
				     MA-flushed? lift-b-ops)
		  :do-not-induct t)))

;; The next correctness theorem is an instantiation of the theorem
;; exintr-correctness-criteria.  The lemma shows the equivalence
;; between MA and ISA state transitions, provided that the MA state
;; transitions are not externally interrupted.  The corresponding ISA
;; execution are not externally interrupted, either.
(defthm correctness-criteria
    (implies (and (MA-state-p MA)
 		  (MA-input-listp sigs-lst)
		  (<= n (len sigs-lst))
		  (flushed-p MA)
		  (flushed-p (MA-stepn MA sigs-lst n))
		  (exintr-free-p sigs-lst)
		  (not (ISA-self-modify-p (proj MA)
					  (zero-intr-lst
					   (num-insts MA sigs-lst n))
					  (num-insts MA sigs-lst n))))
	     (equal (proj (MA-stepn MA sigs-lst n))
		    (ISA-stepn (proj MA)
			       (zero-intr-lst
				(num-insts MA sigs-lst n))
			       (num-insts MA sigs-lst n))))
  :hints (("Goal" :do-not-induct t)))
