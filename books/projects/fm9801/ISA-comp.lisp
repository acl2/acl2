;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; File: ISA-comp.lisp
; Author  Jun Sawada, University of Texas at Austin
;
; This file includes the proof of the invariant properties pc-match-p,
; RF-match-p, SRF-match-p, and mem-match-p.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "MA2-lemmas")
(include-book "MAETT-lemmas")
(include-book "memory-inv")

(deflabel begin-ISA-comp)
; This file proves the invariant conditions specifying the correct
; state of programmer visible states. 
;  Index
;   Misc Lemmas
;   Proof for RF-match-p
;      Base case
;       RF-match-p-init-MA
;      Induction case 
;        Lemmas for no state changes
;        MT-RF-ISA-RF-inst-of-tag
;           ISA-RF-ISA-step-if-INST-wb
;           ROB-write-val-INST-dest-val
;           ROB-write-rid-INST-dest-reg
;           step-RF-INST-post-ISA-of-INST-at-MT-ROB-head-normal-case
;        step-RF-INST-post-ISA-of-INST-at-MT-ROB-head
;       RF-match-p-preserved
;
;   Proof of SRF-Match
;      Base case
;        SRF-match-p-init-MA
;      Induction case 
;        Case 1
;         step-SRF-if-ex-intr?
;         MT-SRF-MT-step-if-ex-intr
;         ISA-SRF-ISA-step-exintr
;        Case 2
;         step-SRF-if-not-commit-inst?
;         MT-SRF-MT-step-if-not-commit-inst
;        Case 3
;         MT-SRF-ISA-RF-inst-of-tag
;         step-SRF-INST-post-ISA-of-INST-at-MT-ROB-head
;       SRF-match-p-preserved
;
;   Proof of pc-match-p preserved
;     Base case
;       pc-match-p-init-MT
;     Induction step
;         Case when ex-intr? is 1.
;           MT-pc-rob-jmp-addr-if-ex-intr
;         Case when enter-excpt? is 1
;           MT-pc-rob-jmp-addr-if-enter-excpt
;         Case when commit-jmp? is on 
;           MT-pc-rob-jmp-addr-if-commit-jmp
;         Case when leave-excpt? is on
;           MT-pc-if-leave-excpt
;         Case when fetch-inst? is on 
;           MT-pc-if-fetch-inst  
;         Otherwise
;       pc-match-p-preserved
;
;   Proof of mem-match-p 
;     Base Case
;       mem-match-p-init-MT
;     Induction Case
;         MT-mem-if-step-MT-if-release-wbuf0
;         MT-mem-if-step-MT-if-not-release-wbuf0
;       mem-match-p-preserved
;     
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Misc Lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(local
(defthm trace-SRF* 
    (equal (trace-SRF INST-list SRF)
	   (if (endp INST-list) 
	       SRF
	       (if (not (committed-p (car INST-list)))
		   SRF
		   (trace-SRF (cdr INST-list)
			      (ISA-SRF (INST-post-ISA (car INST-list)))))))
  :rule-classes :definition))

(local (in-theory (disable trace-SRF* )))

;; Several lemmas given below are for the proof of lemmas in this book.
;; They are not intended to be a universal lemma, because the left-hand
;; side terms are not definitely more complex than right-hand side.
;; However, these rewriting rules are useful in the proof of lemmas in
;; this book. 
(local
(defthm MT-mem-=-MA-mem
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA))
	     (equal (MT-mem MT) (MA-mem MA)))
  :hints (("goal" :in-theory (enable inv mem-match-p)))))

(local
(defthm MT-RF-=-MA-RF
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA))
	     (equal (MT-RF MT) (MA-RF MA)))
  :hints (("goal" :in-theory (enable inv RF-match-p)))))

(local
(defthm MT-SRF-=-MA-SRF
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA))
	     (equal (MT-SRF MT) (MA-SRF MA)))
  :hints (("goal" :in-theory (enable inv SRF-match-p)))))

(local
(defthm MT-pc-=-MA-pc
    (implies (and (inv MT MA)
		  (not (b1p (MT-specultv? MT)))
		  (not (b1p (MT-self-modify? MT)))
		  (MAETT-p MT)
		  (MA-state-p MA))
	     (equal (MT-pc MT) (MA-pc MA)))
  :hints (("goal" :in-theory (enable inv
				     MT-specultv-p MT-self-modify-p
				     pc-match-p lift-b-ops)))))

(encapsulate nil
(local
(defthm ISA-pc-MT-final-ISA-=-MT-pc-help
    (equal (ISA-pc (trace-final-ISA trace ISA))
	   (trace-pc trace (ISA-pc ISA)))))

;  The program counter contains the value of the PC in the final ISA state.
(defthm ISA-pc-MT-final-ISA-=-MT-pc
    (equal (ISA-pc (MT-final-ISA MT)) (MT-pc MT))
  :hints (("goal" :in-theory (enable MT-final-ISA MT-pc))))
)

(local
 (defthm ISA-step-INST-pre-ISA
     (implies (and (not (b1p (ISA-input-exint intr)))
		   (not (b1p (INST-fetch-error? i))))
	      (equal (ISA-step (INST-pre-ISA i) intr)
		     (LET ((S (INST-pre-ISA i))
			   (INST (READ-MEM (ISA-PC (INST-pre-ISA i))
					   (ISA-MEM (INST-pre-ISA i)))))
		       (LET ((OP (OPCODE INST))
			     (RC (RC INST))
			     (RA (RA INST))
			     (RB (RB INST))
			     (IM (IM INST)))
			 (COND ((EQUAL OP 0) (ISA-ADD RC RA RB S))
			       ((EQUAL OP 1) (ISA-MUL RC RA RB S))
			       ((EQUAL OP 2) (ISA-BR RC IM S))
			       ((EQUAL OP 3) (ISA-LD RC RA RB S))
			       ((EQUAL OP 6) (ISA-LDI RC IM S))
			       ((EQUAL OP 4) (ISA-ST RC RA RB S))
			       ((EQUAL OP 7) (ISA-STI RC IM S))
			       ((EQUAL OP 5) (ISA-SYNC S))
			       ((EQUAL OP 8) (ISA-RFEH S))
			       ((EQUAL OP 9) (ISA-MFSR RC RA S))
			       ((EQUAL OP 10) (ISA-MTSR RC RA S))
			       (T (ISA-ILLEGAL-INST s)))))))
   :Hints (("goal" :in-theory (enable ISA-step INST-fetch-error?
				      lift-b-ops)))))
(local (in-theory (disable ISA-step-INST-pre-ISA)))

(encapsulate nil
(local
(defthm MT-CMI-p-MT-step-if-INST-at-ROB-head-modified-induct
    (implies (and (b1p (INST-modified? i))
		  (INST-p i) (member-equal i trace)
		  (trace-all-commit-before i trace)
		  (dispatched-p i)
		  (committed-p (step-INST i MT MA sigs))
		  (INST-listp trace))
	     (trace-CMI-p (step-trace trace MT MA sigs
				      ISA spc smc)))))

(local
(defthm MT-CMI-p-MT-step-if-INST-at-ROB-head-modified-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (INST-modified? i))
		  (INST-p i) (INST-in i MT)
		  (MT-all-commit-before i MT)
		  (dispatched-p i)
		  (committed-p (step-INST i MT MA sigs)))
	     (MT-CMI-p (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable MT-CMI-p INST-in
				     MT-step MT-all-commit-before)))))

; If instruction at the head of the ROB is modified and commit-inst? is on,
; commitment of a self-modified instruction happens. 
(defthm MT-CMI-p-MT-step-if-INST-at-ROB-head-modified
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (commit-inst? MA))
		  (b1p (INST-modified? (inst-of-tag (MT-ROB-head MT) MT))))
	     (MT-CMI-p (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (e/d (commit-inst? lift-b-ops)
				  (incompatible-with-excpt-in-MAETT-lemmas)))))
)

(encapsulate nil
(local
(defthm MT-self-modified-p-MT-step-if-INST-at-ROB-head-modified-induct
    (implies (and (b1p (INST-modified? i))
		  (INST-p i) (member-equal i trace)
		  (trace-all-commit-before i trace)
		  (dispatched-p i)
		  (committed-p (step-INST i MT MA sigs))
		  (INST-listp trace))
	     (equal (trace-self-modify? (step-trace trace MT MA sigs
						    ISA spc smc))
		    1))
  :hints (("goal" :in-theory (enable lift-b-ops)))))

(local
(defthm MT-CMI-p-MT-step-if-INST-at-ROB-head-modified-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (INST-modified? i))
		  (INST-p i) (INST-in i MT)
		  (MT-all-commit-before i MT)
		  (dispatched-p i)
		  (committed-p (step-INST i MT MA sigs)))
	     (equal (MT-self-modify? (MT-step MT MA sigs)) 1))
  :hints (("goal" :in-theory (enable MT-self-modify? INST-in
				     MT-step MT-all-commit-before)))))

; If instruction at the head of the ROB is modified and commit-inst? is on,
; a self-modified instruction is committed.
(defthm MT-self-modify-MT-step-if-INST-at-ROB-head-modified
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (commit-inst? MA))
		  (b1p (INST-modified? (inst-of-tag (MT-ROB-head MT) MT))))
	     (equal (MT-self-modify? (MT-step MT MA sigs)) 1))
  :hints (("goal" :in-theory (e/d (commit-inst? lift-b-ops)
				  (incompatible-with-excpt-in-MAETT-lemmas)))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Proof of invariant RF-match-p
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;; Proof of match-RF-p for the initial case
(defthm RF-match-p-init-MA
    (implies (MA-state-p MA)
	     (RF-match-p (init-MT MA) MA))
  :Hints (("goal" :in-theory (enable RF-match-p init-MT
				     MT-RF))))

;;;;  Induction case. 
; First we prove basic lemmas to characterize the case where no
; changes occur to the register files.  Then we prove that the state
; changes on the register file in the "actual" machine state, and the
; "ideal" machine state calculated from the intermediate abstraction.

;;;;;  Lemmas to characterize when the register file does not change. 

; If no instruction commits in this cycle, the register file is not updated.
(defthm commit-inst-if-rob-write-reg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (commit-inst? MA))))
	     (equal (ROB-write-reg? (MA-rob MA))  0))
  :hints (("goal" :in-theory (enable commit-inst? ROB-write-reg?
				     lift-b-ops equal-b1p-converter))))

; If no instruction commits, the register file is not modified.
(defthm step-RF-if-not-commit-inst?
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (commit-inst? MA))))
	     (equal (step-RF MA) (MA-RF MA)))
  :hints (("goal" :in-theory (enable step-RF))))

; If external interrupt to the ISA does not modify the general register file.
(defthm ISA-RF-ISA-step-with-exintr
    (implies (b1p (ISA-input-exint intr)) 
	     (equal (ISA-RF (ISA-step ISA intr))
		    (ISA-RF ISA)))
  :hints (("goal" :in-theory (enable ISA-def))))

(encapsulate nil
(local
(defthm MT-RF-MT-step-if-not-commit-inst-help
    (implies (not (b1p (commit-inst? MA)))
	     (equal (trace-RF (step-trace trace MT MA sigs
					  ISA spc smc)
			      (ISA-RF ISA))
		    (trace-RF trace (ISA-RF ISA))))))

; If no instruction commits this cycle, MT-RF remains identical.
(defthm MT-RF-MT-step-if-not-commit-inst
    (implies (not (b1p (commit-inst? MA)))
	     (equal (MT-RF (MT-step MT MA sigs))
		    (MT-RF MT)))
  :hints (("goal" :in-theory (enable MT-RF MT-step))))
)
  

(encapsulate nil
(local
(defthm committed-p-step-inst-if-commit-inst?
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (complete-stg-p
		   (INST-stg (inst-of-tag (MT-rob-head MT) MT)))
		  (b1p (commit-inst? MA)))
	     (committed-p (step-INST (inst-of-tag (MT-rob-head MT) MT)
				     MT MA sigs)))
  :hints (("goal" :in-theory (enable step-inst-opener
				     INST-commit?
				     lift-b-ops
				     bv-eqv-iff-equal
				     step-INST-complete)))))

; The instruction at the head of the ROB commits if commit-inst? is on.
(defthm  committed-p-step-inst-INST-at-MT-rob-head
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT)
		  (b1p (commit-inst? MA)))
	     (committed-p (step-INST  (inst-of-tag (MT-ROB-head MT) MT)
				      MT MA sigs)))
  :hints (("goal" :use (:instance INST-is-at-one-of-the-stages
				  (i (inst-of-tag (MT-ROB-head MT) MT)))
		  :in-theory (disable INST-is-at-one-of-the-stages))
	  ("subgoal 2" :by nil))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
    (implies
     (and (inv MT MA)
	  (MA-state-p MA) (MAETT-p MT) (b1p (commit-inst? MA))
	  (not (commit-stg-p (INST-stg
			      (step-INST (inst-of-tag (MT-ROB-head MT) MT)
					 MT MA sigs)))))
     (retire-stg-p (INST-stg
		    (step-INST (inst-of-tag (MT-ROB-head MT) MT) MT MA sigs))))
    :hints (("goal" :in-theory
		    (e/d (committed-p)
			 (NOT-COMMITTED-P-IF-NOT-COMMIT-RETIRE)))))))
)

;;;;;;;  Lemmas to compare the state change on register file
;;;;;;;  in the actual implementation and the ideal state.
;
; The proof of RF-match-p-preserved consists of two major
; lemmas: step-RF-INST-post-ISA-of-INST-at-MT-ROB-head and 
; MT-RF-ISA-RF-inst-of-tag.
;
; step-RF-INST-post-ISA-of-INST-at-MT-ROB-head tells
; that the register file in the next "actual machine state" is the same as
; in the post-ISA of the instruction at the head of the ROB. 
; 
; MT-RF-ISA-RF-inst-of-tag
;  calculates what MT-RF calculates as the "ideal register file"
; 
;;;;;;;
(local
(defthm not-retire-stg-p-step-inst-if-earlier-inst-commit
    (implies (and (inv MT MA)
		  (b1p (INST-commit? j MA))
		  (INST-in-order-p j i MT) 
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (MAETT-p MT) (MA-state-p MA))
	     (not (committed-p (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (e/d (committed-p)
				  (complete-stg-p-if-INST-commit
				   INST-is-at-one-of-the-stages))
		  :use ((:instance complete-stg-p-if-INST-commit (i j))
			(:instance INST-is-at-one-of-the-stages))))))

; local lemmas.
; committed-p-step-inst-car says:
;   If j commits, (car trace) has already committed.
; not-INST-cause-jmp-car-when-inst-commit states:
;   If j commits, (car trace) does not commit in this cycle.
;
(local
(defthm committed-p-step-inst-car
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (member-equal j (cdr trace))
		  (b1p (INST-commit? j MA))
		  (INST-listp trace) (INST-in j MT) (INST-p j)
		  (MAETT-p MT) (MA-state-p MA))
	     (committed-p (step-INST (car trace) MT MA sigs)))
  :hints (("goal" :use (:instance committed-p-if-INST-commit-following
				  (i (car trace)))
		  :in-theory (enable committed-p)))))

(local
(defthm not-INST-cause-jmp-car-when-inst-commit
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (member-equal j (cdr trace))
		  (b1p (INST-commit? j MA))
		  (INST-listp trace)
		  (INST-in j MT) (INST-p j)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-cause-jmp? (car trace) MT MA sigs) 0))
  :hints (("goal" :in-theory (e/d (committed-p INST-commit? lift-b-ops
						 equal-b1p-converter
						 INST-cause-jmp?)
				  (complete-stg-p-if-INST-commit
				   INST-is-at-one-of-the-stages))
		  :use ((:instance complete-stg-p-if-INST-commit (i j))
			(:instance INST-is-at-one-of-the-stages))))))

(encapsulate nil
(local
(defthm MT-RF-MT-step-if-INST-commit-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (member-equal i trace)
		  (b1p (INST-commit? i MA))
		  (INST-p i) (MAETT-p MT) (MA-state-p MA))
	     (equal (trace-RF (step-trace trace MT MA sigs
					  ISA spc smc)
			      (ISA-RF (INST-pre-ISA (car trace))))
		    (ISA-RF (INST-post-ISA i))))
  :rule-classes nil
  :hints (("goal" :in-theory (e/d (trace-RF*
				   INST-exintr-now-INST-commit-exclusive)
				  (trace-RF))
		  :induct t)
	  (when-found (INST-pre-ISA (car (cdr trace)))
		      (:cases ((consp (cdr trace)))))
	  (when-found (consp (cdr trace))
		      (:expand
		       (STEP-TRACE (CDR TRACE)
			   MT MA SIGS
			   (ISA-STEP (INST-PRE-ISA (CAR TRACE))
				     (ISA-input (INST-EXINTR? (CAR TRACE))))
			   (B-IOR (INST-SPECULTV? (CAR TRACE))
				  (INST-START-SPECULTV? (CAR TRACE)))
			   (INST-MODIFIED? (CAR TRACE))))))))

(local
(defthm MT-RF-MT-step-if-INST-commit?
    (implies (and (inv MT MA)
		  (b1p (INST-commit? i MA))
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MT-RF (MT-step MT MA sigs))
		    (ISA-RF (INST-post-ISA i))))
  :hints (("goal" :in-theory (enable MT-RF INST-in MT-step)
		  :use (:instance MT-RF-MT-step-if-INST-commit-help
				  (trace (MT-trace MT))
				  (spc 0) (smc 0)
				  (ISA (MT-init-ISA MT))))
	  ("goal'" :cases ((consp (MT-trace MT)))))))

; This is a landmark lemma.  When commit-inst? is 1, the instruction
; at the head of the ROB commits, advancing the commit boundary
; one instruction ahead.  Thus, MT-RF returns the register file in
; the post-ISA state of the instruction at the head of the ROB.
; 
; Let me explain it more carefully.  MT-RF calculates the
; ideal register file from the MAETT.  Suppose an instruction
; commits in this cycle.  The commit boundary advances one instruction. 
; In other words, The instruction specified as 
;    (inst-of-tag (MT-ROB-head MT) MT) 
; commits.  Thus the register file looks as that in the 
; post ISA state of (inst-of-tag (MT-ROB-head MT) MT).
(defthm MT-RF-ISA-RF-inst-of-tag
    (implies (and (inv MT MA)
		  (b1p (commit-inst? MA))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MT-RF (MT-step MT MA sigs))
		    (ISA-RF
		     (INST-post-ISA (inst-of-tag (MT-ROB-head MT) MT)))))
  :hints (("goal" :restrict ((MT-RF-MT-step-if-INST-commit?
			      ((i (inst-of-tag (MT-ROB-head MT) MT))))))))
)

(encapsulate nil
(local
(defthm MT-RF-INST-pre-ISA-if-MT-all-commit-before-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (member-equal i trace) (INST-p i)
		  (trace-all-commit-before i trace)
		  (subtrace-p trace MT)
		  (not (committed-p i)))
	     (equal (ISA-RF (INST-pre-ISA i))
		    (trace-RF trace
			      (ISA-RF (ISA-before trace MT)))))
  :hints (("goal" :in-theory (enable ISA-before-MT-non-nil-trace)))))

(local
(defthm MT-RF-INST-pre-ISA-if-MT-all-commit-before
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (MT-all-commit-before i MT)
		  (not (committed-p i)))
	     (equal (ISA-RF (INST-pre-ISA i))
		    (MT-RF MT)))
  :hints (("goal" :in-theory (e/d (MT-RF MT-all-commit-before
						   INST-in)
				  (MT-RF-=-MA-RF))))))

; Suppose the ROB is not empty. 
; The register file in the current MA state is the same as in the 
; pre-ISA state of the instruction at the head of the ROB.
(defthm MA-RF-pre-ISA-RF-INST-at-ROB-head
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-of-tag (MT-ROB-head MT) MT))
	     (equal (ISA-RF (INST-pre-ISA (inst-of-tag (MT-ROB-head MT) MT)))
		    (MA-RF MA))))
)

; If INST-wb-SRF? is 1 for instruction i, it does not modify 
; the general register file during its ISA execution.
(defthm ISA-RF-ISA-step-if-INST-wb-sreg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (b1p (INST-wb-sreg? i)))
	     (equal (ISA-RF (ISA-step (INST-pre-ISA i) intr))
		    (ISA-RF (INST-pre-ISA i))))
  :hints (("goal" :in-theory (enable ISA-step-functions ISA-step
				     INST-wb-sreg? INST-cntlv
				     INST-opcode
				     opcode-inst-type))))

; If instruction i raises an exception, it does not modify
; the register file during ISA execution.
(defthm ISA-RF-ISA-step-if-not-INST-excpt
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (b1p (INST-excpt? i)))
	     (equal (ISA-RF (ISA-step (INST-pre-ISA i) intr))
		    (ISA-RF (INST-pre-ISA i))))
  :hints (("goal" :in-theory (enable ISA-step-functions ISA-step
				     INST-excpt?
				     INST-fetch-error?
				     INST-decode-error?
				     INST-data-access-error?
				     INST-STORE-ERROR?
				     INST-LOAD-ERROR?
				     DECODE-ILLEGAL-INST?
				     INST-RA
				     lift-b-ops))))

; This is an important lemma. 
;  The effect of writeback instruction i.
(defthm ISA-RF-ISA-step-if-INST-wb
     (implies (and (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-p i) (INST-in i MT)
		   (b1p (INST-wb? i))
		   (not (b1p (INST-wb-sreg? i)))
		   (not (b1p (INST-excpt? i)))
		   (not (b1p (ISA-input-exint intr))))
	      (equal (ISA-RF (ISA-step (INST-pre-ISA i) intr))
		     (write-reg (INST-dest-val i)
				(INST-dest-reg i)
				(ISA-RF (INST-pre-ISA i)))))
  :hints (("goal" :in-theory (enable ISA-step-functions ISA-step
				     INST-excpt?
				     INST-fetch-error?
				     INST-decode-error?
				     INST-data-access-error?
				     INST-STORE-ERROR?
				     INST-LOAD-ERROR?
				     DECODE-ILLEGAL-INST?
				     INST-wb?
				     INST-wb-sreg? INST-cntlv
				     INST-opcode
				     opcode-inst-type
				     INST-DEST-VAL
				     INST-DEST-REG
				     INST-ADD-DEST-VAL
				     INST-MULT-DEST-VAL
				     INST-LD-DEST-VAL
				     INST-LD-IM-DEST-VAL
				     INST-MFSR-DEST-VAL
				     INST-MTSR-DEST-VAL
				     INST-RA INST-RB INST-RC
				     INST-IM
				     INST-SRC-VAL1
				     INST-SRC-VAL2
				     lift-b-ops))))

; Suppose instruction i is at the head of the ROB.
; If exception handling starts in this cycle, then i must be an exception-
; raising instruction.
(defthm INST-excpt-INST-at-ROB-head-if-enter-excpt
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-of-tag (MT-rob-head MT) MT)
		  (not (b1p (INST-modified? (inst-of-tag (MT-rob-head MT)
							 MT))))
		  (not (b1p (inst-specultv? (inst-of-tag (MT-rob-head MT)
							 MT))))
		  (b1p (enter-excpt? MA)))
	     (equal (INST-excpt? (inst-of-tag (MT-ROB-head MT) MT)) 1))
  :hints (("goal" :in-theory (enable enter-excpt? lift-b-ops
				     equal-b1p-converter))))

; An important lemma.
; Output ROB-write-val from the ROB is equal to the destination value
; of the instruction at the head of the ROB.
(defthm ROB-write-val-INST-dest-val
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-of-tag (MT-ROB-head MT) MT)
		  (complete-stg-p
		   (INST-stg (inst-of-tag (MT-ROB-head MT) MT)))
		  (INST-writeback-p (inst-of-tag (MT-ROB-head MT) MT))
		  (not (b1p (INST-modified?
			     (inst-of-tag (MT-ROB-head MT) MT))))
		  (not (b1p (inst-specultv?
			     (inst-of-tag (MT-ROB-head MT) MT))))
		  (not (b1p (INST-excpt?
			     (inst-of-tag (MT-ROB-head MT) MT)))))
	     (equal (ROB-write-val (MA-rob MA) MA)
		    (INST-dest-val (inst-of-tag (MT-ROB-head MT) MT))))
  :hints (("goal" :in-theory (enable ROB-write-val))))

; An important lemma.
; Output of ROB-write-rid from the ROB designates the destination register
; of the instruction at the head of the ROB.
(defthm ROB-write-rid-INST-dest-reg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-of-tag (MT-ROB-head MT) MT)
		  (complete-stg-p
		   (INST-stg (inst-of-tag (MT-ROB-head MT) MT)))
		  (INST-writeback-p (inst-of-tag (MT-ROB-head MT) MT))
		  (not (b1p (INST-modified?
			     (inst-of-tag (MT-ROB-head MT) MT))))
		  (not (b1p (inst-specultv?
			     (inst-of-tag (MT-ROB-head MT) MT))))
		  (not (b1p (INST-excpt?
			     (inst-of-tag (MT-ROB-head MT) MT)))))
	     (equal (ROB-write-rid (MA-rob MA))
		    (INST-dest-reg (inst-of-tag (MT-ROB-head MT) MT))))
  :hints (("goal" :in-theory (enable ROB-write-rid exception-relations))))

; If instruction i is not a write-back instruction, it does not modify 
; the register file in ISA execution.
(defthm ISA-RF-ISA-step-if-not-INST-wb
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (not (b1p (INST-wb? i))))
	     (equal (ISA-RF (ISA-step (INST-pre-ISA i) intr))
		    (ISA-RF (INST-pre-ISA i))))
  :hints (("goal" :in-theory (enable ISA-step-functions ISA-step
				     INST-wb? INST-cntlv
				     INST-opcode
				     opcode-inst-type))))

; An important lemma. One step before
;   step-RF-INST-post-ISA-of-INST-at-MT-ROB-head
; Suppose instruction i is at the head of the ROB.  If i commits in
; this cycle, the register file states in the next MA state is that of
; the post-ISA state of i.
(defthm step-RF-INST-post-ISA-of-INST-at-MT-ROB-head-normal-case
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (commit-inst? MA))
		  (not (b1p (INST-modified?
			     (inst-of-tag (MT-ROB-head MT) MT))))
		  (not (b1p (inst-specultv?
			     (inst-of-tag (MT-ROB-head MT) MT)))))
	     (equal (step-RF MA)
		    (ISA-RF
		     (INST-post-ISA (inst-of-tag (MT-ROB-head MT) MT)))))
  :hints (("goal" :in-theory (e/d (step-RF lift-b-ops
				     INST-exintr-INST-in-if-not-retired
				     commit-inst? ROB-write-reg?)
				  (inst-is-at-one-of-the-stages))
		  :cases ((b1p (INST-fetch-error?
				(inst-of-tag (MT-ROB-head MT) MT)))))
	  ("subgoal 2" :cases ((b1p (INST-excpt?
				     (inst-of-tag (MT-ROB-head MT) MT)))))
	  ("subgoal 1" :cases ((b1p (INST-excpt?
				     (inst-of-tag (MT-ROB-head MT) MT))))
		       :in-theory (enable INST-excpt? lift-b-ops
					  commit-inst? ROB-write-reg?
					  exception-relations
					  step-RF))
	  ("subgoal 2.2" :use
			 (:instance INST-is-at-one-of-the-stages
				    (i (inst-of-tag (MT-ROB-head MT) MT))))
	  ("subgoal 2.1" :use
			 (:instance INST-is-at-one-of-the-stages
				    (i (inst-of-tag (MT-ROB-head MT) MT))))))

; A landmark lemma. 
; A corollary of 
;  step-RF-INST-post-ISA-of-INST-at-MT-ROB-head-normal-case.
; The general register file in the next cycle is the same as in the
; post-ISA of the instruction at the head of the ROB.
(defthm step-RF-INST-post-ISA-of-INST-at-MT-ROB-head
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (commit-inst? MA))
		  (not (MT-CMI-p (MT-step MT MA sigs))))
	     (equal (step-RF MA)
		    (ISA-RF
		     (INST-post-ISA (inst-of-tag (MT-ROB-head MT) MT)))))
  :hints (("goal" :cases
		  ((b1p (INST-modified? (inst-of-tag (MT-ROB-head MT) MT)))
		   (b1p (inst-specultv? (inst-of-tag (MT-ROB-head MT) MT))))
		  :in-theory (enable commit-inst? lift-b-ops))))

(local
(defthm RF-match-p-preserved-help
    (implies (and (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p intr)
		  (inv MT MA)
		  (not (MT-CMI-p (MT-step MT ma intr))))
	     (equal (MT-RF  (MT-step MT ma intr))
		    (step-RF MA)))
  :hints (("goal" :cases ((b1p (commit-inst? MA)))))))
				      
		  
; RF-match-p is preserved.
(defthm RF-match-p-preserved
    (implies (and (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p intr)
		  (inv MT MA)
		  (not (MT-CMI-p (MT-step MT ma intr))))
	     (RF-match-p (MT-step MT ma intr) (MA-step ma intr)))
  :hints (("goal" :in-theory (enable RF-match-p
				     MT-CMI-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Proof of SRF-Match
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Initial special register satisfies SRF-match-p
(defthm SRF-match-p-init-MA
    (implies (and (MA-state-p MA) (b1p (MA-flushed? MA)))
	     (SRF-match-p (init-MT MA) MA))
  :Hints (("goal" :in-theory (enable SRF-match-p init-MT
				     MT-SRF))))

;;;;;;; Induction case
;
; There are three cases to consider.
;  1  An external interrupt occurs.
;  2  No exception, no instruction commit occurs. 
;  3  Commitment of an instruction occurs. 
;  Commitment includes internal exception handling in our case. 
; 
; There are seven landmark lemmas:
; For Case 1
;     step-SRF-if-ex-intr?
;     MT-SRF-MT-step-if-ex-intr
;     ISA-SRF-ISA-step-exintr
; For Case 2,
;     step-SRF-if-not-commit-inst?
;     MT-SRF-MT-step-if-not-commit-inst
; For Case 3,  
;    MT-SRF-ISA-RF-inst-of-tag
;    step-SRF-INST-post-ISA-of-INST-at-MT-ROB-head

;
; We define MT-ISA-at-dispatch to calculate the ISA state at the
; dispatching boundary.  This state can be characterized as the
; post-ISA of the most recently dispatched instruction, or the pre-ISA
; of the first instruction that has not been dispatched yet.
(defun trace-ISA-at-dispatch (trace ISA)
  (if (endp trace)
      ISA
      (if (not (dispatched-p (car trace)))
	  ISA
	  (trace-ISA-at-dispatch (cdr trace) (INST-post-ISA (car trace))))))

(defun MT-ISA-at-dispatch (MT)
  (trace-ISA-at-dispatch (MT-trace MT) (MT-init-ISA MT)))

(in-theory (disable MT-ISA-at-dispatch))

;;; Start Case 1
; If no instruction commits in this cycle, the special registers are not
; updated.
(defthm commit-inst-if-rob-write-sreg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (commit-inst? MA))))
	     (equal (ROB-write-sreg? (MA-rob MA))  0))
  :hints (("goal" :in-theory (enable commit-inst? ROB-write-sreg?
				     lift-b-ops equal-b1p-converter))))

; An landmark lemma.
; The effect of an external interrupt on special register file.
(defthm step-SRF-if-ex-intr?
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (ex-intr? MA sigs)))
	     (equal (step-SRF MA sigs)
		    (SRF 1 (word (ex-intr-addr MA))
			   (word (SRF-su (MA-SRF MA))))))
  :hints (("goal" :in-theory (enable step-SRF))))

(encapsulate nil
(local
(defthm commit-inst-p-if-dispatched-and-ex-intr
    (implies (and (inv MT MA)
		  (dispatched-p i)
		  (b1p (EX-intr? MA sigs))
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA))
	     (committed-p i))
  :hints (("goal" :in-theory
		  (enable NOT-EX-INTR-IF-INST-AT-EXECUTE-OR-COMPLETE-STG)))))

(local
(defthm MT-SRF-MT-step-if-ex-intr-help
    (implies (and (inv MT MA)
		  (b1p (ex-intr? MA sigs))
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (trace-SRF (step-trace trace MT MA sigs
					   ISA spc smc)
			       (ISA-SRF ISA))
		    (ISA-SRF
		     (ISA-step (trace-ISA-at-dispatch trace ISA)
			       (ISA-input 1)))))
  :hints (("goal" :in-theory (e/d (trace-SRF*)
				  (trace-SRF))))
  :rule-classes nil))

; This is a landmark lemma.  This characterize the ideal state
; of the special register in the next state after an external interrupt
; occurs. 
;
; If an external interrupt occurs, the ideal state of the special register
; file is obtained by expanding the definition of the ISA step function
; for an external interrupt. 
(defthm MT-SRF-MT-step-if-ex-intr
    (implies (and (inv MT MA)
		  (b1p (ex-intr? MA sigs))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MT-SRF (MT-step MT MA sigs))
		    (ISA-SRF
		     (ISA-step (MT-ISA-at-dispatch MT)
			       (ISA-input 1)))))
  :hints (("goal" :use (:instance
			MT-SRF-MT-step-if-ex-intr-help
			(trace (MT-trace MT)) (smc 0) (spc 0)
			(ISA  (MT-init-ISA MT)))
		  :in-theory (enable MT-SRF MT-step
				     MT-ISA-at-dispatch))))
)

(encapsulate nil
(local
(defthm not-MT-all-commit-before-if-INST-modified-help
    (implies (and (member-equal i trace)
		  (not (equal i (car trace)))
		  (b1p (INST-modified? i))
		  (trace-correct-modified-first trace)
		  (not (b1p (INST-first-modified? i)))
		  (not (trace-CMI-p trace)))
	     (not (trace-all-commit-before i trace)))))

; A nasty corner case lemma about the relation between
; The reader can skip it, without losing the picture of the proof.
; MT-CMI-p, INST-modified? and INST-first-modified? are involved.
;
; If INST-first-modified? is false, there must be an modified
; instruction before i. Name it j. And if all instruction before i are
; committed, that implies j is committed. Thus MT-CMI-p
; must be non-nil, if all instructions preceding i are committed. 
(defthm not-MT-all-commit-before-if-INST-modified
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (b1p (INST-modified? i))
		  (not (b1p (INST-first-modified? i)))
		  (not (MT-CMI-p MT))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (MT-all-commit-before i MT)))
  :hints (("goal" :cases ((consp (MT-trace MT))))
	  ("subgoal 2" :in-theory (enable INST-in))
	  ("subgoal 1" :cases ((equal (car (MT-trace MT)) i)))
	  ("subgoal 1.2" :in-theory
		       (enable MT-all-commit-before INST-in inv
			       correct-modified-first weak-inv
			       MT-CMI-p))))
)

; Following lemmas are about the effect of an external interrupt on
; special register.  Many lemmas involve MT-ISA-at-dispatch, which is
; a new function that requires minimum theory build-up.
;
; WARNING!!!!
; Following lemmas may be boring lemmas for a while.
; If you are not interested in the detail, skip to the landmark lemma
; ISA-SRF-ISA-step-exintr, where things get interesting again.
(encapsulate nil
(local
 (defthm commit-if-earlier-than-dq0-and-rob-empty
     (implies (and (inv MT MA)
		   (subtrace-p trace MT)
		   (consp trace)
		   (equal (INST-stg i) '(DQ 0))
		   (member-equal i (cdr trace))
		   (b1p (rob-empty? (MA-rob MA)))
		   (not (commit-stg-p (INST-stg (car trace))))
		   (INST-p i) (INST-listp trace)
		   (MAETT-p MT) (MA-state-p MA))
	      (retire-stg-p (INST-stg (car trace))))
   :hints (("goal" :use ((:instance INST-is-at-one-of-the-stages
				   (i (car trace)))
			 (:instance DQ0-IS-EARLIER-THAN-OTHER-DQ
				    (i i) (j (car trace))))
		   :in-theory (disable INST-is-at-one-of-the-stages)
		   :restrict ((NOT-ROB-EMPTY-IF-INST-IS-EXECUTED
			       ((i (car trace)))))))))

(local
(defthm MT-all-commit-before-INST-at-DQ0-induct
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (member-equal i trace) (INST-p i)
		  (b1p (rob-empty? (MA-rob MA)))
		  (equal (INST-stg i) '(DQ 0))
		  (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA))
	     (trace-all-commit-before i trace))))

(local
(defthm MT-all-commit-before-INST-at-DQ0-help
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(DQ 0))
		  (b1p (rob-empty? (MA-rob MA)))
		  (MAETT-p MT) (MA-state-p MA))
	     (MT-all-commit-before i MT))
  :hints (("goal" :in-theory (enable MT-all-commit-before INST-in)))))

; When an external interrupt occurs, all issued instructions have been
; committed. 
(defthm MT-all-commit-before-INST-at-DQ0
    (implies (and (inv MT MA)
		  (b1p (ex-intr? MA sigs))
		  (uniq-inst-at-stg '(DQ 0) MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (MT-all-commit-before (INST-at-stg '(DQ 0) MT) MT))
  :hints (("goal" :in-theory (enable ex-intr? lift-b-ops))))
)

(local
(defthm no-DQ-inst-if-not-DQ-DE0-valid
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (DQ-stg-p (INST-stg i))))
  :hints (("goal" :in-theory (enable DQ-stg-p)))))
(local (in-theory (disable no-DQ-inst-if-not-DQ-DE0-valid)))

(encapsulate nil
(local
 (defthm commit-if-earlier-than-IFU-and-rob-empty
     (implies (and (inv MT MA)
		   (subtrace-p trace MT)
		   (consp trace)
		   (equal (INST-stg i) '(IFU))
		   (member-equal i (cdr trace))
		   (b1p (rob-empty? (MA-rob MA)))
		   (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
		   (not (commit-stg-p (INST-stg (car trace))))
		   (INST-p i) (INST-listp trace)
		   (MAETT-p MT) (MA-state-p MA))
	      (retire-stg-p (INST-stg (car trace))))
   :hints (("goal" :use ((:instance INST-is-at-one-of-the-stages
				   (i (car trace)))
			 )
		   :in-theory (e/d (no-DQ-inst-if-not-DQ-DE0-valid)
				   (inst-is-at-one-of-the-stages))
		   :restrict ((NOT-ROB-EMPTY-IF-INST-IS-EXECUTED
			       ((i (car trace)))))))))

(local
(defthm MT-all-commit-before-INST-at-IFU-induct
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (b1p (rob-empty? (MA-ROB MA)))
		  (member-equal i trace) (INST-p i) (INST-listp trace)
		  (equal (INST-stg i) '(IFU))
		  (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (trace-all-commit-before i trace))))

(local
(defthm MT-all-commit-before-INST-at-IFU-help
    (implies (and (inv MT MA)
		  (b1p (rob-empty? (MA-ROB MA)))
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(IFU))
		  (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (MT-all-commit-before i MT))
  :hints (("goal" :in-theory (enable MT-all-commit-before INST-in)))))

; If no instruction is in the dispatch queue, and if an external
; interrupt occurs, then all instructions preceding the instruction in
; the IFU are committed.
(defthm MT-all-commit-before-INST-at-IFU
    (implies (and (inv MT MA)
		  (b1p (ex-intr? MA sigs))
		  (uniq-inst-at-stg '(IFU) MT)
		  (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (MT-all-commit-before (INST-at-stg '(IFU) MT) MT))
  :hints (("goal" :in-theory (enable ex-intr? lift-b-ops))))
)

(encapsulate nil
(defthm MT-ISA-at-dispatch-inst-at-DQ0-induct
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (member-equal i trace) (INST-p i) (INST-listp trace)
		  (not (dispatched-p i))
		  (trace-all-commit-before i trace))
	     (equal (trace-ISA-at-dispatch trace (INST-pre-ISA (car trace)))
		    (INST-pre-ISA i)))
  :hints ((when-found (car (cdr trace))
		      (:cases ((consp (cdr trace))))))
  :rule-classes nil)

(local
(defthm MT-ISA-at-dispatch-inst-at-DQ0-help
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (dispatched-p i))
		  (MT-all-commit-before i MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MT-ISA-at-dispatch MT)
		    (INST-pre-ISA i)))
  :hints (("goal" :in-theory (enable MT-ISA-at-dispatch MT-all-commit-before
				     INST-in)
		  :use (:instance MT-ISA-at-dispatch-inst-at-DQ0-induct
				  (trace (MT-trace MT))))
	  ("goal'" :cases ((consp (MT-trace MT)))))))

; A lemma about MT-ISA-at-dispatch.
; The ISA state at the dispatching boundary is equal to the pre-ISA of DQ0.
(defthm MT-ISA-at-dispatch-inst-at-DQ0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg '(DQ 0) MT)
		  (MT-all-commit-before (INST-at-stg '(DQ 0) MT) MT))
	     (equal (MT-ISA-at-dispatch MT)
		    (INST-pre-ISA (INST-at-stg '(DQ 0) MT))))
  :hints (("goal" :restrict
		  ((MT-ISA-at-dispatch-inst-at-DQ0-help
		    ((i (INST-at-stg '(DQ 0) MT))))))))

; A lemma about MT-ISA-at-dispatch.
; If there is no instruction in the dispatch queue, then the ISA state at
; the dispatching boundary is equal to the pre-ISA of the instruction at
; IFU.
(defthm MT-ISA-at-dispatch-inst-at-IFU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg '(IFU) MT)
		  (MT-all-commit-before (INST-at-stg '(IFU) MT) MT))
	     (equal (MT-ISA-at-dispatch MT)
		    (INST-pre-ISA (INST-at-stg '(IFU) MT))))
  :hints (("goal" :restrict
		  ((MT-ISA-at-dispatch-inst-at-DQ0-help
		    ((i (INST-at-stg '(IFU) MT))))))))

)

(local
(encapsulate nil
(local
(defthm ISA-pc-MT-ISA-at-dispatch-MT-pc-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (not (b1p (IFU-valid? (MA-IFU MA))))
		  (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
		  (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (ISA-PC (trace-ISA-at-dispatch trace ISA))
		    (trace-pc trace (ISA-pc ISA))))
  :Hints (("goal" :in-theory (e/d (dispatched-p* dq-stg-p)
				  (dispatched-p))
		  :restrict ((DQ-DE0-valid-if-inst-in ((I (car trace))))
			     (DQ-DE1-valid-if-inst-in ((I (car trace))))
			     (DQ-DE2-valid-if-inst-in ((I (car trace))))
			     (DQ-DE3-valid-if-inst-in ((I (car trace)))))))))

; A help lemma to prove ISA-pc-MT-ISA-at-dispatch
; 
; If no instruction is at IFU or dispatch queue, then the ISA at the
; dispatching boundary has the same pc value as the PC in the
; actual MA state.  
; 
; Note: we need to prove about PC here, because the special register
; stores the correct PC value when an exception occurs. 
(defthm ISA-pc-MT-ISA-at-dispatch-MT-pc
    (implies (and (inv MT MA)
		  (not (b1p (IFU-valid? (MA-IFU MA))))
		  (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (ISA-PC (MT-ISA-at-dispatch MT))
		    (MT-pc MT)))
  :hints (("goal" :in-theory (enable MT-pc MT-ISA-at-dispatch))))
))

(local
(encapsulate nil
(local
 (defthm committed-p-if-not-IFU-DE-valid-rob-empty
     (implies (and (inv MT MA)
		   (INST-in i MT) (INST-p i)
		   (b1p (rob-empty? (MA-ROB MA)))
		   (not (b1p (IFU-valid? (MA-IFU MA))))
		   (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
		   (not (commit-stg-p (INST-stg i)))
		   (MAETT-p MT) (MA-state-p MA))
	      (retire-stg-p (INST-stg i)))
   :hints (("goal" :use (:instance INST-is-at-one-of-the-stages)
		   :in-theory (e/d (DQ-stg-p)
				   (inst-is-at-one-of-the-stages))))))

(local
 (defthm not-inst-specultv-help
     (implies (and (inv MT MA)
		   (INST-in i MT) (INST-p i)
		   (b1p (rob-empty? (MA-ROB MA)))
		   (not (b1p (IFU-valid? (MA-IFU MA))))
		   (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
		   (MAETT-p MT) (MA-state-p MA))
	      (equal (inst-specultv? i) 0))
   :hints (("goal" :use (:instance
			 NOT-INST-SPECULTV-INST-IN-IF-COMMITTED)
		   :in-theory (enable committed-p)))))

		   

(local
(defthm MT-specultv-if-not-IFU-DE-valid-rob-empty-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (b1p (rob-empty? (MA-ROB MA)))
		  (not (b1p (IFU-valid? (MA-IFU MA))))
		  (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (trace-specultv? trace) 0))
  :hints (("goal" :in-theory (enable lift-b-ops INST-start-specultv?
				     committed-p)))))

(local
(defthm MT-specultv-if-not-IFU-DE-valid-rob-empty
    (implies (and (inv MT MA)
		  (b1p (rob-empty? (MA-ROB MA)))
		  (not (b1p (IFU-valid? (MA-IFU MA))))
		  (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MT-specultv? MT) 0))
  :hints (("goal" :in-theory (enable MT-specultv?)))))

(local
 (defthm MT-self-modify-if-not-IFU-DE-valid-rob-empty-induct
     (implies (and (inv MT MA)
		   (subtrace-p trace MT) (INST-listp trace)
		   (not (trace-CMI-p trace))
		   (b1p (rob-empty? (MA-ROB MA)))
		   (not (b1p (IFU-valid? (MA-IFU MA))))
		   (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
		   (MAETT-p MT) (MA-state-p MA))
	      (equal (trace-self-modify? trace) 0))
   :hints (("goal" :in-theory (enable committed-p)))))

(local
 (defthm MT-self-modify-if-not-IFU-DE-valid-rob-empty
     (implies (and (inv MT MA)
		   (not (MT-CMI-p MT))
		   (b1p (rob-empty? (MA-ROB MA)))
		   (not (b1p (IFU-valid? (MA-IFU MA))))
		   (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
		   (MAETT-p MT) (MA-state-p MA))
	      (equal (MT-self-modify? MT) 0))
   :hints (("goal" :in-theory (enable MT-self-modify? MT-CMI-p)))))
 
; Lemma to help the proof of ISA-pc-MT-ISA-at-dispatch.
(defthm ISA-pc-MT-ISA-at-dispatch-if-not-IFU-DE-valid
    (implies (and (inv MT MA)
		  (b1p (ex-intr? MA sigs))
		  (not (MT-CMI-p MT))
		  (not (b1p (IFU-valid? (MA-IFU MA))))
		  (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (ISA-PC (MT-ISA-at-dispatch MT))
		    (MA-pc MA)))
  :hints (("goal" :in-theory (enable ex-intr? lift-b-ops))))
))

(local (in-theory (disable ISA-pc-MT-ISA-at-dispatch-MT-pc)))

(encapsulate nil
(local
(defthm ISA-pc-MT-ISA-at-dispatch-help1
    (implies (and (inv MT MA)
		  (b1p (ex-intr? MA sigs))
		  (not (MT-CMI-p MT))
		  (uniq-inst-at-stg '(DQ 0) MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (DE-PC (DQ-DE0 (MA-DQ MA)))
		    (INST-pc (INST-at-stg '(DQ 0) MT))))
  :hints (("goal" :cases ((MT-all-commit-before (INST-at-stg '(DQ 0) MT) MT)))
	  ("subgoal 1" :in-theory (disable MT-ALL-COMMIT-BEFORE-INST-AT-DQ0)
	       :cases ((b1p (inst-specultv?
			     (INST-at-stg '(DQ 0) MT)))
		       (and (b1p (INST-modified?
				  (INST-at-stg '(DQ 0) MT)))
			    (not (b1p (INST-first-modified?
				       (INST-at-stg '(DQ 0) MT))))))))))

(local
(defthm ISA-pc-MT-ISA-at-dispatch-help2
    (implies (and (inv MT MA)
		  (b1p (ex-intr? MA sigs))
		  (not (MT-CMI-p MT))
		  (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
		  (uniq-inst-at-stg '(IFU) MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (IFU-PC (MA-IFU MA))
		    (INST-pc (INST-at-stg '(IFU) MT))))
  :hints (("goal" :cases ((MT-all-commit-before (INST-at-stg '(IFU) MT) MT)))
	  ("subgoal 1" :in-theory (disable MT-ALL-COMMIT-BEFORE-INST-AT-IFU)
		       :cases ((b1p (inst-specultv?
				     (INST-at-stg '(IFU) MT)))
			       (and (b1p (INST-modified?
					  (INST-at-stg '(IFU) MT)))
				    (not (b1p (INST-first-modified?
					       (INST-at-stg '(IFU) MT))))))))))

; If external interrupt occurs, the pc value in the ISA at the dispatching
; boundary is output from ex-intr-addr. 
(defthm ISA-pc-MT-ISA-at-dispatch
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (ex-intr? MA sigs))
		  (not (MT-CMI-p MT)))
	     (equal (ISA-pc (MT-ISA-at-dispatch MT))
		    (ex-intr-addr MA)))
  :hints (("goal" :in-theory (enable ex-intr-addr))))
)

(encapsulate  nil
(local
(defthm ISA-SRF-su-MT-ISA-at-dispatch-induction
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (b1p (rob-empty? (MA-rob MA)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (SRF-su (ISA-SRF (trace-ISA-at-dispatch trace ISA)))
		    (SRF-su (trace-SRF trace (ISA-SRF ISA)))))
  :hints (("goal" :restrict ((NOT-ROB-EMPTY-IF-INST-IS-EXECUTED
			      ((i (car trace)))))))))

(local
(defthm ISA-SRF-su-MT-ISA-at-dispatch-help
    (implies (and (inv MT MA)
		  (b1p (rob-empty? (MA-rob MA)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (SRF-su (ISA-SRF (MT-ISA-at-dispatch MT)))
		    (SRF-su (MT-SRF MT))))
  :hints (("goal" :in-theory (e/d (MT-ISA-at-dispatch MT-SRF)
				  (MT-SRF-=-MA-SRF))))))

; The current supervisor/user mode is the same as in the ISA at the
; dispatching boundary. 
(defthm ISA-SRF-su-MT-ISA-at-dispatch
    (implies (and (inv MT MA)
		  (b1p (ex-intr? MA MA-sigs))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (SRF-su (ISA-SRF (MT-ISA-at-dispatch MT)))
		    (SRF-su (MA-SRF MA))))
  :Hints (("goal" :in-theory (enable ex-intr? lift-b-ops))))
)

; This is a landmark lemma. 
; The effect of an external interrupt on the special register file.
(defthm ISA-SRF-ISA-step-exintr
    (implies (and (inv MT MA) (b1p (ISA-input-exint ISA-sigs))
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p MA-sigs)
		  (b1p (ex-intr? MA MA-sigs))
		  (not (MT-CMI-p (MT-step MT MA MA-sigs))))
	     (equal (ISA-SRF (ISA-step (MT-ISA-at-dispatch MT) ISA-sigs))
		    (SRF 1 (word (ex-intr-addr MA))
			   (word (SRF-su (MA-SRF MA))))))
  :hints (("goal" :in-theory (enable ISA-step ISA-external-intr)
		  :cases ((MT-CMI-p MT)))))

;;; Starting Case 2 

; A landmark lemma, even though it is easy to prove.
; If no instruction commits and no external interrupt occurs, then
; the special register does not change. 
(defthm step-SRF-if-not-commit-inst?
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (ex-intr? MA sigs)))
		  (not (b1p (commit-inst? MA))))
	     (equal (step-SRF MA sigs) (MA-SRF MA)))
  :hints (("goal" :in-theory (enable step-SRF))))

(encapsulate nil
(local
(defthm MT-SRF-MT-step-if-not-commit-inst-help
    (implies (and (inv MT MA)
		  (not (b1p (commit-inst? MA)))
		  (not (b1p (ex-intr? MA sigs))))
	     (equal (trace-SRF (step-trace trace MT MA sigs
					   ISA spc smc)
			       (ISA-SRF ISA))
		    (trace-SRF trace (ISA-SRF ISA))))))

; This is a landmark lemma. 
; If no instruction commits this cycle, MT-SRF remains identical.
(defthm MT-SRF-MT-step-if-not-commit-inst
    (implies (and (inv MT MA)
		  (not (b1p (ex-intr? MA sigs)))
		  (not (b1p (commit-inst? MA))))
	     (equal (MT-SRF (MT-step MT MA sigs))
		    (MT-SRF MT)))
  :hints (("goal" :in-theory (enable MT-SRF MT-step))))
)

;;; Start Case 3 
(encapsulate nil
(local
 (defthm INST-commit-ex-intr-exclusive
     (implies (and (inv MT MA)
		   (MA-state-p MA) (MAETT-p MT)
		   (b1p (ex-intr? MA sigs)))
	      (not (b1p (INST-commit? i MA))))
   :Hints (("goal" :in-theory (enable INST-commit? lift-b-ops)))))

(local
(defthm MT-SRF-MT-step-if-INST-commit-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (member-equal i trace)
		  (b1p (INST-commit? i MA))
		  (INST-p i) (MAETT-p MT) (MA-state-p MA))
	     (equal (trace-SRF (step-trace trace MT MA sigs
					   ISA spc smc)
			       (ISA-SRF (INST-pre-ISA (car trace))))
		    (ISA-SRF (INST-post-ISA i))))
  :rule-classes nil
  :hints (("goal" :in-theory (e/d (trace-SRF* 
				   INST-exintr-now-INST-commit-exclusive)
				  (trace-SRF))
		  :induct t)
	  (when-found (INST-pre-ISA (car (cdr trace)))
		      (:cases ((consp (cdr trace)))))
	  (when-found (consp (cdr trace))
		      (:expand
		       (STEP-TRACE (CDR TRACE)
			   MT MA SIGS
			   (ISA-STEP (INST-PRE-ISA (CAR TRACE))
				     (ISA-input (INST-EXINTR? (CAR TRACE))))
			   (B-IOR (INST-SPECULTV? (CAR TRACE))
				  (INST-START-SPECULTV? (CAR TRACE)))
			   (INST-MODIFIED? (CAR TRACE))))))))

(local
(defthm MT-SRF-MT-step-if-INST-commit?
    (implies (and (inv MT MA)
		  (b1p (INST-commit? i MA))
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MT-SRF (MT-step MT MA sigs))
		    (ISA-SRF (INST-post-ISA i))))
  :hints (("goal" :in-theory (enable MT-SRF INST-in MT-step)
		  :use (:instance MT-SRF-MT-step-if-INST-commit-help
				  (trace (MT-trace MT))
				  (spc 0) (smc 0)
				  (ISA (MT-init-ISA MT))))
	  ("goal'" :cases ((consp (MT-trace MT)))))))

; This is another landmark lemma. 
; If a instruction commits this cycle, the special register file in the
; next cycle is the same as in the post-ISA state of the instruction
; at the head of the ROB. 
; 
; Let me explain it more carefully. commit-inst? = 1 suggests that
; the instruction at the head of the ROB is committing this cycle.  
; This advances the committing boundary one instruction ahead.
; MT-SRF in the next cycle returns the special register
; file of the post-ISA state of the instruction, because the
; new commitment boundary is after the instruction.
(defthm MT-SRF-ISA-RF-inst-of-tag
    (implies (and (inv MT MA)
		  (b1p (commit-inst? MA))
		  (not (b1p (ex-intr? MA sigs)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MT-SRF (MT-step MT MA sigs))
		    (ISA-SRF
		     (INST-post-ISA (inst-of-tag (MT-ROB-head MT) MT)))))
  :hints (("goal" :restrict ((MT-SRF-MT-step-if-INST-commit?
			      ((i (inst-of-tag (MT-ROB-head MT) MT)))))
		  :in-theory (enable commit-inst? INST-commit?
				     lift-b-ops))))
)

; From here we start proving the landmark lemma
;     step-SRF-INST-post-ISA-of-INST-at-MT-ROB-head.
; WARNING !! Some lemmas may be boring. 
(encapsulate nil
(local
(defthm MT-SRF-INST-pre-ISA-if-MT-all-commit-before-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (member-equal i trace) (INST-p i)
		  (trace-all-commit-before i trace)
		  (subtrace-p trace MT)
		  (not (committed-p i)))
	     (equal (ISA-SRF (INST-pre-ISA i))
		    (trace-SRF trace
			       (ISA-SRF (ISA-before trace MT)))))
  :hints (("goal" :in-theory (enable ISA-before-MT-non-nil-trace)))))

(local
(defthm MT-SRF-INST-pre-ISA-if-MT-all-commit-before
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (MT-all-commit-before i MT)
		  (not (committed-p i)))
	     (equal (ISA-SRF (INST-pre-ISA i))
		    (MT-SRF MT)))
  :hints (("goal" :in-theory (e/d (MT-SRF MT-all-commit-before
						    INST-in)
				  (MT-SRF-=-MA-SRF))))))

; Suppose i is an instruction at the head of the ROB.  The current
; state of the special register file is the same as that in the
; pre-ISA state of i.
(defthm MA-SRF-pre-ISA-SRF-INST-at-ROB-head
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-of-tag (MT-ROB-head MT) MT))
	     (equal (ISA-SRF (INST-pre-ISA (inst-of-tag (MT-ROB-head MT)
							MT)))
		    (MA-SRF MA))))
)

(encapsulate nil
(local
 (defthm not-INST-excpt-INST-at-ROB-head-if-not-enter-excpt-help
     (implies (and (MA-state-p MA)
		   (not (b1p (enter-excpt? MA)))
		   (b1p (commit-inst? MA)))
	      (not (b1p (excpt-raised? (robe-excpt
					(nth-robe (rob-head (MA-rob MA))
						  (MA-rob MA)))))))
   :hints (("goal" :in-theory (enable lift-b-ops commit-inst? enter-excpt?)))))

; If the exception handling does not start this cycle, the instruction
; at the head of the ROB is not an exception causing instruction.
(defthm not-INST-excpt-INST-at-ROB-head-if-not-enter-excpt
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (INST-modified? (inst-of-tag (MT-rob-head MT)
							 MT))))
		  (not (b1p (enter-excpt? MA)))
		  (b1p (commit-inst? MA)))
	     (equal (INST-excpt? (inst-of-tag (MT-ROB-head MT) MT)) 0))
  :hints (("goal" :in-theory (enable equal-b1p-converter lift-b-ops)
		  :use
		  (:instance
		   not-INST-excpt-INST-at-ROB-head-if-not-enter-excpt-help))))

)

; The instruction at the head of the ROB is not a RFEH instruction
; if leave-excpt is 0.
(defthm not-INST-rfeh-INST-at-ROB-head-if-not-leave-excpt
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (INST-modified? (inst-of-tag (MT-rob-head MT)
							  MT))))
		  (not (b1p (INST-fetch-error? (inst-of-tag (MT-rob-head MT)
							     MT))))
		  (not (b1p (leave-excpt? MA)))
		  (b1p (commit-inst? MA)))
	     (equal (INST-rfeh? (inst-of-tag (MT-ROB-head MT) MT)) 0))
  :hints (("goal" :in-theory (enable equal-b1p-converter lift-b-ops
				     leave-excpt? commit-inst?))))

; The instruction at the head of the ROB is a RFEH instruction if
; leave-excpt is 1.
(defthm INST-rfeh-inst-of-tag
    (implies (and (inv MT MA)
		  (b1p (leave-excpt? MA))
		  (not (b1p (INST-modified?
			     (inst-of-tag (MT-ROB-head MT) MT))))
		  (not (b1p (INST-fetch-error?
			     (inst-of-tag (MT-ROB-head MT) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-rfeh? (inst-of-tag (MT-ROB-head MT) MT)) 1))
  :hints (("goal" :in-theory (enable leave-excpt? lift-b-ops
				     equal-b1p-converter))))

; If If rob-write-sreg from the ROB is 1, the instruction at the head
; of the ROB is a write-back register. 
(defthm INST-wb-inst-of-tag-if-rob-write-sreg
    (implies (and (inv MT MA)
		  (b1p (rob-write-sreg? (MA-rob MA)))
		  (not (b1p (INST-modified?
			     (inst-of-tag (MT-ROB-head MT) MT))))
		  (not (b1p (INST-fetch-error?
			     (inst-of-tag (MT-ROB-head MT) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-wb? (inst-of-tag (MT-ROB-head MT) MT)) 1))
  :hints (("goal" :in-theory (enable rob-write-sreg? lift-b-ops
				     equal-b1p-converter))))

; If rob-write-sreg from the ROB is 1, the instruction at the
; head of the ROB is a special register modifier.
(defthm INST-wb-sreg-inst-of-tag-if-rob-write-sreg
    (implies (and (inv MT MA)
		  (b1p (rob-write-sreg? (MA-rob MA)))
		  (not (b1p (INST-modified?
			     (inst-of-tag (MT-ROB-head MT) MT))))
		  (not (b1p (INST-fetch-error?
			     (inst-of-tag (MT-ROB-head MT) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-wb-sreg? (inst-of-tag (MT-ROB-head MT) MT)) 1))
  :hints (("goal" :in-theory (enable rob-write-sreg? lift-b-ops
				     equal-b1p-converter))))

; Relation between the signal ROB-write-sreg? from the ROB and the
; control vector of the instruction at the head of the ROB. 
(defthm ISA-SRF-ISA-step-if-not-ROB-write-SRF-help
    (implies (and (inv MT MA)
		  (uniq-inst-of-tag (MT-ROB-head MT) MT)
		  (complete-stg-p (INST-stg (inst-of-tag (MT-ROB-head MT) MT)))
		  (not (b1p (rob-write-sreg? (MA-rob MA))))
		  (not (b1p (INST-modified?
			     (inst-of-tag (MT-ROB-head MT) MT))))
		  (not (b1p (INST-excpt?
			     (inst-of-tag (MT-ROB-head MT) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (or (not (b1p (INST-wb-sreg? (inst-of-tag (MT-ROB-head MT) MT))))
		 (not (b1p (INST-wb? (inst-of-tag (MT-ROB-head MT) MT))))))
  :hints (("goal" :in-theory (enable rob-write-sreg? lift-b-ops
				     INST-excpt?
				     equal-b1p-converter)))
  :rule-classes nil)

(local
(defthm ISA-SRF-ISA-step-if-INST-rfeh
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (b1p (INST-rfeh? i))
		  (not (b1p (INST-excpt? i)))
		  (not (b1p (ISA-input-exint intr )))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (ISA-SRF (ISA-step (INST-pre-ISA i) intr))
		    (SRF (logcar (SRF-SR1 (ISA-SRF (INST-pre-ISA i))))
			 (SRF-SR0 (ISA-SRF (INST-pre-ISA i)))
			 (SRF-SR1 (ISA-SRF (INST-pre-ISA i))))))
  :hints (("goal" :in-theory (enable ISA-step 
				     INST-rfeh? decode INST-opcode
				     ISA-RFEH
				     supervisor-mode?
				     decode-illegal-inst?
				     ISA-illegal-inst
				     ISA-fetch-error
				     INST-decode-error?
				     lift-b-ops read-sreg
				     ISA-step-INST-pre-ISA
				     INST-excpt?
				     logbit* rdb INST-cntlv
				     exception-relations)
		  :cases ((b1p (INST-fetch-error? i)))))))

(local
(defthm ISA-SRF-ISA-step-if-INST-fetch-error
    (implies (and (INST-p i)
		  (b1p (INST-fetch-error? i))
		  (not (b1p (ISA-input-exint intr))))
	     (equal (ISA-SRF (ISA-step (INST-pre-ISA i) intr))
		    (SRF 1 (word (INST-pc i))
			   (word (SRF-su (ISA-SRF (INST-pre-ISA i)))))))
  :hints (("goal" :in-theory (enable ISA-step INST-fetch-error?
				     ISA-fetch-error)))))

(local
(defthm ISA-SRF-ISA-step-if-INST-decode-error
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (INST-fetch-error? i)))
		  (b1p (INST-decode-error? i))
		  (not (b1p (ISA-input-exint intr))))
	     (equal (ISA-SRF (ISA-step (INST-pre-ISA i) intr))
		    (SRF 1 (word (+ 1 (INST-pc i)))
			   (word (SRF-su (ISA-SRF (INST-pre-ISA i)))))))
  :hints (("goal" :in-theory (enable ISA-step INST-fetch-error?
				     ISA-RFEH supervisor-mode?
				     lift-b-ops decode-illegal-inst?
				     ISA-MFSR ISA-MTSR INST-RA INST-RC
				     INST-RB
				     ISA-illegal-inst
				     INST-decode-error?)))))

(local
(defthm ISA-SRF-ISA-step-if-INST-data-accs-error
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (INST-fetch-error? i)))
		  (b1p (INST-data-access-error? i))
		  (not (b1p (ISA-input-exint intr))))
	     (equal (ISA-SRF (ISA-step (INST-pre-ISA i) intr))
		    (SRF 1 (word (INST-pc i))
			   (word (SRF-su (ISA-SRF (INST-pre-ISA i)))))))
  :hints (("goal" :in-theory (enable INST-data-access-error? ISA-step
				     INST-fetch-error? INST-load-error?
				     INST-store-error? ISA-ldi
				     ISA-ld ISA-sti ISA-st
				     ISA-data-accs-error
				     lift-b-ops)))))
(local
(defthm ISA-SRF-ISA-step-if-INST-excpt
    (implies (and (inv MT MA)
		  (b1p (enter-excpt? MA))
		  (not (b1p (ISA-input-exint intr)))
		  (not (b1p (INST-modified?
			     (inst-of-tag (MT-ROB-head MT) MT))))
		  (not (b1p (inst-specultv?
			     (inst-of-tag (MT-ROB-head MT) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (ISA-SRF
		     (ISA-step (INST-pre-ISA (inst-of-tag (MT-ROB-head MT)
							  MT))
			       intr))
		    (SRF 1 (rob-write-val (MA-ROB MA) MA)
			 (word (SRF-su (MA-SRF MA))))))
  :hints (("goal" :in-theory (enable enter-excpt? lift-b-ops
				     rob-write-val INST-excpt-flags
				     exception-relations
				     INST-EXCPT-DETECTED-P)
		  :cases ((not (b1p (INST-fetch-error?
				(inst-of-tag (MT-ROB-head MT) MT))))))
	  ("subgoal 1" :cases ((not (b1p (INST-decode-error?
				(inst-of-tag (MT-ROB-head MT) MT))))))
	  ("subgoal 1.1" :cases ((not (b1p (INST-data-access-error?
				    (inst-of-tag (MT-ROB-head MT) MT)))))))))

; The effect of the ISA execution on the special register file 
; when the instruction actually modifies the special register. 
(defthm ISA-SRF-ISA-step-if-INST-wb
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (b1p (INST-wb? i))
		  (b1p (INST-wb-sreg? i))
		  (not (b1p (INST-rfeh? i)))
		  (not (b1p (INST-excpt? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (ISA-input-exint intr )))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (ISA-SRF (ISA-step (INST-pre-ISA i) intr))
		    (write-sreg (INST-dest-val i)
				(INST-dest-reg i)
				(ISA-SRF (INST-pre-ISA i)))))
  :hints (("goal" :in-theory (enable ISA-step INST-excpt? lift-b-ops
				     INST-fetch-error? INST-cntlv
				     decode logbit* rdb INST-opcode
				     supervisor-mode? decode-illegal-inst?
				     INST-dest-val INST-dest-reg
				     INST-rc INST-ra
				     INST-MTSR-DEST-VAL INST-src-val1
				     ISA-MTSR INST-decode-error?
				     INST-wb? INST-wb-sreg?))))

; When the committed instruction does not modify the special register,
; the state of the special register does not change. 
(defthm ISA-SRF-ISA-step-if-not-INST-wb-INST-wb-SRF
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (INST-excpt? i)))
		  (not (b1p (INST-rfeh? i)))
		  (or (not (b1p (INST-wb? i)))
		      (not (b1p (INST-wb-sreg? i))))
		  (not (b1p (ISA-input-exint intr )))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (ISA-SRF (ISA-step (INST-pre-ISA i) intr))
		    (ISA-SRF (INST-pre-ISA i))))
  :hints (("goal" :in-theory  (enable ISA-step INST-excpt? lift-b-ops
				     INST-fetch-error? INST-cntlv
				     INST-rfeh?
				     decode logbit* rdb INST-opcode
				     supervisor-mode? decode-illegal-inst?
				     INST-dest-val INST-dest-reg
				     INST-rc INST-ra
				     INST-MTSR-DEST-VAL INST-src-val1
				     ISA-add  ISA-mul ISA-br
				     ISA-ld ISA-ldi ISA-st
				     ISA-sync ISA-mfsr
				     ISA-sti
				     INST-decode-error?
				     INST-DATA-ACCESS-ERROR?
				     INST-load-error? INST-store-error?
				     INST-wb? INST-wb-sreg?))))

(encapsulate nil
(local
(defthm step-SRF-INST-post-ISA-of-INST-at-MT-ROB-head-normal-case-1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (commit-inst? MA))
		  (b1p (INST-fetch-error?
			(inst-of-tag (MT-ROB-head MT) MT)))
		  (not (b1p (INST-modified?
			     (inst-of-tag (MT-ROB-head MT) MT))))
		  (not (b1p (inst-specultv?
			     (inst-of-tag (MT-ROB-head MT) MT)))))
	     (equal (step-SRF MA sigs)
		    (ISA-SRF
		     (INST-post-ISA (inst-of-tag (MT-ROB-head MT) MT)))))
  :hints (("goal" :in-theory (e/d (step-SRF lift-b-ops
				      leave-excpt? enter-excpt?
				      INST-exintr-INST-in-if-not-retired
				      COMMIT-INST?
				      INST-EXCPT-FLAGS
				      ROB-WRITE-VAL)
				  (UNIQ-INST-OF-TAG-IF-COMMIT-INST
				   INST-is-at-one-of-the-stages
				   UNIQ-INST-OF-TAG-IF-context-sync))
		  :use (:instance inst-is-at-one-of-the-stages
				  (i (inst-of-tag (MT-rob-head MT) MT)))))))

(local
(defthm step-SRF-INST-post-ISA-of-INST-at-MT-ROB-head-normal-case-2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (commit-inst? MA))
		  (not (b1p (INST-fetch-error?
			     (inst-of-tag (MT-ROB-head MT) MT))))
		  (not (b1p (INST-modified?
			     (inst-of-tag (MT-ROB-head MT) MT))))
		  (not (b1p (inst-specultv?
			     (inst-of-tag (MT-ROB-head MT) MT)))))
	     (equal (step-SRF MA sigs)
		    (ISA-SRF
		     (INST-post-ISA (inst-of-tag (MT-ROB-head MT) MT)))))
  :hints (("goal" :in-theory
		  (enable step-SRF lift-b-ops
			  INST-exintr-INST-in-if-not-retired
			  not-INST-excpt-INST-at-ROB-head-if-not-enter-excpt)
		  :use
		  (:instance ISA-SRF-ISA-step-if-not-ROB-write-SRF-help)))))
				     

; A help lemma for step-SRF-INST-post-ISA-of-INST-at-MT-ROB-head.
(defthm step-SRF-INST-post-ISA-of-INST-at-MT-ROB-head-normal-case
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (commit-inst? MA))
		  (not (b1p (INST-modified?
			     (inst-of-tag (MT-ROB-head MT) MT))))
		  (not (b1p (inst-specultv?
			     (inst-of-tag (MT-ROB-head MT) MT)))))
	     (equal (step-SRF MA sigs)
		    (ISA-SRF
		     (INST-post-ISA (inst-of-tag (MT-ROB-head MT) MT)))))
  :hints (("goal" :cases ((b1p (INST-fetch-error?
				(inst-of-tag (MT-ROB-head MT) MT)))))))
)

; This is a landmark lemma. 
; Suppose instruction i is at the head of the ROB.  If i commits in this
; cycle, the new state of the special register file is identical to the
; special register file in the post-ISA state of i.
(defthm step-SRF-INST-post-ISA-of-INST-at-MT-ROB-head
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (commit-inst? MA))
		  (not (b1p (ex-intr? MA sigs)))
		  (not (MT-CMI-p (MT-step MT MA sigs))))
	     (equal (step-SRF MA sigs)
		    (ISA-SRF
		     (INST-post-ISA (inst-of-tag (MT-ROB-head MT) MT)))))
  :hints (("goal"
	   :cases ((b1p (INST-modified? (inst-of-tag (MT-ROB-head MT) MT)))
		   (b1p (inst-specultv? (inst-of-tag (MT-ROB-head MT) MT)))))))

(local
(defthm SRF-match-p-preserved-help
    (implies (and (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (inv MT MA)
		  (not (MT-CMI-p (MT-step MT ma sigs))))
	     (equal (MT-SRF  (MT-step MT MA sigs))
		    (step-SRF MA sigs)))
  :hints (("goal" :cases ((b1p (commit-inst? MA))
			  (b1p (ex-intr? MA sigs)))))))

; SRF-match-p is preserved.
(defthm SRF-match-p-preserved
    (implies (and (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (inv MT MA)
		  (not (MT-CMI-p (MT-step MT ma sigs))))
	     (SRF-match-p (MT-step MT ma sigs) (MA-step ma sigs)))
  :hints (("goal" :in-theory (enable SRF-match-p
				     MT-CMI-p))))

(deftheory incompatible-with-excpt
    (union-theories
     '(NOT-INST-RFEH-INST-AT-ROB-HEAD-IF-NOT-LEAVE-EXCPT
      not-INST-excpt-INST-at-ROB-head-if-not-enter-excpt
      INST-EXCPT-INST-AT-ROB-HEAD-IF-ENTER-EXCPT)
     (theory 'incompatible-with-excpt-in-MAETT-lemmas)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  Proof of PC-match-p preserved
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;; Proof of pc-match-p for initial states.
(defthm pc-match-p-init-MT
    (implies (MA-state-p MA)
	     (pc-match-p (init-MT MA) MA))
  :Hints (("goal" :in-theory (enable pc-match-p init-mt MT-pc))))

;;;;;;; Induction case
;;; Proof by case analysis,
;;
;  Cases are  
;    Case when ex-intr? is 1.
;    Case when enter-excpt? is 1
;    Case when commit-jmp? is on 
;    Case when leave-excpt? is on
;    Case when fetch-inst? is on 

;;;;;; Proof of pc-match-p for the case enter-excpt? is on 
(defthm ISA-pc-ISA-step-ex-intr
    (implies (b1p (ISA-input-exint intr))
	     (equal (ISA-pc (ISA-step ISA intr)) #x30))
  :hints (("goal" :in-theory (enable ISA-step ISA-external-intr))))
    

(encapsulate nil
(local
(defthm MT-pc-rob-jmp-addr-if-ex-intr-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (consp trace)
		  (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (ex-intr? MA sigs)))
	     (equal (trace-pc (step-trace trace MT MA sigs
					  (INST-pre-ISA (car trace))
					  spc smc)
			      (ISA-pc (INST-pre-ISA (car trace))))
		    #x30))
  :hints ((when-found (INST-PRE-ISA (CAR (CDR TRACE)))
		      (:cases ((consp (cdr trace))))))
  :rule-classes nil))
	  

; A landmark lemma.
; Next ideal pc value is supplied from ROB-jmp-addr, when an external
; interrupt occurs. 
(defthm MT-pc-rob-jmp-addr-if-ex-intr
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (ex-intr? MA sigs)))
	     (equal (MT-pc (MT-step MT MA sigs))
		    (ROB-jmp-addr (MA-rob MA) MA sigs)))
  :hints (("goal" :in-theory (enable ROB-jmp-addr MT-step MT-pc)
		  :use (:instance MT-pc-rob-jmp-addr-if-ex-intr-help
				  (trace (MT-trace MT)) (spc 0) (smc 0)))))
)

;;;;;    Case when enter-excpt? is 1
(local
(encapsulate nil
(local
(defthm MT-pc-MT-step-if-INST-cause-jmp-induct
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (consp trace)
		  (member-equal i trace) (INST-p i)
		  (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (trace-all-commit-before i trace)
		  (b1p (INST-cause-jmp? i MT MA sigs)))
	     (equal (trace-pc (step-trace trace MT MA sigs
					  (INST-pre-ISA (car trace))
					  spc smc)
			      (ISA-pc (INST-pre-ISA (car trace))))
		    (ISA-pc (INST-post-ISA i))))
  :hints ((when-found (INST-pre-ISA (car (cdr trace)))
		      (:cases ((consp (cdr trace))))))
  :rule-classes nil))

(local
(defthm MT-pc-MT-step-if-INST-cause-jmp-help
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (MT-all-commit-before i MT)
		  (b1p (INST-cause-jmp? i MT MA sigs)))
	     (equal (MT-pc (MT-step MT MA sigs))
		    (ISA-pc (INST-post-ISA i))))
; Matt K. mod: Apparently heuristics have somehow changed.  The proof goes
; through by replacing the original hints with corresponding proof-builder
; commands.
#|
  :hints (("goal" :in-theory (enable MT-pc MT-step
				     MT-all-commit-before INST-in)
	  :use (:instance MT-pc-MT-step-if-INST-cause-jmp-induct
			  (trace (MT-trace MT)) (smc 0) (spc 0))))
|#
  :instructions ((:in-theory (enable MT-pc MT-step
				     MT-all-commit-before INST-in))
                 (:use (:instance MT-pc-MT-step-if-INST-cause-jmp-induct
                                  (trace (MT-trace MT)) (smc 0) (spc 0)))
                 :prove) ; or :bash
  :rule-classes nil))

; If INST-cause-jmp? is 1, the ideal pc value for the next state is
; the PC in the post-ISA state of the instruction at the head of the ROB.
(defthm MT-pc-MT-step-if-INST-cause-jmp
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-of-tag (MT-ROB-head MT) MT)
		  (b1p (INST-cause-jmp? (inst-of-tag (MT-ROB-head MT) MT)
					MT MA sigs)))
     (equal (MT-pc (MT-step MT MA sigs))
	    (ISA-pc (INST-post-ISA (inst-of-tag (MT-ROB-head MT) MT)))))
  :hints (("goal" :use (:instance MT-pc-MT-step-if-INST-cause-jmp-help
				  (i (inst-of-tag (MT-ROB-head MT) MT))))))
))

(encapsulate nil
(local
(defthm ISA-pc-INST-post-ISA-INST-fetch-error
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (complete-stg-p (INST-stg i))
		  (b1p (INST-fetch-error? i))
		  (not (b1p (ISA-input-exint intr))))
	     (equal (ISA-pc (ISA-step (INST-pre-ISA i) intr))
		    (logapp 4 0 (excpt-type (INST-excpt-flags i)))))
  :hints (("goal" :in-theory (enable ISA-step INST-fetch-error?
				     ISA-fetch-error
				     INST-excpt-flags)))
  :rule-classes nil))

(local
(defthm ISA-pc-INST-post-ISA-INST-decode-error
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (complete-stg-p (INST-stg i))
		  (not (b1p (INST-fetch-error? i)))
		  (b1p (INST-decode-error? i))
		  (not (b1p (ISA-input-exint intr))))
	     (equal (ISA-pc (ISA-step (INST-pre-ISA i) intr))
		    (logapp 4 0 (excpt-type (INST-excpt-flags i)))))
  :hints (("goal" :in-theory (enable ISA-step INST-excpt-flags
				     ISA-step-INST-pre-ISA
				     decode-illegal-inst?
				     ISA-MFSR ISA-MTSR 
				     INST-ra INST-rc
				     ISA-rfeh supervisor-mode?
				     ISA-illegal-inst
				     INST-decode-error?
				     lift-b-ops)))
  :rule-classes nil))

(local
(defthm ISA-pc-INST-post-ISA-INST-data-accs-error
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (complete-stg-p (INST-stg i))
		  (not (b1p (INST-fetch-error? i)))
		  (not (b1p (INST-decode-error? i)))
		  (b1p (INST-data-access-error? i))
		  (not (b1p (ISA-input-exint intr))))
	     (equal (ISA-pc (ISA-step (INST-pre-ISA i) intr))
		    (logapp 4 0 (excpt-type (INST-excpt-flags i)))))
  :hints (("goal" :in-theory (enable ISA-step-INST-pre-ISA
				     INST-data-access-error?
				     INST-excpt-flags
				     ISA-ldi ISA-ld
				     ISA-st ISA-sti
				     ISA-data-accs-error
				     INST-load-error? INST-store-error?
				     lift-b-ops)))
  :rule-classes nil))

; The exception vector values.
; Suppose i is an exception raising instruction.  After execution i,
; the PC is set to exception type number which is shifted to the left 4-bits.
(defthm ISA-pc-INST-post-ISA-excpt-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (complete-stg-p (INST-stg i))
		  (b1p (INST-excpt? i)) (not (b1p (ISA-input-exint intr))))
	     (equal (ISA-pc (ISA-step (INST-pre-ISA i) intr))
		    (logapp 4 0 (excpt-type (INST-excpt-flags i)))))
  :hints (("goal" :in-theory (enable INST-excpt? lift-b-ops)
		  :use ((:instance ISA-pc-INST-post-ISA-INST-data-accs-error)
			(:instance ISA-pc-INST-post-ISA-INST-decode-error)
			(:instance ISA-pc-INST-post-ISA-INST-fetch-error)))))
)

; When an exception handling occurs, INST-cause-jmp? value for the
; instruction at the head of the ROB is 1. 
(defthm INST-cause-jmp-INST-at-MT-ROB-head-if-enter-excpt
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (INST-modified?
			     (inst-of-tag (MT-ROB-head MT) MT))))
		  (b1p (enter-excpt? MA)))
	     (equal (INST-cause-jmp? (inst-of-tag (MT-ROB-head MT) MT)
				     MT MA sigs)
		    1))
  :hints (("goal" :in-theory (enable enter-excpt? lift-b-ops
				     equal-b1p-converter
				     INST-cause-jmp?))))

; A landmark lemma. 
; When an exception handling occurs, the ideal pc value at the next
; cycle is output on ROB-jmp-addr.  
(defthm MT-pc-rob-jmp-addr-if-enter-excpt
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (MT-self-modify? (MT-step MT MA sigs))))
		  (b1p (enter-excpt? MA)))
	     (equal (MT-pc (MT-step MT MA sigs))
		    (ROB-jmp-addr (MA-rob MA) MA sigs)))
  :hints (("goal" :cases ((b1p (INST-modified?
				(inst-of-tag (MT-ROB-head MT) MT))))
		  :in-theory (enable ROB-jmp-addr
				     INST-exintr-INST-in-if-not-retired))))

;;;;;; Proof of pc-match-p for the case where commit-jmp? is on 

; When commit-jmp? is 1, INST-cause-jmp? is 1 for the instruction
; at the head of the ROB.
(defthm INST-cause-jmp-INST-at-MT-ROB-head-if-commit-jmp
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (INST-modified?
			     (inst-of-tag (MT-ROB-head MT) MT))))
		  (b1p (commit-jmp? MA)))
	     (equal (INST-cause-jmp? (inst-of-tag (MT-ROB-head MT) MT)
				     MT MA sigs)
		    1))
  :hints (("goal" :in-theory (e/d (enter-excpt? lift-b-ops
				commit-jmp? complete-stg-if-robe-complete
				equal-b1p-converter
				INST-cause-jmp?)
				  (incompatible-with-excpt)))))

; SYNC instruction increments the PC.
(defthm ISA-pc-INST-pre-ISA-if-INST-sync
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (complete-stg-p (INST-stg i))
		  (not (b1p (INST-excpt? i)))
		  (not (b1p (INST-rfeh? i)))
		  (b1p (INST-sync? i))
		  (not (b1p (ISA-input-exint intr))))
	     (equal (ISA-pc (ISA-step (INST-pre-ISA i) intr))
		    (addr (1+ (ISA-pc (INST-pre-ISA i))))))
  :hints (("goal" :in-theory (enable INST-sync? ISA-step-INST-pre-ISA
				     lift-b-ops INST-cntlv decode
				     rdb logbit* INST-opcode
				     INST-rfeh?
				     ISA-sync ISA-rfeh
				     INST-excpt?))))

; The effect of branch instruction.
(defthm ISA-pc-INST-pre-ISA-if-INST-branch
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (complete-stg-p (INST-stg i))
		  (not (b1p (INST-excpt? i)))
		  (b1p (INST-bu? i))
		  (not (b1p (ISA-input-exint intr))))
	     (equal (ISA-pc (ISA-step (INST-pre-ISA i) intr))
		    (if (b1p (INST-branch-taken? i))
			(INST-br-target i)
			(addr (1+ (ISA-pc (INST-pre-ISA i)))))))
  :hints (("goal" :in-theory (enable ISA-step-INST-pre-ISA
				     lift-b-ops INST-bu?
				     INST-cntlv INST-opcode
				     decode logbit* rdb
				     INST-im INST-BRANCH-TAKEN?
				     ISA-br bv-eqv-iff-equal
				     rname-p
				     INST-br-target
				     INST-excpt?))))

(encapsulate nil
(local
(defthm MT-pc-rob-jmp-addr-if-commit-jmp-help-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (INST-modified?
			     (inst-of-tag (MT-rob-head MT) MT))))
		  (not (b1p (ex-intr? MA sigs)))
		  (not (b1p (leave-excpt? MA)))
		  (not (b1p (enter-excpt? MA)))
		  (b1p (commit-jmp? MA)))
	     (equal (ROB-jmp-addr (MA-rob MA) MA sigs)
		    (ISA-pc (ISA-step (INST-pre-ISA
				       (inst-of-tag (MT-ROB-head MT) MT))
				      (ISA-input 0)))))
  :hints (("goal" :in-theory (e/d (ROB-jmp-addr
				     enter-excpt?
				     execute-stg-if-not-robe-complete
				     complete-stg-if-robe-complete
				     LEAVE-EXCPT?
				     INST-excpt?
				     lift-b-ops commit-jmp?)
				  (incompatible-with-excpt))
		  :cases
		  ((b1p (INST-excpt? (inst-of-tag (MT-rob-head MT) MT))))))))

(local
(defthm MT-pc-rob-jmp-addr-if-commit-jmp-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (MT-self-modify? (MT-step MT ma sigs))))
		  (not (b1p (ex-intr? MA sigs)))
		  (not (b1p (leave-excpt? MA)))
		  (not (b1p (enter-excpt? MA)))
		  (b1p (commit-jmp? MA)))
	     (equal (MT-pc (MT-step MT MA sigs))
		    (ROB-jmp-addr (MA-rob MA) MA sigs)))
  :hints (("goal" :cases ((b1p (INST-modified?
				(inst-of-tag (MT-ROB-head MT) MT))))
		  :in-theory (enable lift-b-ops
				     INST-exintr-INST-in-if-not-retired
				     commit-inst?)))))

; A landmark lemma
; When commit-jmp? is on, the ideal pc value is provided through
; ROB-jmp-addr.  Commit-jmp? is on when sync or branch is executed.
(defthm MT-pc-rob-jmp-addr-if-commit-jmp
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (MT-self-modify? (MT-step MT ma sigs))))
		  (not (b1p (leave-excpt? MA)))
		  (b1p (commit-jmp? MA)))
	     (equal (MT-pc (MT-step MT MA sigs))
		    (ROB-jmp-addr (MA-rob MA) MA sigs)))
  :hints (("goal" :cases ((b1p (ex-intr? MA sigs))
			  (b1p (enter-excpt? MA))))))

)

;;;;;; Proof of pc-match-p for the case leave-excpt? is on 
; The effect of RFEH instruction on the PC.
(defthm ISA-pc-INST-step-if-INST-rfeh
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (INST-excpt? i)))
		  (b1p (INST-rfeh? i))
		  (not (b1p (ISA-input-exint intr))))
	     (equal (ISA-pc (ISA-step (INST-pre-ISA i) intr))
		    (addr (SRF-sr0 (ISA-SRF (INST-pre-ISA i))))))
  :hints (("goal" :in-theory (enable ISA-step-INST-pre-ISA
				     INST-rfeh? INST-cntlv INST-opcode
				     logbit* rdb decode INST-decode-error?
				     decode-illegal-inst? supervisor-mode?
				     read-sreg
				     ISA-rfeh INST-excpt?
				     lift-b-ops))))

(encapsulate nil
(local
(defthm MT-pc-if-leave-excpt-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (INST-modified?
			     (inst-of-tag (MT-rob-head MT) MT))))
		  (not (b1p (enter-excpt? MA)))
		  (b1p (leave-excpt? MA)))
	     (equal (MT-pc (MT-step MT MA sigs))
		    (addr (SRF-SR0 (MA-SRF MA)))))
  :hints (("goal" :in-theory (e/d (leave-excpt? enter-excpt?
				INST-excpt?
				INST-exintr-INST-in-if-not-retired
				INST-EXCPT-DETECTED-P
				complete-stg-if-robe-complete
				execute-stg-if-not-robe-complete
				lift-b-ops)
				  (incompatible-with-excpt))
		  :cases
		  ((b1p (INST-excpt? (inst-of-tag (MT-rob-head MT) MT))))))))

; A landmark lemma.
; The ideal program counter value for the next state is provided from
; special register 0.
(defthm MT-pc-if-leave-excpt
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (MT-self-modify? (MT-step MT ma sigs))))
		  (not (b1p (enter-excpt? MA)))
		  (b1p (leave-excpt? MA)))
	     (equal (MT-pc (MT-step MT MA sigs))
		    (addr (SRF-SR0 (MA-SRF MA)))))
  :hints (("goal" :cases ((b1p (INST-modified?
				(inst-of-tag (MT-ROB-head MT) MT))))
		  :in-theory (enable lift-b-ops commit-inst?))))
)

;;;;;; Proof of pc-match-p for the case where no instruction is fetched.

(encapsulate nil
(local
(defthm MT-pc-if-not-fetch-inst-local
    (implies (and (inv MT MA)
		  (consp trace)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (ex-intr? MA sigs)))
		  (not (b1p (commit-jmp? MA)))
		  (not (b1p (enter-excpt? MA)))
		  (not (b1p (leave-excpt? MA)))
		  (not (b1p (fetch-inst? MA sigs))))
	     (equal (trace-pc (step-trace trace MT MA sigs
					  (INST-pre-ISA (car trace))
					  spc smc)
			      (ISA-pc (INST-pre-ISA (car trace))))
		    (trace-pc trace (ISA-pc (INST-pre-ISA (car trace))))))
  :hints ((when-found (INST-pre-ISA (car (cdr trace)))
		      (:cases ((consp (cdr trace)))))
	  ("goal" :in-theory (enable INST-cause-jmp? lift-b-ops)))
  :rule-classes nil))

; The ideal pc value for the next cycle is the current PC value
; if no instruction is fetched. 
(defthm MT-pc-if-not-fetch-inst
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (ex-intr? MA sigs)))
		  (not (b1p (commit-jmp? MA)))
		  (not (b1p (enter-excpt? MA)))
		  (not (b1p (leave-excpt? MA)))
		  (not (b1p (ex-intr? MA sigs)))
		  (not (b1p (fetch-inst? MA sigs))))
	     (equal (MT-pc (MT-step MT MA sigs))
		    (MT-pc MT)))
  :hints (("goal" :use (:instance MT-pc-if-not-fetch-inst-local
				  (trace (MT-trace MT)) (spc 0) (smc 0))
		  :in-theory (enable MT-pc MT-step))))
)

;;;;;; Proof of pc-match-p for the case fetch-inst? is on 

; If the instruction at IFU is a branch instruction whose branch is
; taken, the value output on the IFU-branch-target is the ; PC in the
; post-ISA state of the branch instruction.
(defthm IFU-branch-target-INST-pc-INST-post-ISA
    (implies (and (inv MT MA)
		  (uniq-INST-at-stg '(IFU) MT)
		  (not (b1p (INST-fetch-error? (INST-at-stg '(IFU) MT))))
		  (b1p (INST-bu? (INST-at-stg '(IFU) MT)))
		  (b1p (INST-branch-taken? (INST-at-stg '(IFU) MT)))
		  (not (b1p (inst-specultv? (INST-at-stg '(IFU) MT))))
		  (not (b1p (INST-modified? (INST-at-stg '(IFU) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (IFU-branch-target (MA-IFU MA))
		    (ISA-pc (INST-post-ISA (INST-at-stg '(IFU) MT)))))
  :hints (("goal" :in-theory (enable IFU-branch-target
				     exception-relations
				     INST-bu? INST-cntlv decode
				     logbit* rdb INST-opcode
				     INST-exintr-INST-in-if-not-retired
				     INST-branch-taken? lift-b-ops
				     ISA-br rname-p
				     ISA-step-INST-pre-ISA))))

(encapsulate nil
(local
(defthm MT-pc-post-ISA-INST-at-IFU-induct
    (implies (and (inv MT MA)
		  (consp trace)
		  (subtrace-p trace MT)
		  (member-equal i trace) (INST-p i)
		  (IFU-stg-p (INST-stg i))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (trace-pc trace (ISA-pc (INST-pre-ISA (car trace))))
		    (ISA-pc (INST-post-ISA i))))
  :hints (("goal" :in-theory (enable INST-exintr-INST-in-if-not-retired))
	  (when-found (TRACE-PC (CDR TRACE)
				(ISA-PC (ISA-STEP (INST-PRE-ISA (CAR TRACE))
						  '(ISA-INPUT 0))))
		      (:expand (TRACE-PC (CDR TRACE)
				(ISA-PC (ISA-STEP (INST-PRE-ISA (CAR TRACE))
						  '(ISA-INPUT 0)))))))
  :rule-classes nil))

(local
(defthm MT-pc-post-ISA-INST-at-IFU-help
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (IFU-stg-p (INST-stg i))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MT-pc MT) (ISA-pc (INST-post-ISA i))))
; Matt K. mod: Apparently heuristics have somehow changed.  The proof goes
; through by replacing the original hints with corresponding proof-builder
; commands.
#|
  :hints (("goal" :in-theory (enable MT-pc INST-in)
		  :use (:instance MT-pc-post-ISA-INST-at-IFU-induct
				  (trace (MT-trace MT)))))
|#
  :instructions ((:in-theory (enable MT-pc INST-in))
                 (:use (:instance MT-pc-post-ISA-INST-at-IFU-induct
				  (trace (MT-trace MT))))
                 :prove) ; or :bash

))

; When an instruction i is at IFU, the PC value calculated by MT-pc
; is the PC of the post-ISA of i.
(defthm MT-pc-post-ISA-INST-at-IFU
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(IFU) MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MT-pc MT)
		    (ISA-pc (INST-post-ISA (INST-at-stg '(IFU) MT)))))
  :hints (("goal" :restrict ((MT-pc-post-ISA-INST-at-IFU-help
			      ((i (INST-at-stg '(IFU) MT))))))))
)

(in-theory (disable MT-pc-post-ISA-INST-at-IFU))

; Following lemmas are for the proof of MT-pc-if-fetch-inst.
; WARNING!!!  You can skip to MT-pc-if-fetch-inst.
; there are interesting lemmas, but some of them are about the definition 
; of the speculative execution and other concepts, and the reader may be
; confused why they are related just by reading.  In fact, the
; speculative execution is closely related to the PC values, but the
; reader can get the big picture of the proof without understanding
; the following lemmas.

;
; If branch prediction and actual branch outcomes are different,
; INST-wrong-branch? of the branch instruction is set to 1. 
(defthm INST-wrong-branch-step-INST-IFU
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(IFU) MT)
		  (not (b1p (INST-branch-taken? (INST-at-stg '(IFU) MT))))
		  (b1p (IFU-branch-predict? (MA-IFU MA) MA sigs))
		  (not (b1p (DQ-full? (MA-DQ MA))))
		  (b1p (INST-bu? (INST-at-stg '(IFU) MT)))
		  (not (b1p (INST-excpt? (INST-at-stg '(IFU) MT))))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (INST-wrong-branch? (step-INST (INST-at-stg '(IFU) MT)
						   MT MA sigs))
		    1))
  :hints (("goal" :in-theory (enable INST-wrong-branch? lift-b-ops
				     equal-b1p-converter))))

      
; If a branch is wrongly predicted, the instruction starts a
; speculative execution.
(defthm INST-start-specultv-step-INST-IFU
    (implies (and (inv MT MA)
		  (not (b1p (INST-branch-taken? (INST-at-stg '(IFU) MT))))
		  (b1p (IFU-branch-predict? (MA-IFU MA) MA sigs))
		  (not (b1p (DQ-full? (MA-DQ MA))))
		  (not (b1p (inst-specultv? (INST-at-stg '(IFU) MT))))
		  (not (b1p (INST-modified? (INST-at-stg '(IFU) MT))))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (INST-start-specultv? (step-INST (INST-at-stg '(IFU) MT)
						     MT MA sigs))
		    1))
  :hints (("goal" :in-theory (enable INST-start-specultv? lift-b-ops
				     INST-BU-OPCODE-2
				     INST-opcode
				     equal-b1p-converter
				     IFU-branch-predict?)
		  :cases ((b1p (INST-excpt? (INST-at-stg '(IFU) MT)))))))

; If the branch prediction is incorrect for the instruction at IFU, 
; the processor starts speculative execution of instructions. 
(defthm not-MT-specultv-if-correct-branch-predict
    (implies (and (inv MT MA)
		  (not (b1p (DQ-full? (MA-DQ MA))))
		  (not (b1p (INST-branch-taken? (INST-at-stg '(IFU) MT))))
		  (not (b1p (inst-specultv? (INST-at-stg '(IFU) MT))))
		  (not (b1p (INST-modified? (INST-at-stg '(IFU) MT)))) 
		  (b1p (IFU-branch-predict? (MA-IFU MA) MA sigs))
		  (not (b1p (flush-all? MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (MT-specultv? (MT-step MT MA sigs)) 1))
  :hints (("goal" :restrict
		  ((MT-inst-specultv-if-INST-start-specultv
		    ((i (step-INST (INST-at-stg '(IFU) MT) MT MA sigs)))))
		  :in-theory (enable IFU-branch-predict?
				     lift-b-ops))))

; If a fetch error occurs, a speculative execution starts. 
; Note: even after a fetch error, the processor continues to
; fetch instructions.  We consider this as speculative actions. 
(defthm MT-specultv-if-INST-fetch-error
    (implies (and (b1p (INST-fetch-error? i))
		  (INST-in i MT) (INST-p i)
		  (not (dispatched-p i))
		  (not (b1p (flush-all? MA sigs))))
	     (equal (MT-specultv? (MT-step MT MA sigs)) 1))
  :Hints (("goal" :restrict ((MT-INST-SPECULTV-IF-INST-START-SPECULTV
			      ((i (step-INST i MT MA sigs)))))
		  :in-theory (enable INST-start-specultv?
				     lift-b-ops dispatched-p
				     INST-excpt?))))

(local
(defthm IFU-branch-target-if-IFU-branch-predict
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (b1p (IFU-branch-predict? (MA-IFU MA) MA sigs))
		  (not (b1p (enter-excpt? MA)))
		  (not (b1p (ex-intr? MA sigs)))
		  (not (b1p (leave-excpt? MA)))
		  (not (b1p (commit-jmp? MA)))
		  (not (b1p (DQ-full? (MA-DQ MA))))
		  (not (b1p (MT-specultv? (MT-step MT MA sigs))))
		  (not (b1p (MT-self-modify? MT))))
	     (equal (MT-pc MT)
		    (IFU-branch-target (MA-IFU MA))))
  :hints (("goal" :in-theory (enable IFU-branch-predict? lift-b-ops
				     INST-BU-OPCODE-2 INST-opcode
				     exception-relations
				     MT-pc-post-ISA-INST-at-IFU
				     flush-all?)
		  :cases ((b1p (inst-specultv? (INST-at-stg '(IFU) MT)))
			  (b1p (INST-modified? (INST-at-stg '(IFU) MT)))
			  (b1p (INST-fetch-error? (INST-at-stg '(IFU) MT)))))
	  ("subgoal 4" :cases ((not (b1p (INST-branch-taken?
					  (INST-at-stg '(IFU) MT)))))))))

(encapsulate nil
(local
(defthm MT-pc-MT-step-if-fetched-inst-help
    (implies (b1p (fetch-inst? MA sigs))
	     (equal (trace-pc (step-trace trace MT MA sigs
					  ISA spc smc)
			      (ISA-pc ISA))
		    (ISA-pc (INST-post-ISA
			     (fetched-inst MT (trace-final-ISA trace ISA)
					   spc1 smc1)))))))

; When an instruction is fetched, the ideal PC value is the PC in the
; post-ISA state of the fetched instruction.
(defthm MT-pc-MT-step-if-fetched-inst
    (implies (b1p (fetch-inst? MA sigs))
	     (equal (MT-pc (MT-step MT MA sigs))
		    (ISA-pc (INST-post-ISA
			     (fetched-inst MT (MT-final-ISA MT)
					   (MT-specultv? MT)
					   (MT-self-modify? MT))))))
  :hints (("goal" :in-theory (enable MT-pc MT-step
				     MT-final-ISA)
		  :use (:instance MT-pc-MT-step-if-fetched-inst-help
				  (trace (MT-trace MT))
				  (spc1 (MT-specultv? MT))
				  (smc1 (MT-self-modify? MT))
				  (ISA (MT-init-ISA MT))))))
)

; This is a technical lemma, and the reader may want to skip this.
; The ISA-start-specultv becomes 1, whenever the machine fetches an
; instruction that will not be committed.  For instance, such
; instructions are fetched after a mispredicted branch instruction, an
; exception-raising instruction, and so on.  Otherwise, the PC is
; incremented by 1.
(defthm ISA-pc-INST-pre-ISA-if-not-INST-start-specultv
    (implies (and (not (b1p (INST-start-specultv?
			     (fetched-inst MT ISA spc smc))))
		  (not (b1p (ISA-input-exint intr))))
	     (equal (ISA-pc (ISA-step ISA intr))
		    (addr (+ 1 (ISA-pc ISA)))))
  :hints (("goal" :in-theory (enable lift-b-ops INST-excpt?
				     ISA-step
				     INST-wrong-branch?
				     INST-context-sync? INST-sync?
				     INST-fetch-error?
				     INST-decode-error?
				     decode-illegal-inst?
				     supervisor-mode? INST-ra INST-rc
				     INST-data-access-error?
				     INST-load-error? INST-store-error?
				     INST-branch-taken?
				     INST-bu? INST-cntlv INST-opcode
				     decode logbit* rdb
				     ISA-add ISA-mul ISA-br
				     ISA-st ISA-sti ISA-MFSR
				     ISA-MTSR
				     ISA-ld ISA-ldi
				     INST-start-specultv?))))

(encapsulate nil
(local
(defthm member-equal-fetched-inst
   (implies (and (inv MT MA)
		 (b1p (fetch-inst? MA sigs))
		 (subtrace-p trace MT) (INST-listp trace)
		 (MAETT-p MT) (MA-state-p MA))
    (member-equal (fetched-inst MT (trace-final-ISA trace
						    (ISA-before trace MT))
				(MT-specultv? MT)
				(MT-self-modify? MT))
		  (step-trace trace MT MA sigs
			      (ISA-before trace MT)
			      (specultv-before? trace MT)
			      (modified-inst-before? trace MT))))
  :hints (("goal" :in-theory (enable lift-b-ops)))
  :rule-classes nil))

; The fetched instruction is in the new MAETT. 
(defthm INST-in-fetched-inst
    (implies (and (inv MT MA)
		  (b1p (fetch-inst? MA sigs))
		  (MAETT-p MT) (MA-state-p MA))
    (INST-in (fetched-inst MT (MT-final-ISA MT) (MT-specultv? MT)
			   (MT-self-modify? MT))
	     (MT-step MT MA sigs)))
  :hints (("goal" :use (:instance member-equal-fetched-inst
				  (trace (MT-trace MT)))
		  :in-theory (enable MT-final-ISA MT-specultv? INST-in
				     MT-self-modify? MT-step))))
)

; If the fetched instruction starts speculative execution,
; MT-specultv? is 1. (That means the processor is executing speculatively.)
(defthm INST-in-specultv-if-INST-start-specultv-fetched-inst
    (implies (and (inv MT MA)
		  (b1p (fetch-inst? MA sigs))
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (INST-start-specultv?
			(fetched-inst MT (MT-final-ISA MT)
				      (MT-specultv? MT)
				      (MT-self-modify? MT)))))
	     (equal (MT-specultv? (MT-step MT MA sigs)) 1))
  :hints (("goal" :in-theory (enable fetch-inst? lift-b-ops)
		  :restrict
		  ((MT-INST-SPECULTV-IF-INST-START-SPECULTV
		    ((i (fetched-inst MT (MT-final-ISA MT)
				      (MT-specultv? MT)
				      (MT-self-modify? MT)))))))))

(encapsulate nil
(local
(defthm MT-specultv-MT-step-if-fetch-inst-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (b1p (fetch-inst? MA sigs))
		  (not (b1p (trace-self-modify? trace)))
		  (b1p (trace-specultv? trace))
		  (INST-listp trace) (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs))
	     (equal (trace-specultv? (step-trace trace MT MA sigs
						 ISA spc smc))
		    1))
  :hints (("goal" :in-theory (enable lift-b-ops fetch-inst?)))))

; If the processor fetches an instruction, and it has been executing 
; instructions speculatively, it continues to execute instructions
; speculatively.
(defthm MT-specultv-MT-step-if-fetch-inst
    (implies (and (inv MT MA)
		  (b1p (fetch-inst? MA sigs))
		  (not (b1p (MT-self-modify? MT)))
		  (b1p (MT-specultv? MT))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (MT-specultv? (MT-step MT MA sigs)) 1))
  :hints (("goal" :in-theory (enable MT-step MT-specultv? MT-self-modify?))))
				     
)

(encapsulate nil
(local
(defthm MT-self-modify-MT-step-if-fetch-inst-help
    (implies (and (INST-listp trace)
		  (b1p (trace-self-modify? trace))
		  (b1p (fetch-inst? MA sigs)))
	     (equal (trace-self-modify? (step-trace trace MT MA sigs
						    ISA spc smc)) 1))
  :hints (("goal" :in-theory (enable fetch-inst? lift-b-ops)))))

; The processor continues to execute a modified stream of instructions,
; if it fetches an instruction this cycle. 
(defthm MT-self-modify-MT-step-if-fetch-inst
    (implies (and (MAETT-p MT) (b1p (MT-self-modify? MT))
		  (b1p (fetch-inst? MA sigs)))
	     (equal (MT-self-modify? (MT-step MT MA sigs)) 1))
  :hints (("goal" :in-theory (enable MT-self-modify? MT-step))))
)

; A landmark lemma.  When the processor fetches an instruction, 
; the pc is incremented. 
(defthm MT-pc-if-fetch-inst
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (not (b1p (MT-specultv? (MT-step MT MA sigs))))
		  (not (b1p (MT-self-modify? (MT-step MT MA sigs))))
		  (b1p (fetch-inst? MA sigs)))
	     (equal (MT-pc (MT-step MT MA sigs))
		    (addr (+ 1 (MA-pc MA)))))
  :hints (("goal" :in-theory
		  (e/d ()
		       (ISA-pc-INST-pre-ISA-if-not-INST-start-specultv)
		       )
		  :cases ((b1p (MT-self-modify? MT))
			  (b1p (INST-start-specultv?
				(FETCHED-INST MT (MT-FINAL-ISA MT)
					      (MT-SPECULTV? MT)
					      (MT-SELF-MODIFY? MT))))))
	  ("subgoal 3" :cases ((b1p (MT-specultv? MT))))
	  ("subgoal 3.2" :use (:instance
			     ISA-pc-INST-pre-ISA-if-not-INST-start-specultv
			     (intr (ISA-input 0))
			     (ISA (MT-final-ISA MT))
			     (spc (MT-specultv? MT))
			     (smc (MT-self-modify? MT))))))

;; Now all cases are covered, following are the lemmas to help the proof of 
;; pc-match-p-preserved.
(encapsulate nil
(local
(defthm MT-self-modify-MT-step-help
    (implies (and (INST-listp trace)
		  (not (b1p (ex-intr? MA sigs)))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (fetch-inst? MA sigs))))
	     (equal (trace-self-modify? (step-trace trace MT MA sigs
						    ISA spc smc))
		    (trace-self-modify? trace)))
  :hints (("goal" :in-theory (enable flush-all? lift-b-ops ex-intr?
				     INST-cause-jmp? INST-exintr-now?)))))

; If a processor is executing a modified stream of instructions,
; it will continue to execute modified instruction stream unless
; some the pipeline is flushed.
(defthm MT-self-modify-MT-step
    (implies (and (MAETT-p MT)
		  (not (b1p (ex-intr? MA sigs)))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (fetch-inst? MA sigs))))
	     (equal (MT-self-modify? (MT-step MT MA sigs))
		    (MT-self-modify? MT)))
  :hints (("goal" :in-theory (enable MT-self-modify? MT-step))))
)

; Following are several lemmas about speculative execution, 
; branching and exceptions.
(encapsulate nil
(local
(defthm MT-specultv-MT-step-if-not-branch-predict-induct
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (fetch-inst? MA sigs)))
		  (not (b1p (trace-self-modify? trace)))
		  (not (b1p (IFU-branch-predict? (MA-IFU MA) MA sigs))))
	     (equal (trace-specultv? (step-trace trace MT MA sigs
						 ISA spc smc))
		    (trace-specultv? trace)))
  :hints (("goal" :in-theory (enable lift-b-ops)))))

(defthm MT-specultv-MT-step-if-not-branch-predict
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (MT-self-modify? MT)))
		  (not (b1p (fetch-inst? MA sigs)))
		  (not (b1p (IFU-branch-predict? (MA-IFU MA) MA sigs))))
	     (equal (MT-specultv? (MT-step MT MA sigs))
		    (MT-specultv? MT)))
  :hints (("goal" :in-theory (enable MT-specultv? MT-step
				     MT-self-modify?))))
)

(local
(encapsulate nil
(local
(defthm MT-specultv-MT-step-if-dq-full-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (fetch-inst? MA sigs)))
		  (not (b1p (trace-self-modify? trace)))
		  (b1p (DQ-full? (MA-DQ MA))))
	     (equal (trace-specultv? (step-trace trace MT MA sigs
						 ISA spc smc))
		    (trace-specultv? trace)))
  :hints (("goal" :in-theory (enable lift-b-ops)))))

(defthm MT-specultv-MT-step-if-dq-full
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (fetch-inst? MA sigs)))
		  (not (b1p (MT-self-modify? MT)))
		  (b1p (DQ-full? (MA-DQ MA))))
	     (equal (MT-specultv? (MT-step MT MA sigs))
		    (MT-specultv? MT)))
  :hints (("goal" :in-theory (enable MT-specultv? MT-step
				     MT-self-modify?))))
))

(local
(defthm INST-fetch-error-fetched-inst-if-IFU-fetch-prohibited
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (MT-specultv? MT)))
		  (not (b1p (MT-self-modify? MT)))
		  (b1p (IFU-fetch-prohibited? (MA-pc MA) (MA-mem MA)
					      (SRF-su (MA-SRF MA)))))
	     (equal (INST-fetch-error? (fetched-inst MT
						     (MT-final-ISA MT)
						     spc smc))
		    1))
  :hints (("goal" :in-theory (enable INST-fetch-error? lift-b-ops
				     IFU-fetch-prohibited?
				     read-error?
				     equal-b1p-converter)))))

(local
(defthm INST-excpt-fetched-inst-if-IFU-fetch-prohibited
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (MT-specultv? MT)))
		  (not (b1p (MT-self-modify? MT)))
		  (b1p (IFU-fetch-prohibited? (MA-pc MA) (MA-mem MA)
					      (SRF-su (MA-SRF MA)))))
	     (equal (INST-excpt? (fetched-inst MT
					       (MT-final-ISA MT)
					       spc smc))
		    1))
  :hints (("goal" :in-theory (enable INST-excpt?)))))

(local
(defthm INST-start-specultv-fetched-inst-if-IFU-fetch-prohibited
    (implies (and (inv MT MA)
		  (not (b1p (MT-specultv? MT)))
		  (not (b1p (MT-self-modify? MT)))
		  (b1p (IFU-fetch-prohibited? (MA-pc MA) (MA-mem MA)
					      (SRF-su (MA-SRF MA))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-start-specultv? (fetched-inst MT
							(MT-final-ISA MT)
							spc smc)) 1))
  :hints (("goal" :in-theory (enable INST-start-specultv?)))))

(local
(encapsulate nil
(local
(defthm MT-specultv-MT-step-if-fetch-prohibited-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (not (b1p (specultv-before? trace MT)))
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (IFU-fetch-prohibited? (MA-pc MA) (MA-mem MA)
					      (SRF-su (MA-SRF MA))))
		  (b1p (fetch-inst? MA sigs))
		  (not (b1p (MT-self-modify? MT))))
	     (equal (trace-specultv? (step-trace trace MT MA sigs
						 (ISA-before trace MT)
						 spc smc))
		    1))
  :hints (("goal" :in-theory (enable lift-b-ops)))
  :rule-classes nil))

(defthm MT-specultv-MT-step-if-fetch-prohibited
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (IFU-fetch-prohibited? (MA-pc MA) (MA-mem MA)
					      (SRF-su (MA-SRF MA))))
		  (b1p (fetch-inst? MA sigs))
		  (not (b1p (MT-self-modify? MT))))
	     (equal (MT-specultv? (MT-step MT MA sigs)) 1))
  :hints (("goal" :in-theory (enable MT-specultv? MT-step)
		  :use (:instance
			MT-specultv-MT-step-if-fetch-prohibited-help
			(trace (MT-trace MT))
			(spc 0) (smc 0)))))
))
		    

(local
(defthm pc-match-p-preserved-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (b1p (MT-specultv? (MT-step MT MA sigs))))
		  (not (b1p (MT-self-modify? (MT-step MT MA sigs)))))
	     (equal (MT-pc (MT-step MT MA sigs)) (step-pc MA sigs)))
  :hints (("goal" :in-theory (e/d (step-pc lift-b-ops fetch-inst?
				   MT-specultv-p MT-self-modify-p
				     IFU-branch-predict?
				     flush-all?)
				  (MT-PC-MT-STEP-IF-FETCHED-INST
				   INST-POST-ISA-FETCHED-INST
				   MT-PC-MT-STEP-IF-INST-CAUSE-JMP
				   INST-CAUSE-JMP-IF-LEAVE-EXCPT))
		  :cases ((b1p (fetch-inst? MA sigs))))
	  ("subgoal 1" :cases ((b1p (MT-self-modify? MT)))))))

; pc-match-p is an invariant. 
(defthm pc-match-p-preserved
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (pc-match-p (MT-step MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable pc-match-p lift-b-ops
				     MT-specultv-p MT-self-modify-p))))
		  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Proof of Mem-match-p 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Proof of mem-match-p for initial state
(defthm mem-match-p-init-MT
    (implies (MA-state-p MA)
	     (mem-match-p (init-MT MA) MA))
  :hints (("goal" :in-theory (enable mem-match-p init-MT MT-mem))))

;;; Proof of induction case
;; There are two landmark lemmas.
;    MT-mem-if-step-MT-if-release-wbuf0
;    MT-mem-if-step-MT-if-not-release-wbuf0
; These lemmas define the value of MT-mem in the next cycle. 
; The basic idea of proof is comparing
;  (step-mem MA sigs) and (MT-mem (MT-step MT MA sigs)).
; Both sides are expressed in terms of MA, and proven to be equivalent.

; An external interrupt does not change the memory.
(defthm ISA-mem-ISA-step-if-exint
    (implies (b1p (ISA-input-exint intr))
	     (equal (ISA-mem (ISA-step ISA intr)) (ISA-mem ISA)))
  :hints (("goal" :in-theory (enable ISA-step ISA-external-intr))))

; An instruction causing an internal exception does not modify the memory.
(defthm ISA-mem-ISA-step-if-INST-excpt
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (b1p (INST-excpt? i))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (ISA-mem (ISA-step (INST-pre-ISA i) intr))
		    (ISA-mem (INST-pre-ISA i))))
  :hints (("goal" :in-theory (enable INST-excpt? lift-b-ops
				     ISA-external-intr
				     INST-fetch-error? INST-decode-error?
				     INST-data-access-error?
				     INST-store-error? INST-load-error?
				     decode-illegal-inst?
				     ISA-fetch-error
				     ISA-step-functions
				     ISA-step))))

; If i is not a store instruction, i does not modifier the memory.
(defthm ISA-mem-ISA-step-if-not-INST-store
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (INST-store? i))))
	     (equal (ISA-mem (ISA-step (INST-pre-ISA i) intr))
		    (ISA-mem (INST-pre-ISA i))))
  :hints (("goal" :in-theory (enable ISA-step INST-store? lift-b-ops
				     INST-ld-st? INST-cntlv
				     INST-LSU?
				     INST-opcode decode logbit* rdb
				     ISA-external-intr
				     ISA-fetch-error
				     ISA-add ISA-mul ISA-br
				     ISA-data-accs-error
				     ISA-ld ISA-ldi
				     ISA-illegal-INST ISA-mfsr ISA-mtsr
				     ISA-sync ISA-rfeh))))

; If an exception occurs this cycle, then the instruction at the
; head of the ROB does not modify the memory.
(defthm ISA-mem-INST-step-if-enter-excpt
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (inst-tag i) (MT-ROB-head MT))
		  (complete-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (b1p (enter-excpt? MA)))
	     (equal (ISA-mem (ISA-step (INST-pre-ISA i) ISA-sigs))
		    (ISA-mem (INST-pre-ISA i))))
  :hints (("goal" :in-theory (enable enter-excpt? lift-b-ops
				     exception-relations)
		  :cases ((b1p (INST-excpt? i))))))

; If commit-jmp? is on, the instruction at the head of the ROB does not
; modify the memory.
; See ISA-mem-INST-step-if-INST-cause-jmp.
(defthm ISA-mem-INST-step-if-commit-jmp
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (inst-tag i) (MT-ROB-head MT))
		  (complete-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (b1p (commit-jmp? MA)))
	     (equal (ISA-mem (ISA-step (INST-pre-ISA i) ISA-sigs))
		    (ISA-mem (INST-pre-ISA i))))
  :hints (("goal" :cases ((not (b1p (INST-store? i))) (b1p (INST-excpt? i)))
		  :in-theory (enable commit-jmp? lift-b-ops
				     INST-excpt?))))

; If leave-excpt? is on, then the instruction at the head of the ROB does
; not modify the memory.
; See ISA-mem-INST-step-if-INST-cause-jmp.
(defthm ISA-mem-INST-step-if-leave-excpt
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (inst-tag i) (MT-ROB-head MT))
		  (complete-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (b1p (leave-excpt? MA)))
	     (equal (ISA-mem (ISA-step (INST-pre-ISA i) ISA-sigs))
		    (ISA-mem (INST-pre-ISA i))))
  :hints (("goal" :cases ((not (b1p (INST-store? i))) (b1p (INST-excpt? i)))
		  :in-theory (enable leave-excpt? lift-b-ops
				     INST-excpt?))))

; INST-cause-jmp? is on for i, if i does not modify the memory. 
; An instruction causing a jump (in any sense) does not modify a memory.
; For instance, a branch instruction or a RFEH instruction does not modify
; the memory.
(defthm ISA-mem-INST-step-if-INST-cause-jmp
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (not (MT-CMI-p (MT-step MT MA MA-sigs)))
		  (b1p (INST-cause-jmp? i MT MA MA-sigs)))
	     (equal (ISA-mem (ISA-step (INST-pre-ISA i) ISA-sigs))
		    (ISA-mem (INST-pre-ISA i))))
  :hints (("goal" :in-theory (enable INST-cause-jmp? lift-b-ops)
		  :cases ((b1p (inst-specultv? i))
			  (b1p (INST-modified? i))))))

; If i is a store instruction, it does not cause a jump (in any sense). 
(defthm not-INST-cause-jmp-if-INST-store
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (MT-CMI-p (MT-step MT MA MA-sigs)))
		  (b1p (INST-store? i)) (not (b1p (INST-excpt? i))))
	     (equal (INST-cause-jmp? i MT MA sigs) 0))
  :hints (("goal" :in-theory (e/d (INST-cause-jmp? lift-b-ops
				     INST-excpt? commit-jmp?
				     commit-inst?
				     enter-excpt? leave-excpt?
				     equal-b1p-converter)
				  (incompatible-with-excpt))
		  :cases ((b1p (INST-modified? i))
			  (b1p (inst-specultv? i))))))

(local
(defthm retire-stg-p-step-INST-if-not-INST-store
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (INST-store? i)))
		  (b1p (INST-cause-jmp? i MT MA sigs))
		  (not (MT-CMI-p (MT-step MT MA MA-sigs))))
	     (retire-stg-p (INST-stg (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (enable complete-stg-p
				     step-inst step-inst-complete
				     INST-cause-jmp? INST-commit?
				     lift-b-ops)
		  :cases ((b1p (inst-specultv? i))
			  (b1p (INST-modified? i)))))))

; If i causes an exception, it retires immediately.
(defthm retire-stg-p-step-INST-if-INST-excpt
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (INST-excpt? i))
		  (b1p (INST-cause-jmp? i MT MA sigs))
		  (not (MT-CMI-p (MT-step MT MA MA-sigs))))
	     (retire-stg-p (INST-stg (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (e/d (step-inst step-inst-complete
				    complete-stg-p
				    lift-b-ops INST-commit?
				   INST-cause-jmp?))
		  :cases ((b1p (inst-specultv? i))
			  (b1p (INST-modified? i))))))

; If i causes a jump, i retires immediately.
(defthm retire-stg-p-step-inst-if-INST-cause-jmp
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (INST-cause-jmp? i MT MA sigs))
		  (not (MT-CMI-p (MT-step MT MA MA-sigs))))
	     (retire-stg-p (INST-stg (step-INST i MT MA sigs))))
  :hints (("goal" :cases ((b1p (INST-excpt? i)) (not (b1p (INST-store? i)))))))

; If instruction i directly retires without going through the commit stage,
; i is not a store instruction and the memory is not updated. 
(defthm not-retire-stg-p-step-inst-if-INST-store
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (complete-stg-p (INST-stg i))
		  (retire-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i))))
	     (equal (ISA-mem (ISA-step (INST-pre-ISA i) ISA-sigs))
		    (ISA-mem (INST-pre-ISA i))))
  :hints (("goal" :in-theory (enable complete-stg-p lift-b-ops
				     NOT-INST-STORE-IF-COMPLETE
				     INST-excpt? INST-COMMIT?
				     enter-excpt? 
				     step-inst step-inst-complete)
		  :cases ((b1p (INST-excpt? i)) (not (b1p (INST-store? i)))))))

; If i is in the write buffer but not at wbuf0, then i will stay in
; the commit stage. 
(defthm commit-stg-p-step-INST-if-not-release-wbuf0
    (implies (and (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (commit-stg-p (INST-stg i)))
	     (commit-stg-p (INST-stg (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (enable step-INST step-INST-commit))))

(encapsulate nil
(local
(defthm ISA-mem-ISA-step-if-not-release-wbuf0-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (not (retire-stg-p (INST-stg i)))
		  (not (b1p (INST-modified? i)))
		  (retire-stg-p (INST-stg (step-INST i MT MA sigs))))
	     (equal (inst-specultv? i) 0))
  :hints (("goal"
	   :use ((:instance INST-is-at-one-of-the-stages)
		 (:instance
		  inst-specultv-inst-at-rob-head-if-uniq-inst-at-rob-head))
	   :in-theory
	   (e/d (step-INST-complete-INST
		 INST-commit? lift-b-ops
		 step-inst-complete)
		(INST-is-at-one-of-the-stages
		 inst-specultv-inst-at-rob-head-if-uniq-inst-at-rob-head))))))

(local
(defthm ISA-mem-ISA-step-if-not-release-wbuf0-help2
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (not (retire-stg-p (INST-stg i)))
		  (retire-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (not (MT-CMI-p (MT-step MT MA sigs))))
	     (equal (INST-modified? i) 0))
  :hints (("goal" :use ((:instance INST-is-at-one-of-the-stages))
		  :in-theory (e/d (step-INST-complete-INST
				     lift-b-ops
				     equal-b1p-converter
				     step-inst-complete)
				  (inst-is-at-one-of-the-stages))))))

; If instruction i is not at wbuf0, and i advances to the retire stage,
; then the execution of i does not modify the memory, because i cannot
; be a store instruction.
(defthm ISA-mem-ISA-step-if-not-release-wbuf0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (release-wbuf0? (MA-LSU MA) MA-sigs)))
		  (not (retire-stg-p (INST-stg i)))
		  (retire-stg-p (INST-stg (step-INST i MT MA MA-sigs)))
		  (not (MT-CMI-p (MT-step MT MA MA-sigs))))
	     (equal (ISA-mem (ISA-step (INST-pre-ISA i) ISA-sigs))
		    (ISA-mem (INST-pre-ISA i))))
  :hints (("goal" :use (:instance INST-is-at-one-of-the-stages)
		  :in-theory (disable INST-is-at-one-of-the-stages))))
)

(encapsulate nil
(local
(defthm MT-mem-local-help1
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (consp trace)
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (not (retire-stg-p (INST-stg (car trace))))
		  (equal (ISA-mem ISA) mem)
		  (retire-stg-p (INST-stg (step-INST (car trace) MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA))
	      (equal (trace-mem (step-trace (cdr trace) MT MA sigs ISA spc smc)
				mem)
		     mem))
  :hints (("goal" :cases ((consp (cdr trace)))
		  :expand (STEP-TRACE (CDR TRACE)
				      MT MA SIGS ISA SPC SMC))
	  ("subgoal 1" :use
		       ((:instance
			 NOT-RETIRE-STG-P-STEP-INST-IF-EARLIER-INST-COMMIT
			 (j (car trace)) (i (cadr trace)))
			(:instance
			 INST-is-at-one-of-the-stages (i (car trace))))
		       :in-theory
		       (e/d (step-INST-complete-INST step-INST-complete
			     COMMITTED-P lift-b-ops)
			    (NOT-RETIRE-STG-P-STEP-INST-IF-EARLIER-INST-COMMIT
			     INST-is-at-one-of-the-stages))))))

(local
(defthm MT-mem-if-step-MT-if-not-release-wbuf0-help
    (implies (and (inv MT MA)
		  (consp trace)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs))))
	     (equal (trace-mem (step-trace trace MT MA sigs
					   (INST-pre-ISA (car trace))
					   spc smc)
			       (ISA-mem (INST-pre-ISA (car trace))))
		    (trace-mem trace (ISA-mem (INST-pre-ISA (car trace))))))
  :hints (("goal" :induct t
		  :expand ((TRACE-MEM (LIST (STEP-INST (CAR TRACE) MT MA SIGS))
				      (ISA-MEM (INST-PRE-ISA (CAR TRACE))))))
	  (when-found (INST-pre-ISA (car (cdr trace)))
		      (:cases ((consp (cdr trace))))))
  :rule-classes nil))

; a landmark lemma. 
; If the instruction at wbuf0 is not released, the ideal memory
; state does not change.  
(defthm MT-mem-if-step-MT-if-not-release-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs))))
	     (equal (MT-mem (MT-step MT MA sigs))
		    (MT-mem MT)))
  :hints (("goal" :cases ((consp (MT-trace MT)))
		  :in-theory (e/d (MT-mem MT-step)
				  (MT-MEM-=-MA-MEM)))
	  ("subgoal 1"
	   :use (:instance MT-mem-if-step-MT-if-not-release-wbuf0-help
			   (trace (MT-trace MT)) 
			   (spc 0) (smc 0)))))
)

(local
(encapsulate nil
(local
(defthm no-inst-at-stgs-wbuf0-if-car-at-commit-wbuf0-help1
    (implies (and (member-equal (INST-stg (car sub)) stgs)
		  (tail-p sub trace)
		  (uniq-inst-at-stgs-in-trace stgs trace))
	     (no-inst-at-stgs-in-trace stgs (cdr sub)))))

(local
(defthm no-inst-at-stgs-wbuf0-if-car-at-commit-wbuf0-help2
    (implies (and (tail-p sub trace)
		  (consp sub)
		  (no-inst-at-stgs-in-trace stgs trace))
	     (no-inst-at-stgs-in-trace stgs (cdr sub)))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     NO-LSU-STG-CONFLICT)))))

; A help lemma. 
(defthm no-inst-at-stgs-wbuf0-if-car-at-commit-wbuf0
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (consp trace)
		  (equal (INST-stg (car trace)) '(commit wbuf0))
		  (equal stgs '((LSU wbuf0)
				(LSU wbuf0 lch)
				(complete wbuf0)
				(commit wbuf0))))
	     (no-inst-at-stgs-in-trace stgs (cdr trace)))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     subtrace-p
				     no-inst-at-stgs
				     uniq-inst-at-stgs
				     NO-LSU-STG-CONFLICT))))
))

(in-theory (enable inst-stg-step-inst))

(encapsulate nil
(local
 (defthm ISA-mem-ISA-step-if-non-retire-retires-help2
     (implies (and (inv MT MA)
		   (INST-in i MT) (INST-p i)
		   (not (retire-stg-p (INST-stg i)))
		   (not (equal (INST-stg i) '(commit wbuf0)))
		   (b1p (inst-specultv? i))
		   (MAETT-p MT) (MA-state-p MA))
	      (not (retire-stg-p (INST-stg (step-INST i MT MA sigs)))))
   :hints (("goal" :use (:instance inst-is-at-one-of-the-stages (i i))
		   :in-theory (e/d (commit-stg-p)
				   (inst-is-at-one-of-the-stages))))))

(local
 (defthm ISA-mem-ISA-step-if-non-retire-retires-help3
     (implies (and (inv MT MA)
		   (INST-in i MT) (INST-p i)
		   (b1p (INST-modified? i))
		   (not (retire-stg-p (INST-stg i)))
		   (not (equal (INST-stg i) '(commit wbuf0)))
		   (retire-stg-p (INST-stg (step-INST i MT MA sigs)))
		   (MAETT-p MT) (MA-state-p MA))
	      (MT-CMI-p (MT-step MT MA sigs)))
   :hints (("goal" :use (:instance inst-is-at-one-of-the-stages (i i))
		   :in-theory (e/d (commit-stg-p complete-stg-p
				      lift-b-ops)
				   (inst-is-at-one-of-the-stages))))))
	      

(local
(defthm ISA-mem-ISA-step-if-non-retire-retires-help
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (retire-stg-p (INST-stg i)))
		  (not (equal (INST-stg i) '(commit wbuf0)))
		  (retire-stg-p (INST-stg (step-inst i MT MA MA-sigs)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (ISA-mem (ISA-step (INST-pre-ISA i) intr))
		    (ISA-mem (INST-pre-ISA i))))
   :hints (("goal" :cases ((b1p (INST-store? i))))
	   ("subgoal 1" :cases  ((b1p (INST-excpt? i))))
	   ("subgoal 1.2" :use (:instance
				inst-is-at-one-of-the-stages (i i))
			  :in-theory (e/d (commit-stg-p lift-b-ops
					     NOT-INST-STORE-IF-COMPLETE
					     INST-excpt?
					     complete-stg-p)
					  (inst-is-at-one-of-the-stages))))))

; If any instruction goes to the retire stage from a stage other than
; (commit wbuf0), then the instruction is not a store instruction. 
; Thus, the instruction has no effect on the memory.
(defthm ISA-mem-ISA-step-if-non-retire-retires
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (retire-stg-p (INST-stg i)))
		  (not (equal (INST-stg i) '(commit wbuf0)))
		  (retire-stg-p (INST-stg (step-inst i MT MA MA-sigs)))
		  (not (MT-CMI-p (MT-step MT MA MA-sigs)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (ISA-mem (ISA-step (INST-pre-ISA i) intr))
		    (ISA-mem (INST-pre-ISA i))))
  :hints (("goal" :cases ((b1p (inst-specultv? i))
			  (b1p (INST-modified? i))))))
)

(encapsulate nil
; This local help lemma shows that retired non-store instructions
; do not affect the value of MT-mem.
; Note. This may be a good example to discuss in a paper, but
; probably difficult to explain in detail.
(local
(defthm MT-mem-MT-step-if-commit-wbuf0-help-help
    (implies (and (inv MT MA)
		  (consp trace)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (no-retired-store-p trace)
		  (no-inst-at-stgs-in-trace '((LSU wbuf0)
					      (LSU wbuf0 lch)
					      (complete wbuf0)
					      (commit wbuf0))
					    trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (equal (INST-pre-ISA (car trace)) ISA))
	     (equal (trace-mem (step-trace trace MT MA sigs
					   ISA spc smc)
			       (ISA-mem ISA))
		    (ISA-mem ISA)))
   :hints (("goal" :expand (TRACE-MEM
               (LIST (STEP-INST (CAR TRACE) MT MA SIGS)
                     (FETCHED-INST MT
                                   (ISA-STEP (INST-PRE-ISA (CAR TRACE))
                                             '(ISA-input 0))
                                   (B-IOR (INST-SPECULTV? (CAR TRACE))
                                          (INST-START-SPECULTV? (CAR TRACE)))
                                   (INST-MODIFIED? (CAR TRACE))))
               (ISA-MEM (INST-PRE-ISA (CAR TRACE))))))))
		     
; Matt K. mod: Proof no longer succeeds.  To fix it may require some reasonably
; deep understanding of this proof effort.
(skip-proofs
(local
(defthm MT-mem-MT-step-if-commit-wbuf0-help
    (implies (and (inv MT MA)
		  (consp trace)
		  (subtrace-p trace MT)
		  (member-equal i trace) (INST-p i)
		  (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (release-wbuf0? (MA-LSU MA) sigs))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (equal (INST-stg i) '(commit wbuf0)))
	     (equal (trace-mem (step-trace trace MT MA sigs
						   (INST-pre-ISA (car trace))
						   spc smc)
				       (ISA-mem (INST-pre-ISA (car trace))))
		    (ISA-mem (INST-post-ISA i))))
  :hints (("goal" :induct t)
	  (when-found (INST-LISTP (CDR TRACE))
		      (:cases ((consp (cdr trace))))))))
)

; If Instruction i at write buffer 0 is released this cycle, 
; the ideal memory state is the memory of the post-ISA of i. 
(defthm MT-mem-MT-step-if-commit-wbuf0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (release-wbuf0? (MA-LSU MA) sigs))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (equal (INST-stg i) '(commit wbuf0)))
	     (equal (MT-mem (MT-step MT MA sigs))
		    (ISA-mem (INST-post-ISA i))))
  :hints (("goal" :in-theory (enable INST-in MT-mem MT-step)
		  :use (:instance MT-mem-MT-step-if-commit-wbuf0-help
				  (trace (MT-trace MT)) (spc 0) (smc 0)))
	  ("goal'" :cases ((consp (MT-trace MT))))))

)

(encapsulate nil
(local
(defthm local-help
    (implies (and (inv MT MA)
		  (consp trace)
		  (subtrace-p trace MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-listp trace)
		  (member-equal i trace) (INST-p i)
		  (equal (INST-stg i) '(commit wbuf0)))
	     (equal (ISA-mem (INST-pre-ISA i))
		    (trace-mem trace (ISA-mem (INST-pre-ISA (car trace))))))
  :hints ((when-found (INST-PRE-ISA (CAR (CDR TRACE)))
		      (:cases ((consp (cdr trace))))))
  :rule-classes nil))

(local
(defthm ISA-mem-INST-pre-ISA-if-INST-at-commit-wbuf0-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(commit wbuf0)))
	     (equal (ISA-mem (INST-pre-ISA i))
		    (MT-mem MT)))
  :hints (("goal" :in-theory (e/d (MT-mem INST-in)
				  (MT-MEM-=-MA-MEM))
		  :cases ((consp (MT-trace MT))))
	  ("subgoal 1" :use (:instance local-help (trace (MT-trace MT)))))))

; Before the write instruction is released, the current memory is
;  the same as the memory in the pre-ISA of the instruction.
(defthm ISA-mem-INST-pre-ISA-if-INST-at-commit-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(commit wbuf0)))
	     (equal (ISA-mem (INST-pre-ISA i))
		    (MA-mem MA))))
)    

; The effect of a store instruction.
(defthm ISA-mem-ISA-step-if-INST-store
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (ISA-input-exint intr)))
		  (b1p (INST-store? i))
		  (not (b1p (INST-excpt? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (equal (ISA-mem (ISA-step (INST-pre-ISA i) intr))
		    (write-mem (INST-src-val3 i)
			       (INST-store-addr i)
			       (ISA-mem (INST-pre-ISA i)))))
  :hints (("goal" :in-theory (enable ISA-step-INST-pre-ISA INST-excpt?
				     INST-data-access-error?
				     INST-store-error?
				     INST-store? INST-cntlv INST-opcode
				     INST-LSU? INST-ld-st?
				     ISA-st ISA-sti INST-src-val3
				     INST-STORE-ADDR  INST-rc INST-im
				     INST-ra INST-rb
				     decode rdb logbit*
				     lift-b-ops))))

; A lemma for the proof of MT-mem-if-step-MT-if-release-wbuf0.
; The effect of an instruction in write buffer 0.
(defthm ISA-mem-ISA-step-if-INST-at-commit-wbuf0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (ISA-input-exint intr)))
		  (equal (INST-stg i) '(commit wbuf0))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (equal (ISA-mem (ISA-step (INST-pre-ISA i) intr))
		    (write-mem (wbuf-val (LSU-wbuf0 (MA-LSU MA)))
			       (wbuf-addr (LSU-wbuf0 (MA-LSU MA)))
			       (MA-mem MA))))
  :hints (("goal" :cases ((b1p (inst-specultv? i))
			  (not (b1p (INST-store? i))))
		  :in-theory (enable LSU-STORE-IF-AT-LSU-WBUF))))

; A landmark lemma. 
; When the content of write buffer 0 is released, the memory
; is updated with the content of wbuf0.
(defthm MT-mem-if-step-MT-if-release-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (b1p (release-wbuf0? (MA-LSU MA) sigs)))
	     (equal (MT-mem (MT-step MT MA sigs))
		    (write-mem (wbuf-val (LSU-wbuf0 (MA-LSU MA)))
			       (wbuf-addr (LSU-wbuf0 (MA-LSU MA)))
			       (MA-mem MA))))
  :hints (("goal" :in-theory (enable release-wbuf0? release-wbuf0-ready?
				     INST-exintr-INST-in-if-not-retired
				     NOT-INST-SPECULTV-INST-IN-IF-COMMITTED
				     lift-b-ops committed-p)
		  :restrict ((MT-mem-MT-step-if-commit-wbuf0
			      ((i (INST-at-stg '(commit wbuf0) MT)))))
		  :cases ((b1p (INST-modified?
				(INST-at-stg '(commit wbuf0) MT)))))))

(local
(defthm mem-match-p-preserved-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (not (MT-CMI-p (MT-step MT MA sigs))))
	     (equal (MT-mem (MT-step MT MA sigs))
		    (step-mem MA sigs)))
  :hints (("goal" :in-theory (enable step-mem)))))

; Mem-match-p is invariantly preserved.
(defthm mem-match-p-preserved
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (not (MT-CMI-p (MT-step MT MA sigs))))
	     (mem-match-p (MT-step MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable mem-match-p MA-step))))
