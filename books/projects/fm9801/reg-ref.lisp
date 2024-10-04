;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; MI-inv.lisp
; Author  Jun Sawada, University of Texas at Austin
;
;  This book proves the invariant properties consistent-reg-tbl-p and
;  consistent-sreg-tbl-p, and consistent-RS-entry-p.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "ACL2")

(include-book "MA2-lemmas")
(include-book "MAETT-lemmas")
(include-book "modifier")

(deflabel begin-reg-ref)
;  This book proves the invariant condition about Tomasulo's tags.
;  
;  Index.
;    Proof of consistent-reg-tbl-p
;      Base case 
;        consistent-reg-ref-p-init-MT
;      Induction Case   
;          not-LRM-in-ROB-MT-step-if-not-reg-ref-wait
;          LRM-in-ROB-MT-step-if-reg-ref-wait
;          LRM-in-ROB-MT-step
;            INST-tag-LRM-MT-step-if-not-dispatch-inst
;            INST-tag-LRM-MT-step-if-not-reg-modifier
;            INST-tag-LRM-MT-step-if-dispatch-inst
;          consistent-reg-ref-p-MT-step
;        consistent-reg-tbl-p-preserved
;    Proof of consistent-sreg-tbl-p
;      Base Case
;        consistent-sreg-tbl-p-init-MT
;      Inductive case (not yet commented properly)
;           not-LSRM-in-ROB-MT-step-if-not-reg-ref-wait
;           LSRM-in-ROB-MT-step-if-reg-ref-wait
;           LSRM-in-ROB-MT-step 
;             INST-tag-LSRM-MT-step-if-not-dispatch-inst
;             INST-tag-LSRM-MT-step-if-not-sreg-modifier
;             INST-tag-LSRM-MT-step-if-dispatch-inst
;           INST-tag-LSRM-MT-step
;         consistent-sreg-ref-p-MT-step
;        consistent-sreg-tbl-p-preserved 
;    
;    Proof of consistent-RS-p
;        Rules about Common Data Bus and instruction stage.
;        Rewriting Rules derived from consistent-RS-p
;        Proof of the existence of the register modifiers. 
;          e.g. exist-LRM-before-p-step-INST-operand0-ra
;        Proof of lemmas about dispatched instructions.
;          e.g. INST-tag-LRM-before-step-INST-logbit0-ra
;        Proof of lemmas about idling instructions.
;          e.g. execute-stg-p-LRM-before-step-INST-if-logbit0-ra
;        Case analysis on the old and new stage of i
;          e.g. consistent-IU-RS0-p-step-INST-DQ0
;      consistent-RS-entry-p-step-INST
; 

(in-theory (disable (:REWRITE NOT-ROB-EMPTY-IF-INST-IS-EXECUTED . 1)
		    NOT-EX-INTR-IF-ROB-NOT-EMPTY))

(in-theory
 (disable (:rewrite not-member-equal-cdr-if-car-is-not-dispatched . 1)
	  (:rewrite not-member-equal-cdr-if-car-is-not-commit . 1)
	  (:rewrite INST-at-DQ-0-is-first-non-dispatched-inst . 1)))

(in-theory
 (enable (:rewrite not-member-equal-cdr-if-car-is-not-dispatched . 2)
	 (:rewrite not-member-equal-cdr-if-car-is-not-commit . 2)
	 (:rewrite INST-at-DQ-0-is-first-non-dispatched-inst . 2)))

(local
(defthm uniq-inst-at-DQ0-if-dispatch-inst
    (implies (and (inv MT MA)
		  (b1p (dispatch-inst? MA))
		  (MAETT-p MT) (MA-state-p MA))
	     (uniq-inst-at-stg '(DQ 0) MT))
  :hints (("Goal" :in-theory (enable lift-b-ops
				     DQ-ready-no-unit? DQ-ready-to-IU?
				     DQ-ready-to-MU? DQ-ready-to-BU?
				     DQ-ready-to-LSU?
				     dispatch-inst? dispatch-no-unit?
				     dispatch-to-IU? dispatch-to-MU?
				     dispatch-to-LSU? dispatch-to-BU?)))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Proof of consistent-reg-tbl-p
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Proof of consistent-reg-tbl-p for initial states
(encapsulate nil
(local
(defthm reg-ref-empty-if-MA-flushed-help
    (implies (and (b1p (reg-tbl-empty-under? index2 DQ))
		  (integerp index1) (integerp index2)
		  (<= 0 index1) (< index1 index2))
	     (b1p (reg-ref-empty? index1 DQ)))
  :hints (("goal" :in-theory (enable lift-b-ops)))))

; If MA is flushed, the valid flags of register reference table are all 0.
(defthm reg-ref-empty-if-MA-flushed
    (implies (and (b1p (MA-flushed? MA)) (rname-p index))
	     (b1p (reg-ref-empty? index (MA-DQ MA))))
  :hints (("goal" :in-theory (enable MA-flushed? DQ-empty?
				     lift-b-ops rname-p
				     reg-tbl-empty?))))
)

(encapsulate nil
(local
(defthm consistent-reg-ref-p-init-MT-help
    (implies (and (MA-state-p MA) (b1p (reg-ref-empty? index (MA-DQ MA))))
	     (consistent-reg-ref-p index (init-MT MA) MA))
  :hints (("goal" :in-theory (enable reg-ref-empty? lift-b-ops
				     consistent-reg-ref-p
				     INIT-MT exist-LRM-in-ROB-p)))))

; Register reference table satisfies consistent-reg-ref-p,
; when MA is flushed.  Simply a clean (no valid entry) reference table is
; consistent.  
(defthm consistent-reg-ref-p-init-MT
    (implies (and (MA-state-p MA) (b1p (MA-flushed? MA))  (rname-p index))
	     (consistent-reg-ref-p index (init-MT MA) MA)))
)

(encapsulate nil
(local
(defthm consistent-reg-tbl-p-init-MT-help
    (implies (and (MA-state-p MA) (b1p (MA-flushed? MA))
		  (integerp index) (<= 0 index) (<= index *num-regs*))
	     (consistent-reg-tbl-under index (init-MT MA) MA))
  :hints (("goal" :in-theory (enable rname-p unsigned-byte-p)))))

; consistent-reg-tbl-p is true for the initial MAETT. 
(defthm consistent-reg-tbl-p-init-MT
    (implies (and (MA-state-p MA) (b1p (MA-flushed? MA)))
	     (consistent-reg-tbl-p (init-MT MA) MA))
  :hints (("goal" :in-theory (enable consistent-reg-tbl-p))))
)

;; Invariant proof
(encapsulate nil
(local
(defun induct-help (i tbl)
  (if (endp tbl)
      (cons i tbl)
      (induct-help (1+ i) (cdr tbl)))))

(local
(defthm rname-idempotent
    (implies (and (integerp i) (<= 0 i)  (< i *num-regs*))
	     (equal (rname i) i))
  :hints (("Goal" :in-theory (enable rname loghead)))))

(local
(defthm reg-tbl-nth-step-DQ-help
    (implies (and (integerp i) (<= 0 i)
		  (integerp idx) (<= 0 idx)
		  (<= i idx) (< idx *num-regs*)
		  (< (- idx i) (len tbl)))
	     (equal (nth (- idx i) (step-reg-list tbl i MA sigs))
		    (step-reg-ref (nth (- idx i) tbl)
				  idx MA sigs)))
  :hints (("goal" :induct (induct-help i tbl)
		  :in-theory (e/d (STEP-REG-LIST) ()))
	  (when-found (car tbl)
		      (:expand (STEP-REG-LIST TBL I MA SIGS)))
	  (when-found (cdr tbl)
		      (:expand (STEP-REG-LIST TBL I MA SIGS))))
  :rule-classes nil))

; This is a rule to open up the definition of step-DQ.
(defthm reg-tbl-nth-step-DQ
    (implies (and (MA-state-p MA) (rname-p idx))
	     (equal (reg-tbl-nth idx (DQ-reg-tbl (step-DQ MA sigs)))
		    (step-reg-ref (reg-tbl-nth idx (DQ-reg-tbl (MA-DQ MA)))
				  idx MA sigs)))
  :hints (("goal" :in-theory (enable step-DQ step-reg-tbl unsigned-byte-p
				     rname-p reg-tbl-nth)
		  :use (:instance reg-tbl-nth-step-DQ-help
				  (idx idx) (i 0)
				  (tbl (DQ-reg-tbl (MA-DQ MA)))))))
)

; The instruction i is the oldest non-committed instruction.  Only when i
; commits, flush-all? can be 1.  I must be the instruction that causes the
; flush-all.
(defthm commit-inst-step-inst-if-flush-all
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MT-all-commit-before i MT)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (INST-exintr-now? i MA sigs)))
		  (b1p (flush-all? MA sigs)))
	     (committed-p (step-INST i MT MA sigs)))
  :hints (("Goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (COMMITTED-P)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm not-LRM-in-ROB-MT-step-if-flush-all-help
    (implies (and (inv MT MA)
		  (MT-all-commit-before-trace trace MT)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (flush-all? MA sigs)))
	     (not (trace-exist-LRM-in-ROB-p idx
					    (step-trace trace MT MA sigs
							ISA spc smc))))
  :hints (("goal" :in-theory (enable committed-p))
	  (when-found (MT-ALL-COMMIT-BEFORE-TRACE (CDR TRACE) MT)
		      (:cases ((committed-p (car trace))))))))

; No register modifier will be in the ROB after a flush-all.
; This is used to prove the consistent-reg-ref-p
(defthm not-LRM-in-ROB-MT-step-if-flush-all
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (flush-all? MA sigs)))
	     (not (exist-LRM-in-ROB-p idx (MT-step MT MA sigs))))
  :hints (("Goal" :in-theory (enable exist-LRM-in-ROB-p))))
)

; To determine whether the newly dispatched instruction is a register
; modifier, we only have to check the wb? field and wb-sreg? field of
; the control vector coming out of dispatcher. (dispatch-cntlv MA)
; is the cntlv vector output from the dispatch logic.  If wb? is 0
; or wb-sreg is 1, the dispatched instruction is not a register
; modifier. 
(defthm not-reg-modifier-if-not-cntlv-wb
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (b1p (dispatch-inst? MA))
		  (not (b1p (INST-specultv? (INST-at-stg '(DQ 0) MT))))
		  (not (b1p (INST-modified? (INST-at-stg '(DQ 0) MT))))
		  (not (INST-fetch-error-detected-p (INST-at-stg '(DQ 0) MT)))
		  (or (not (b1p (cntlv-wb? (dispatch-cntlv MA))))
		      (b1p (cntlv-wb-sreg? (dispatch-cntlv MA)))))
	     (not (reg-modifier-p idx (INST-at-stg '(DQ 0) MT))))
  :hints (("Goal" :in-theory (enable dispatch-cntlv reg-modifier-p
				     dispatch-inst? DISPATCH-NO-UNIT?
				     dispatch-to-IU? dispatch-to-MU?
				     dispatch-to-BU? dispatch-to-LSU?
				     DQ-READY-NO-UNIT? DQ-READY-TO-BU?
				     DQ-READY-TO-IU? DQ-READY-TO-LSU?
				     DQ-READY-TO-MU?
				     INST-WB-SREG? INST-WB?
				     lift-b-ops))))

(local
(defthm not-trace-LRM-in-ROB-MT-step-if-no-dispatch
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rname-p idx)
		  (not (trace-exist-LRM-in-ROB-p idx trace))
		  (not (b1p (dispatch-inst? MA))))
	     (not (trace-exist-LRM-in-ROB-p idx
		       (step-trace trace MT MA sigs ISA spc smc))))))

; There will be no register modifier in the ROB in the next cycle
; if no modifiers are in the ROB in this cycle, and no new instruction is
; dispatched.  
(defthm not-LRM-in-ROB-MT-step-if-no-dispatch
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rname-p idx)
		  (not (exist-LRM-in-ROB-p idx MT))
		  (not (b1p (dispatch-inst? MA))))
	     (not (exist-LRM-in-ROB-p idx (MT-step MT MA sigs))))
  :hints (("Goal" :in-theory (enable exist-LRM-in-ROB-p MT-step))))

; If i is not at DQ0, it won't be dispatched in this cycle.
(defthm not-dispatched-inst-step-inst-if-not-DQ0
    (implies (and (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (INST-p i)
		  (not (dispatched-p i))
		  (not (equal (INST-stg i) '(DQ 0))))
	     (not (dispatched-p (step-inst i MT MA sigs))))
  :hints (("Goal" :in-theory (enable dispatched-p*
				     step-inst-dq-inst
				     step-inst-dq
				     DQ-STG-P))))

(in-theory (enable uniq-inst-at-INST-stg-if-INST-in))

(local
(encapsulate nil
(local
 (defthm local-help
     (implies (and (inv MT MA)
		   (INST-in i MT) (INST-p i)
		   (INST-in j MT) (INST-p j)
		   (INST-in-order-p i j MT)
		   (not (equal i j))
		   (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		   (DQ-stg-p (INST-stg i)) (DQ-stg-p (INST-stg j)))
	      (DQ-stg-p (INST-stg (step-INST j MT MA sigs))))
 :hints (("Goal" :in-theory (enable DQ-stg-p step-inst-dq-inst
				    step-inst-low-level-functions)
		 :use ((:instance uniq-stage-inst)
		       (:instance DQ-stg-index-monotonic))))))

(local
 (defthm not-dispatched-inst-step-inst-if-earlier-non-dispatched
     (implies (and (inv MT MA)
		   (INST-in i MT) (INST-p i)
		   (INST-in j MT) (INST-p j)
		   (INST-in-order-p i j MT)
		   (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		   (not (dispatched-p i)))
	      (not (dispatched-p (step-inst j MT MA sigs))))
   :hints (("Goal" :in-theory (e/d (dispatched-p* IFU-IS-LAST-INST)
				   (inst-is-at-one-of-the-stages))
		   :restrict ((local-help ((i i))))
		   :use (:instance inst-is-at-one-of-the-stages
			 (i j)))
	   (when-found (DQ-stg-p (INST-stg j))
		       (:cases ((equal i j)))))))
		  
; A local lemma. 
(defthm not-trace-LRM-in-ROB-step-trace
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (INST-in i MT) (INST-p i)
		  (not (dispatched-p i))
		  (subtrace-after-p i trace MT)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (not (trace-exist-LRM-in-ROB-p idx
			(step-trace trace MT MA sigs ISA spc smc)))))
))

(local
(defthm not-trace-LRM-in-ROB-MT-step-if-not-reg-modifier
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rname-p idx)
		  (not (trace-exist-LRM-in-ROB-p idx trace))
		  (not (reg-modifier-p idx (INST-at-stg-in-trace '(DQ 0)
								 trace))))
	     (not (trace-exist-LRM-in-ROB-p idx
			 (step-trace trace MT MA sigs ISA spc smc))))
  :hints (("Goal" :in-theory (enable dispatched-p)
		  :restrict ((not-trace-LRM-in-ROB-step-trace
			      ((i (car trace)))))))))

; If there is no register modifier in the ROB in the current cycle, and the
; instruction at DQ0 is not a register modifier,
; there will be no register modifier in the ROB in the next cycle. 
(defthm not-LRM-in-ROB-MT-step-if-not-reg-modifier
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rname-p idx)
		  (not (exist-LRM-in-ROB-p idx MT))
		  (not (reg-modifier-p idx (INST-at-stg '(DQ 0) MT))))
	     (not (exist-LRM-in-ROB-p idx (MT-step MT MA sigs))))
  :hints (("Goal" :in-theory (enable exist-LRM-in-ROB-p
				     INST-at-stg))))

; INST-start-specultv? for a particular instruction i does not
; change after stepping the instruction.
;
; INST-start-specultv? is 1 for the instruction that starts
; speculative execution. For instance, a mispredicted branch starts a
; speculation.  Thus, instruction in IFU stage may change the value of
; INST-start-specultv? when branch prediction makes a wrong choice.
; Another possibility is that the instruction abandons the following
; instructions and starts the execution of the correct branch all over
; again.  This happens only when an instruction commits, and it happens 
; only when flush-all? is 1. Except these cases, the value
; of INST-start-specultv?  does not change.
;
; Note:
; If the instruction is at the execute stage, this is true from the
; definition of INST-start-specultv?.  If it is at complete-stg-p,
; the instruction will not retire because flush-all? is off.  Therefore,
; the value of INST-start-specultv? does not change.
(defthm INST-start-speculative-if-not-flush-all
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (dispatched-p i)
		  (not (committed-p i))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (INST-specultv? i)))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (INST-start-specultv? (step-INST i MT MA sigs))
		    (INST-start-specultv? i)))
  :hints (("Goal" :in-theory (e/d (dispatched-p committed-p
				     equal-b1p-converter)
				  (inst-is-at-one-of-the-stages))
		  :cases ((b1p (INST-modified? i))))
	  ("subgoal 1" :cases ((committed-p (step-INST i MT MA sigs))))
	  ("subgoal 1.1" :in-theory (e/d (dispatched-p committed-p
					    step-inst-low-level-functions
					    step-inst-complete-inst
					    lift-b-ops
					    equal-b1p-converter
				     step-inst-complete-inst)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm MT-modified-at-dispatch-MT-step-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (b1p (trace-modified-at-dispatch? trace))
		  (not (b1p (flush-all? MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (trace-modified-at-dispatch?
		     (step-trace trace MT MA sigs ISA spc smc))
		    1))))

; If the processor is executing modified instruction stream at
; the dispatching boundary, it will continue to execute modified stream
; unless flush-all? is true. 
(defthm MT-modified-at-dispatch-MT-step
    (implies (and (inv MT MA)
		  (b1p (MT-modified-at-dispatch? MT))
		  (not (b1p (flush-all? MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (MT-modified-at-dispatch? (MT-step MT MA sigs)) 1))
  :hints (("goal" :in-theory (enable MT-modified-at-dispatch?))))
)

; If the processor is executing speculatively at the dispatching boundary. 
; the instruction at (DQ 0) is a speculative instruction.
(defthm INST-specultv-INST-at-DQ0-if-MT-specultv-at-dispatch
    (implies (and (inv MT MA)
		  (b1p (MT-specultv-at-dispatch? MT))
		  (uniq-inst-at-stg '(DQ 0) MT)
		  (MAETT-p MT) (MA-state-p MA)) 
	     (equal (INST-specultv? (INST-at-stg '(DQ 0) MT)) 1))
  :hints (("Goal"
	   :restrict
	   ((MT-specultv-at-dispatch-off-if-non-specultv-inst-in
	     ((i (INST-at-stg '(DQ 0) MT)))))
	   :in-theory
	   (enable dispatched-p
		   MT-specultv-at-dispatch-off-if-non-specultv-inst-in
		   equal-b1p-converter))))

; The processor is executing modified instruction stream at the
; dispatch boundary, the instruction at DQ0 is in the modified instruction
; stream. 
(defthm INST-modified-INST-at-DQ0-if-MT-CMI
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg '(DQ 0) MT)
		  (b1p (MT-modified-at-dispatch? MT)))
	     (equal (INST-modified? (INST-at-stg '(DQ 0) MT)) 1))
  :hints (("Goal" :in-theory
		  (enable equal-b1p-converter
		  INST-modified-at-dispatch-off-if-undispatched-inst-in)
		  :restrict
		  ((INST-modified-at-dispatch-off-if-undispatched-inst-in
		    ((i (INST-at-stg '(DQ 0) MT))))))))

(encapsulate nil
(local
(defthm DQ0-is-dispatched
    (implies (and (INST-p i) (equal (INST-stg i) '(DQ 0)))
	     (not (dispatched-p i)))
  :hints (("Goal" :in-theory (enable dispatched-p)))))

(local
(defthm MT-specultv-at-dispatch-MT-step-if-specultv-dispatch-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (member-equal i trace) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-inst? MA))
		  (b1p (INST-specultv? i))
		  (equal (INST-stg i) '(DQ 0))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (trace-specultv-at-dispatch?
		     (step-trace trace MT MA sigs ISA spc smc))
		    1))
  :hints (("Goal" :in-theory (enable lift-b-ops)))))

; If the instruction at DQ0 is speculatively executed, and the
; instruction is dispatched in this cycle, the processor will be
; executing a speculative instruction stream at the dispatching
; boundary.
(defthm MT-specultv-at-dispatch-MT-step-if-specultv-dispatch
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (INST-specultv? i))
		  (b1p (dispatch-inst? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (MAETT-p MT) (MA-state-p MA)) 
	     (equal (MT-specultv-at-dispatch? (MT-step MT MA sigs)) 1))
  :hints (("Goal" :in-theory (e/d (MT-specultv-at-dispatch?
				   INST-in)
				  ()))))
)

; If the processor is not executing speculatively at the dispatching
; boundary, the instruction at DQ0 is not speculatively executed. 
(defthm INST-specultv-INST-at-DQ0-if-dispatch-inst
    (implies (and (inv MT MA)
		  (b1p (dispatch-inst? MA))
		  (not (b1p (flush-all? MA sigs)))
		  (uniq-inst-at-stg '(DQ 0) MT)
		  (not (b1p (MT-specultv-at-dispatch?
			     (MT-step MT MA sigs))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-specultv? (INST-at-stg '(DQ 0) MT)) 0))
  :hints (("Goal" :in-theory (enable equal-b1p-converter)
		  :restrict
		  ((MT-specultv-at-dispatch-MT-step-if-specultv-dispatch
		    ((i (INST-at-stg '(DQ 0) MT))))))))

(encapsulate nil
(local
(defthm MT-specultv-at-dispatch-MT-step-if-fetch-error-detected-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (equal (INST-stg i) '(DQ 0))
		  (member-equal i trace) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-inst? MA))
		  (b1p (INST-start-specultv? i))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (trace-specultv-at-dispatch?
		     (step-trace trace MT MA sigs ISA spc smc)) 
		    1))
  :hints (("Goal" :in-theory (enable lift-b-ops)))))

; If a fetch error has been detected with the dispatched instruction,
; then the processor starts executing instructions speculatively at the
; dispatching boundary from the next cycle.   Note that the
; instructions following an exception are considered to be speculatively
; executed. 
(defthm MT-specultv-at-dispatch-MT-step-if-fetch-error-detected
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)  
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-inst? MA))
		  (INST-fetch-error-detected-p i)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (MT-specultv-at-dispatch? (MT-step MT MA sigs))
		    1))
  :hints (("Goal" :in-theory (enable INST-start-specultv? INST-excpt?
				     INST-in lift-b-ops
				     MT-specultv-at-dispatch?)
		  :cases ((b1p (INST-fetch-error? i))))))
)

; Contrapositive of MT-specultv-at-dispatch-MT-step-if-fetch-error-detected
(defthm INST-fetch-error-INST-at-DQ0-if-dispatch-inst
    (implies (and (inv MT MA)
		  (b1p (dispatch-inst? MA))
		  (not (b1p (flush-all? MA sigs)))
		  (uniq-inst-at-stg '(DQ 0) MT)
		  (not (b1p (MT-specultv-at-dispatch?
			     (MT-step MT MA sigs))))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (not (INST-fetch-error-detected-p (INST-at-stg '(DQ 0) MT))))
  :hints (("Goal" :restrict
		  ((MT-specultv-at-dispatch-MT-step-if-fetch-error-detected
		    ((i (INST-at-stg '(DQ 0) MT))))))))

(encapsulate nil
(local
(defthm MT-modified-at-dispatch-MT-step-if-dispatch-inst-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (member-equal i trace) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-inst? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (b1p (INST-modified? i))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (trace-modified-at-dispatch?
		     (step-trace trace MT MA sigs ISA spc smc))
		    1))))

; If instruction at DQ0 is a modified instruction that is dispatched in
; this cycle, the processor will be executing a modified stream of
; instructions at dispatching boundary in the next cycle.
(defthm MT-modified-at-dispatch-MT-step-if-dispatch-inst
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-inst? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (b1p (INST-modified? i)))
	     (equal  (MT-modified-at-dispatch? (MT-step MT MA sigs)) 1))
  :hints (("Goal" :in-theory (enable MT-modified-at-dispatch? INST-in))))
)

; Contrapositive of MT-modified-at-dispatch-MT-step-if-dispatch-inst
(defthm INST-modified-INST-at-DQ0-if-dispatch-inst
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (b1p (flush-all? MA sigs)))
		  (uniq-inst-at-stg '(DQ 0) MT)
		  (b1p (dispatch-inst? MA))
		  (not (b1p (MT-modified-at-dispatch? (MT-step MT MA sigs)))))
	     (equal (INST-modified? (INST-at-stg '(DQ 0) MT)) 0))
  :hints (("Goal" :restrict
		  ((MT-modified-at-dispatch-MT-step-if-dispatch-inst
		    ((i (INST-at-stg '(DQ 0) MT)))))
		  :in-theory (enable equal-b1p-converter))))

(local
(defthm MT-specultv-at-dispatch-MT-step-contra
    (implies (and (inv MT MA)
		  (not (b1p (MT-specultv-at-dispatch?
			     (MT-step MT MA sigs))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (not (b1p (flush-all? MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (MT-specultv-at-dispatch? MT) 0))
  :hints (("goal" :in-theory (enable equal-b1p-converter)))))

(local
(defthm MT-modified-at-dispatch-MT-step-contra
    (implies (and (inv MT MA)
		  (not (b1p (MT-modified-at-dispatch?
			     (MT-step MT MA sigs))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (not (b1p (flush-all? MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (MT-modified-at-dispatch? MT) 0))
  :hints (("Goal" :in-theory (enable equal-b1p-converter)))))

; This is an important lemma.  If an instruction is dispatched, and
; if it is a register modifier of register idx, the value of the
; signal dispatch-dest-reg from the dispatch logic is idx.
; In other words, dispatch-dest-reg designates the destination register
; of the dispatched instruction. 
(defthm not-reg-modifier-if-not-dispatch-dest-reg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (b1p (dispatch-inst? MA))
		  (not (b1p (INST-specultv? (INST-at-stg '(DQ 0) MT))))
		  (not (b1p (INST-modified? (INST-at-stg '(DQ 0) MT))))
		  (not (INST-fetch-error-detected-p (INST-at-stg '(DQ 0) MT)))
		  (not (equal idx (dispatch-dest-reg MA))))
	     (not (reg-modifier-p idx (INST-at-stg '(DQ 0) MT))))
  :hints (("Goal" :in-theory (e/d (reg-modifier-p dispatch-dest-reg
				     DQ-out-dest-reg
						  dispatch-inst?
						  INST-DEST-REG
						  INST-CNTLV
						  INST-OPCODE
						  DECODE rdb logbit*
						  INST-wb? 
				     lift-b-ops)
				  (DE-VALID-CONSISTENT)))))

; Yet another complicated lemma.  Let us consider register idx.
; Suppose the register reference table has wait? flag set to 0 for
; idx, which suggests no instruction in the ROB is modifying register
; idx.  Further suppose dispatch-dest-reg, an output from the
; dispatching logic, is not idx.  This implies that the dispatched
; instruction does not modify idx, either.  Thus, there is no register
; modifier in the ROB in the next cycle.
(defthm not-LRM-in-ROB-MT-step-if-dispatch-dest-reg-differs
    (implies (and (inv MT MA)
		  (not (b1p (reg-ref-wait?
			     (reg-tbl-nth idx (DQ-reg-tbl (MA-DQ MA))))))
		  (not (equal idx (dispatch-dest-reg MA)))
		  (not (b1p (flush-all? MA sigs)))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (not (b1p (MT-specultv-at-dispatch?
			     (MT-step MT MA sigs))))
		  (not (b1p (MT-modified-at-dispatch?
			     (MT-step MT MA sigs))))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rname-p idx))
	     (not (exist-LRM-in-ROB-p idx (MT-step MT MA sigs))))
  :hints (("Goal" :cases ((b1p (dispatch-inst? MA))))))

; If the ROB is writing its value to the register file, and I is the
; instruction at the head of the ROB, then I is committing in this
; cycle.
(defthm INST-commit-LRM-in-ROB
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (b1p (ROB-write-reg? (MA-ROB MA)))
		  (dispatched-p i)
		  (not (committed-p i))
		  (equal (MT-ROB-head MT) (INST-tag i))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-commit? i MA) 1))
  :Hints (("Goal" :in-theory (enable ROB-write-reg? INST-commit?
				     commit-inst?
				     INST-commit? equal-b1p-converter
				     committed-p dispatched-p
				     lift-b-ops))))

(local
(encapsulate nil
(local
 (defthm committed-p-step-inst-if-following-inst-commit
     (implies (and (inv MT MA)
		   (b1p (INST-commit? i MA))
		   (INST-in i MT) (INST-p i)
		   (INST-in j MT) (INST-p j) 
		   (INST-in-order-p j i MT)
		   (MAETT-p MT) (MA-state-p MA))
	      (committed-p (step-INST j MT MA sigs)))
   :hints (("Goal" :in-theory (enable INST-commit? lift-b-ops)
		   :use (:instance UNCOMMITTED-INST-P-IS-AFTER-MT-ROB-HEAD
				   (i j))))))

; a help lemma
(defthm commit-inst-step-inst-car-if-LRM-commit
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (subtrace-p trace MT) (INST-listp trace)
		  (subtrace-after-p i trace MT)
		  (trace-exist-LRM-in-ROB-p idx trace)
		  (b1p (INST-commit?
			(trace-LRM-in-ROB idx trace) MA))
		  (MAETT-p MT) (MA-state-p MA))
	     (committed-p (step-inst i MT MA sigs))))
))

(encapsulate nil		      
(local
(defthm LRM-in-ROB-MT-step-if-inst-commit-LRM-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (rname-p idx)
		  (not (b1p (dispatch-inst? MA)))
		  (trace-exist-LRM-in-ROB-p idx trace)
		  (b1p (inst-commit?
			(trace-LRM-in-ROB idx trace) MA))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (not (trace-exist-LRM-in-ROB-p idx
			(step-trace trace MT MA sigs ISA spc smc))))
  :hints (("Goal" :restrict
		  ((commit-inst-step-inst-car-if-LRM-commit
		    ((trace (cdr trace)))))))))

; If the last register modifier in the ROB is committing, and no new
; modifier is dispatched, there will be no register modifier in the
; ROB, because no more modifier is left in the ROB.
(defthm LRM-in-ROB-MT-step-if-inst-commit-LRM
    (implies (and (inv MT MA)
		  (not (b1p (dispatch-inst? MA)))
		  (exist-LRM-in-ROB-p idx MT)
		  (b1p (inst-commit? (LRM-in-ROB idx MT) MA))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rname-p idx))
	     (not (exist-LRM-in-ROB-p idx (MT-step MT MA sigs))))
  :hints (("Goal" :in-theory (enable exist-LRM-in-ROB-p
				     LRM-in-ROB))))
)

(encapsulate nil
(local
(defthm LRM-in-ROB-MT-step-if-inst-commit-LRM-2-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (not (reg-modifier-p idx
				       (inst-at-stg-in-trace '(DQ 0) trace)))
		  (trace-exist-LRM-in-ROB-p idx trace)
		  (b1p (inst-commit? (trace-LRM-in-ROB idx trace)
				     MA))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rname-p idx))
	     (not (trace-exist-LRM-in-ROB-p idx
		       (step-trace trace MT MA sigs ISA spc smc))))
  :hints (("Goal" :restrict
		  ((commit-inst-step-inst-car-if-LRM-commit
		    ((trace (cdr trace)))))))))

; Similar to LRM-in-ROB-MT-step-if-inst-commit-LRM,
; except that there may be a dispatched instruction, but it is not
; modifying register idx. 
(defthm LRM-in-ROB-MT-step-if-inst-commit-LRM-2
    (implies (and (inv MT MA)
		  (not (reg-modifier-p idx (inst-at-stg '(DQ 0) MT)))
		  (exist-LRM-in-ROB-p idx MT)
		  (b1p (inst-commit? (LRM-in-ROB idx MT) MA))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rname-p idx))
	     (not (exist-LRM-in-ROB-p idx (MT-step MT MA sigs))))
  :hints (("Goal" :in-theory (enable exist-LRM-in-ROB-p
				     LRM-in-ROB
				     INST-at-stg))))
)

; If the last register modifier is not at the head of the ROB, it
; does not commit this cycle. 
(defthm not-INST-commit-LRM-in-ROB-if-not-ROB-head
    (implies (and (inv MT MA)
		  (not (equal (MT-ROB-head MT)
			      (INST-tag (LRM-in-ROB idx MT))))
		  (exist-LRM-in-ROB-p idx MT)
		  (MAETT-p MT) (MA-state-p MA) (rname-p idx))
	     (equal (INST-commit? (LRM-in-ROB idx MT) MA) 0))
  :hints (("Goal" :in-theory (enable INST-commit? equal-b1p-converter
				     lift-b-ops))))

; Last register modifier in the ROB is a writeback instruction.
(defthm INST-wb-LRM-in-ROB
    (implies (exist-LRM-in-ROB-p idx MT)
	     (equal (INST-wb? (LRM-in-ROB idx MT)) 1))
  :hints (("Goal" :in-theory (e/d (reg-modifier-p equal-b1p-converter)
				  (reg-modifier-p-LRM-in-ROB))
		  :use (:instance reg-modifier-p-LRM-in-ROB))))

; The last (general) register modifier in the ROB is not a writeback
; instruction to a special register.
(defthm INST-wb-sreg-LRM-in-ROB
    (implies (exist-LRM-in-ROB-p idx MT)
	     (equal (INST-wb-sreg? (LRM-in-ROB idx MT)) 0))
  :hints (("Goal" :in-theory (e/d (reg-modifier-p equal-b1p-converter)
				  (reg-modifier-p-LRM-in-ROB))
		  :use (:instance reg-modifier-p-LRM-in-ROB))))

; The last special register modifier is a writeback instruction. 
(defthm INST-wb-LSRM-in-ROB
    (implies (exist-LSRM-in-ROB-p idx MT)
	     (equal (INST-wb? (LSRM-in-ROB idx MT)) 1))
  :hints (("Goal" :in-theory (e/d (sreg-modifier-p equal-b1p-converter)
				  (sreg-modifier-p-LSRM-in-ROB))
		  :use (:instance sreg-modifier-p-LSRM-in-ROB))))

; The last special register modifier writes back into a special register. 
(defthm INST-wb-sreg-LSRM-in-ROB
    (implies (exist-LSRM-in-ROB-p idx MT)
	     (equal (INST-wb-sreg? (LSRM-in-ROB idx MT)) 1))
  :hints (("Goal" :in-theory (e/d (sreg-modifier-p equal-b1p-converter)
				  (sreg-modifier-p-LSRM-in-ROB))
		  :use (:instance sreg-modifier-p-LSRM-in-ROB))))
  
(encapsulate nil
(local
(defthm ROBE-WB-INST-WB-special
    (implies (and (inv MT MA)
		  (equal (MT-rob-head MT) (INST-tag i))
		  (INST-in i MT) (INST-p i)
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (INST-specultv? i)))
		  (dispatched-p i) (not (committed-p i))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (robe-wb? (nth-robe (MT-rob-head MT) (MA-rob MA)))
		    (INST-wb? i)))))

(local
(defthm ROBE-WB-INST-WB-SREG-special
    (implies (and (inv MT MA)
		  (equal (MT-rob-head MT) (INST-tag i))
		  (INST-in i MT) (INST-p i)
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (INST-specultv? i)))
		  (dispatched-p i) (not (committed-p i))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (robe-wb-sreg? (nth-robe (MT-rob-head MT) (MA-rob MA)))
		    (INST-wb-sreg? i)))))

(local
 (defthm ROBE-EXCPT-INST-EXCPT-FLAGS-special
    (implies (and (inv MT MA)
		  (equal (MT-ROB-head MT) (INST-tag i))
		  (complete-stg-p (INST-stg i))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (INST-specultv? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)) 
	     (equal (robe-excpt (nth-robe (MT-ROB-head MT) (MA-rob MA)))
		    (INST-excpt-flags i)))))

(local
(defthm not-INST-commit-LRM-in-ROB-help
    (implies (and (inv MT MA)
		  (not (b1p (ROB-write-reg? (MA-ROB MA))))
		  (not (b1p (INST-specultv? (LRM-in-ROB idx MT))))
		  (not (b1p (INST-modified? (LRM-in-ROB idx MT))))
		  (not (b1p (INST-excpt? (LRM-in-ROB idx MT))))
		  (exist-LRM-in-ROB-p idx MT)
		  (MAETT-p MT) (MA-state-p MA) (rname-p idx))
	     (equal (INST-commit? (LRM-in-ROB idx MT) MA) 0))
  :hints (("Goal" :in-theory
		  (e/d (INST-commit? lift-b-ops
		        INST-excpt? equal-b1p-converter
			COMMIT-INST?
			ROB-write-reg?)
		       (uniq-inst-of-tag-if-commit-inst
			COMPLETE-INST-OF-TAG-IF-COMMIT-INST
			NOT-EXECUTE-STG-P-INST-AT-ROB-HEAD-IF-COMMIT-INST))))))

; When register modifier commits, ROB-write-reg? must be turned on.
; Note: The rule is written in the form of contrapositive. 
(defthm not-INST-commit-LRM-in-ROB
    (implies (and (inv MT MA)
		  (not (b1p (ROB-write-reg? (MA-ROB MA))))
		  (not (b1p (MT-specultv-at-dispatch? (MT-STEP MT MA SIGS))))
		  (not (b1p (MT-modified-at-dispatch? (MT-STEP MT MA SIGS))))
		  (not (MT-CMI-p (MT-step MT MA SIGS)))
		  (not (b1p (flush-all? MA SIGS)))
		  (exist-LRM-in-ROB-p idx MT)
		  (MAETT-p MT) (MA-state-p MA) (rname-p idx))
	     (equal (INST-commit? (LRM-in-ROB idx MT) MA) 0))
  :hints (("Goal" :in-theory (enable equal-b1p-converter
				     flush-all? lift-b-ops)
		  :restrict ((MT-CMI-P-IF-MODIFIED-INST-COMMIT
			      ((i (LRM-in-ROB idx MT)))))
		  :cases ((b1p (INST-specultv?
				(LRM-in-ROB idx MT)))
			  (b1p (INST-modified?
				(LRM-in-ROB idx MT)))))
	  ("subgoal 3" :cases ((b1p (INST-excpt?
				     (LRM-in-ROB idx MT)))))
	  ("subgoal 3.1" :cases
		 ((complete-stg-p (INST-stg (LRM-IN-ROB IDX MT)))))))
)

(encapsulate nil
(local
 (defthm ROBE-dest-INST-dest-reg-special
    (implies (and (inv MT MA)
		  (equal (MT-ROB-head MT) (INST-tag i))
		  (INST-writeback-p i)
		  (complete-stg-p (INST-stg i))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (INST-specultv? i)))
		  (not (INST-fetch-error-detected-p i))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)) 
	     (equal (robe-dest (nth-robe (MT-ROB-head MT) (MA-rob MA)))
		    (INST-dest-reg i)))))

(local
(defthm not-INST-commit-LRM-in-ROB-if-rob-write-rid-differs-local
    (implies (and (inv MT MA)
		  (not (equal (rob-write-rid (MA-ROB MA)) idx))
		  (exist-LRM-in-ROB-p idx MT)
		  (not (b1p (INST-specultv? (LRM-in-ROB idx MT))))
		  (not (b1p (INST-modified? (LRM-in-ROB idx MT))))
		  (not (b1p (INST-excpt? (LRM-in-ROB idx MT))))
		  (MAETT-p MT) (MA-state-p MA) (rname-p idx))
	     (equal (INST-commit? (LRM-in-ROB idx MT) MA) 0))
  :hints (("Goal" :in-theory (enable rob-write-rid INST-commit? lift-b-ops
				     equal-b1p-converter INST-excpt?)))))

; If the last modifier of register idx in the ROB is committing,
; signal rob-write-rid from the ROB designates the modified register
; idx.
(defthm not-INST-commit-LRM-in-ROB-if-rob-write-rid-differs
    (implies (and (inv MT MA)
		  (not (equal (rob-write-rid (MA-ROB MA)) idx))
		  (exist-LRM-in-ROB-p idx MT)
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (MT-specultv-at-dispatch?
			     (MT-step MT MA sigs))))
		  (not (b1p (MT-modified-at-dispatch?
			     (MT-step MT MA sigs))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (rname-p idx))
	     (equal (INST-commit? (LRM-in-ROB idx MT) MA) 0))
  :hints (("Goal" :in-theory (enable equal-b1p-converter
				     flush-all? lift-b-ops)
		  :restrict ((MT-CMI-P-IF-MODIFIED-INST-COMMIT
			      ((i (LRM-in-ROB idx MT)))))
		  :cases ((b1p (INST-specultv?
				(LRM-in-ROB idx MT)))
			  (b1p (INST-modified?
				(LRM-in-ROB idx MT)))))
	  ("subgoal 3" :cases ((b1p (INST-excpt?
				     (LRM-in-ROB idx MT)))))
	  ("subgoal 3.1" :cases
		 ((complete-stg-p (INST-stg (LRM-IN-ROB IDX MT)))))))
)
		   
(encapsulate nil
(local
(defthm LRM-in-ROB-MT-step-if-inst-commit-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (trace-exist-LRM-in-ROB-p idx trace)
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (inst-commit?
			     (trace-LRM-in-ROB idx trace)
			     MA)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (trace-exist-LRM-in-ROB-p idx
			(step-trace trace MT MA sigs ISA spc smc))))) 

; If the last register modifier in the ROB does not commit, the ROB
; will continue to hold the register modifier. 
(defthm LRM-in-ROB-MT-step-if-inst-commit
    (implies (and (inv MT MA)
		  (exist-LRM-in-ROB-p idx MT)
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (inst-commit? (LRM-in-ROB idx MT) MA)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (exist-LRM-in-ROB-p idx (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable exist-LRM-in-ROB-p
				     LRM-in-ROB))))
)

(encapsulate nil
(local
(defthm LRM-in-ROB-if-dispatch-inst-help
    (implies (and (inv MT MA)
		  (b1p (dispatch-inst? MA))
		  (b1p (cntlv-wb? (dispatch-cntlv MA)))
		  (not (b1p (cntlv-wb-sreg? (dispatch-cntlv MA))))
		  (not (b1p (INST-specultv? (INST-at-stg '(DQ 0) MT))))
		  (not (b1p (INST-modified? (INST-at-stg '(DQ 0) MT))))
		  (not (INST-fetch-error-detected-p (INST-at-stg '(DQ 0) MT)))
		  (MAETT-p MT) (MA-state-p MA))
	     (reg-modifier-p (dispatch-dest-reg MA)
			     (INST-at-stg '(DQ 0) MT)))
  :hints (("Goal" :in-theory (enable reg-modifier-p DQ-OUT-DEST-REG
				     dispatch-cntlv INST-WB? INST-wb-sreg?
				     INST-dest-reg INST-cntlv INST-opcode
				     lift-b-ops decode rdb logbit*
				     dispatch-dest-reg)))))

; If the dispatched instruction is a write-back instruction,
; then the dispatched instruction is a modifier of the register
; that is designated by signal dispatch-dest-reg from the dispatch logic.
(defthm LRM-in-ROB-if-dispatch-inst
    (implies (and (inv MT MA)
		  (b1p (dispatch-inst? MA))
		  (b1p (cntlv-wb? (dispatch-cntlv MA)))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (cntlv-wb-sreg? (dispatch-cntlv MA))))
		  (not (b1p (MT-specultv-at-dispatch?
			     (MT-step MT MA sigs))))
		  (not (b1p (MT-modified-at-dispatch?
			     (MT-step MT MA sigs))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (reg-modifier-p (dispatch-dest-reg MA)
			     (INST-at-stg '(DQ 0) MT))))
)

(encapsulate nil
(local
(defthm LRM-in-ROB-MT-step-if-dispatch-induct
    (implies (and (inv MT MA) 
		  (subtrace-p trace MT) (INST-listp trace) 
		  (member-equal i trace) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-inst? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (reg-modifier-p idx i)
		  (MAETT-p MT) (MA-state-p MA))
	     (trace-exist-LRM-in-ROB-p idx
			(step-trace trace MT MA sigs ISA spc smc)))))

(local
(defthm LRM-in-ROB-MT-step-if-dispatch-help
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-inst? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (reg-modifier-p idx i)
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LRM-in-ROB-p idx (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable exist-LRM-in-ROB-p INST-in)))))

; If the dispatched instruction is a register modifier, then
; the ROB contains a register modifier in the next clock cycle. 
(defthm LRM-in-ROB-MT-step-if-dispatch
    (implies (and (inv MT MA)
		  (b1p (dispatch-inst? MA))
		  (not (b1p (flush-all? MA sigs)))
		  (reg-modifier-p idx (INST-at-stg '(DQ 0) MT))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LRM-in-ROB-p idx (MT-step MT MA sigs)))
  :hints (("Goal" :restrict ((LRM-in-ROB-MT-step-if-dispatch-help
			      ((i (INST-at-stg '(DQ 0) MT))))))))
)
			
; A landmark lemma.
; Following two lemmas imply that the wait? bit of register reference table
; in the next cycle is correct.  Register reference table contains
; 0 for wait? bit, then there is no register modifier in the ROB. 
; Conversely, if wait? bit is 1, there is a register modifier.
(defthm not-LRM-in-ROB-MT-step-if-not-reg-ref-wait
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rname-p idx)
		  (not (b1p (MT-specultv-at-dispatch?
			     (MT-step MT MA sigs))))
		  (not (b1p (MT-modified-at-dispatch?
			     (MT-step MT MA sigs))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (not (b1p (reg-ref-wait?
			     (reg-tbl-nth idx
					  (DQ-reg-tbl (step-DQ MA sigs)))))))
	     (not (exist-LRM-in-ROB-p idx (MT-step MT MA sigs))))
  :hints (("Goal" :in-theory (enable STEP-REG-REF lift-b-ops)
		  :cases ((b1p (flush-all? MA sigs))))
	  (use-hint-always (:cases ((b1p (dispatch-inst? MA)))))
	  (use-hint-always
	   (:cases ((b1p (reg-ref-wait?
			  (reg-tbl-nth (rob-write-rid (MA-rob MA))
				       (DQ-reg-tbl (MA-DQ MA))))))))))

; A landmark lemma. See the comment above.
(defthm LRM-in-ROB-MT-step-if-reg-ref-wait
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rname-p idx)
		  (not (b1p (MT-specultv-at-dispatch?
			     (MT-step MT MA sigs))))
		  (not (b1p (MT-modified-at-dispatch?
			     (MT-step MT MA sigs))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (b1p (reg-ref-wait?
			(reg-tbl-nth idx
				     (DQ-reg-tbl (step-DQ MA sigs))))))
	     (exist-LRM-in-ROB-p idx (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable STEP-REG-REF lift-b-ops))))

(encapsulate nil
(local
(defthm trace-LRM-in-ROB-step-trace-if-dispatch-inst
    (implies (and (inv MT MA)
		  (member-equal i trace) (INST-p i)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-inst? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (reg-modifier-p idx i)
		  (MAETT-p MT) (MA-state-p MA))
	     (trace-exist-LRM-in-ROB-p idx
			  (step-trace trace MT MA sigs ISA spc smc)))))

(local
(defthm LRM-in-ROB-MT-step-if-dispatch-inst-induct
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (reg-modifier-p idx i)
		  (member-equal i trace) (INST-p i) 
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-inst? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (trace-LRM-in-ROB idx
			 (step-trace trace MT MA sigs ISA spc smc)) 
		    (step-INST i MT MA sigs)))
  :hints (("goal" :restrict
		  ((NOT-TRACE-LRM-IN-ROB-STEP-TRACE
		    ((i (car trace)))))))))

(local
(defthm LRM-in-ROB-MT-step-if-dispatch-inst-help
    (implies (and (inv MT MA)
		  (reg-modifier-p idx i)
		  (INST-in i MT) (INST-p i) 
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-inst? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (LRM-in-ROB idx (MT-step MT MA sigs))
		    (step-INST i MT MA sigs)))
  :hints (("Goal" :in-theory (enable LRM-in-ROB INST-in)))))

; If instruction i at DQ0 is a register modifier of register idx, and
; it is dispatched in this cycle, i is the last register modifier in
; the ROB in the next cycle.
(defthm LRM-in-ROB-MT-step-if-dispatch-inst
    (implies (and (inv MT MA)
		  (b1p (dispatch-inst? MA))
		  (not (b1p (flush-all? MA sigs)))
		  (reg-modifier-p idx (INST-at-stg '(DQ 0) MT))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (LRM-in-ROB idx (MT-step MT MA sigs))
		    (step-INST (INST-at-stg '(DQ 0) MT) MT MA sigs)))
  :hints (("Goal" :restrict
		  ((LRM-in-ROB-MT-step-if-dispatch-inst-help
		    ((i (INST-at-stg '(DQ 0) MT))))))))
)

(local
(defthm trace-LRM-in-ROB-step-trace-if-not-INST-commit
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (trace-exist-LRM-in-ROB-p idx trace)
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (INST-commit?
			     (trace-LRM-in-ROB idx trace) MA)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (trace-exist-LRM-in-ROB-p idx
		(step-trace trace MT MA sigs ISA spc smc)))))

(encapsulate nil
(local
(defthm LRM-in-ROB-MT-step-if-not-dispatch-inst-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (not (b1p (dispatch-inst? MA)))
		  (not (b1p (flush-all? MA sigs)))
		  (trace-exist-LRM-in-ROB-p idx trace)
		  (not (b1p (INST-commit?
			     (trace-LRM-in-ROB idx trace) MA)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rname-p idx))
	     (equal (trace-LRM-in-ROB idx
			    (step-trace trace MT MA sigs ISA spc smc)) 
		    (step-INST (trace-LRM-in-ROB idx trace)
			       MT MA sigs)))))

; help lemma to prove LRM-in-ROB-MT-step
(defthm LRM-in-ROB-MT-step-if-not-dispatch-inst
    (implies (and (inv MT MA)
		  (not (b1p (dispatch-inst? MA)))
		  (not (b1p (flush-all? MA sigs)))
		  (exist-LRM-in-ROB-p idx MT)
		  (not (b1p (INST-commit? (LRM-in-ROB idx MT) MA)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rname-p idx))
	     (equal (LRM-in-ROB idx (MT-step MT MA sigs))
		    (step-INST (LRM-in-ROB idx MT) MT MA sigs)))
  :hints (("Goal" :in-theory (enable LRM-in-ROB
				     exist-LRM-in-ROB-p))))

)

(encapsulate nil
(local
(defthm LRM-in-ROB-MT-step-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (not (b1p (flush-all? MA sigs)))
		  (not (reg-modifier-p idx
				       (INST-at-stg-in-trace '(DQ 0) trace)))
		  (trace-exist-LRM-in-ROB-p idx trace)
		  (not (b1p (INST-commit? (trace-LRM-in-ROB idx trace) MA)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rname-p idx))
	     (equal (trace-LRM-in-ROB idx
			(step-trace trace MT MA sigs ISA spc smc))
		    (step-INST (trace-LRM-in-ROB idx trace)
			       MT MA sigs)))))

; A landmark lemma.
; If the last register modifier in the ROB does not commit in this
; cycle, and the instruction at DQ0 is not a modifier, then the
; current last register modifier will continue to be the last register
; modifier in the next cycle.
(defthm LRM-in-ROB-MT-step
    (implies (and (inv MT MA)
		  (not (b1p (flush-all? MA sigs)))
		  (not (reg-modifier-p idx (INST-at-stg '(DQ 0) MT)))
		  (exist-LRM-in-ROB-p idx MT)
		  (not (b1p (INST-commit? (LRM-in-ROB idx MT) MA)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rname-p idx))
	     (equal (LRM-in-ROB idx (MT-step MT MA sigs))
		    (step-INST (LRM-in-ROB idx MT) MT MA sigs)))
  :hints (("Goal" :in-theory (enable LRM-in-ROB
				     INST-at-stg
				     exist-LRM-in-ROB-p))))
)

; Lemmas for the proof of INST-tag-LRM-MT-step
;
; The proof of INST-tag-LRM-MT-step is divided into three cases, where
; dispatch-inst? is false, where the instruction at DQ0 is not a
; register modifier, and where both conditions are false.  In either
; case, the new value of robe field of the register reference table is
; the correct Tomasulo's tag for the last register modifier in the
; ROB.
(defthm INST-tag-LRM-MT-step-if-not-dispatch-inst
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rname-p idx)
		  (not (b1p (dispatch-inst? MA)))
		  (not (b1p (MT-specultv-at-dispatch? (MT-step MT MA sigs))))
		  (not (b1p (MT-modified-at-dispatch? (MT-step MT MA sigs))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (b1p (reg-ref-wait?
			(step-reg-ref (reg-tbl-nth idx (DQ-reg-tbl (MA-DQ MA)))
				      idx MA sigs))))
	     (equal (INST-tag (LRM-in-ROB
				idx (MT-step MT MA sigs)))
		    (reg-ref-tag (step-reg-ref
				   (reg-tbl-nth idx (DQ-reg-tbl (MA-DQ MA)))
				   idx MA sigs))))
  :hints (("Goal" :in-theory (enable step-reg-ref lift-b-ops))))

(defthm INST-tag-LRM-MT-step-if-not-reg-modifier
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rname-p idx)
		  (not (reg-modifier-p idx (INST-at-stg '(DQ 0) MT)))
		  (not (b1p (MT-specultv-at-dispatch? (MT-step MT MA sigs))))
		  (not (b1p (MT-modified-at-dispatch? (MT-step MT MA sigs))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (b1p (reg-ref-wait?
			(step-reg-ref (reg-tbl-nth idx (DQ-reg-tbl (MA-DQ MA)))
				      idx MA sigs))))
	     (equal (INST-tag (LRM-in-ROB
				idx (MT-step MT MA sigs)))
		    (reg-ref-tag (step-reg-ref
				   (reg-tbl-nth idx (DQ-reg-tbl (MA-DQ MA)))
				   idx MA sigs))))
    :hints (("Goal" :in-theory (enable step-reg-ref lift-b-ops))))

(defthm INST-tag-LRM-MT-step-if-dispatch-inst
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rname-p idx)
		  (b1p (dispatch-inst? MA))
		  (reg-modifier-p idx (INST-at-stg '(DQ 0) MT))
		  (not (b1p (MT-specultv-at-dispatch? (MT-step MT MA sigs))))
		  (not (b1p (MT-modified-at-dispatch? (MT-step MT MA sigs))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (b1p (reg-ref-wait?
			(step-reg-ref (reg-tbl-nth idx (DQ-reg-tbl (MA-DQ MA)))
				      idx MA sigs))))
	     (equal (reg-ref-tag (step-reg-ref
				   (reg-tbl-nth idx (DQ-reg-tbl (MA-DQ MA)))
				   idx MA sigs))
		    (INST-tag (LRM-in-ROB
				idx (MT-step MT MA sigs)))))
  :hints (("Goal" :in-theory (enable step-reg-ref lift-b-ops))))
		  
; Combining the three lemmas above, we conclude that the
; Tomasulo's tag for the last register modifier in the ROB is
; in the register reference table in the next cycle. 
(defthm INST-tag-LRM-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rname-p idx)
		  (not (b1p (MT-specultv-at-dispatch? (MT-step MT MA sigs))))
		  (not (b1p (MT-modified-at-dispatch? (MT-step MT MA sigs))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (b1p (reg-ref-wait?
			(step-reg-ref (reg-tbl-nth idx (DQ-reg-tbl (MA-DQ MA)))
				      idx MA sigs))))
	     (equal (INST-tag (LRM-in-ROB idx (MT-step MT MA sigs)))
		    (reg-ref-tag (step-reg-ref
				  (reg-tbl-nth idx (DQ-reg-tbl (MA-DQ MA)))
				  idx MA sigs))))
  :hints (("Goal" :cases ((not (b1p (dispatch-inst? MA)))
			  (not (reg-modifier-p idx
					       (INST-at-stg '(DQ 0) MT)))))))

; Consistent-reg-ref-p is an invariant for register idx.
(defthm consistent-reg-ref-p-MT-step
    (implies (and (inv MT MA)
		  (rname-p idx)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (MT-CMI-p (MT-step MT MA sigs))))
	     (consistent-reg-ref-p idx (MT-step MT MA sigs)
				   (MA-step MA sigs)))
  :hints (("Goal" :in-theory (enable consistent-reg-ref-p))))

(encapsulate nil
(local
(defthm consistent-reg-tbl-p-preserved-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (integerp idx) (<= 0 idx) (<= idx *num-regs*)
		  (not (MT-CMI-p (MT-step MT MA sigs))))
	     (consistent-reg-tbl-under idx (MT-step MT MA sigs)
				       (MA-step MA sigs)))
  :hints (("Goal" :in-theory (enable consistent-reg-tbl-p rname-p
				     unsigned-byte-p)))))

; Consistent-reg-tbl-p is an invariant. 
(defthm consistent-reg-tbl-p-preserved
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (MT-CMI-p (MT-step MT MA sigs))))
	     (consistent-reg-tbl-p (MT-step MT MA sigs)
				   (MA-step MA sigs)))
  :hints (("Goal" :in-theory (enable consistent-reg-tbl-p))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;	     
; Proof of consistent-sreg-tbl-p-preserved
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Proof of consistent-sreg-tbl-p for initial states
(defthm consistent-sreg-tbl-p-init-MT
    (implies (and (MA-state-p MA) (b1p (MA-flushed? MA)))
	     (consistent-sreg-tbl-p (init-MT MA) MA))
  :hints (("goal" :in-theory (enable consistent-sreg-tbl-p
				     consistent-sreg-ref-p init-MT
				     MA-flushed? lift-b-ops DQ-empty?
				     SREG-TBL-EMPTY?
				     exist-LSRM-in-ROB-p))))

;;; Invariant proof
; This is a lemma to open up the definition of step-DQ.
(defthm sreg-tbl-nth-step-DQ
    (implies (and (MA-state-p MA) (srname-p idx))
	     (equal (sreg-tbl-nth idx (DQ-sreg-tbl (step-DQ MA sigs)))
		    (step-sreg-ref (sreg-tbl-nth idx (DQ-sreg-tbl (MA-DQ MA)))
				   idx MA sigs)))
  :hints (("goal" :in-theory (enable step-DQ step-sreg-tbl unsigned-byte-p
				     srname-p sreg-tbl-nth))))

;;;; Proof of not-LSRM-in-ROB-MT-step-if-not-reg-ref-wait
(encapsulate nil
(local
(defthm dispatched-p-LSRM-in-ROB-help
    (implies (trace-exist-LSRM-in-ROB-p idx trace)
	     (dispatched-p (trace-LSRM-in-ROB idx trace)))))

; The (special) register modifier in the ROB is dispatched.
(defthm dispatched-p-LSRM-in-ROB
    (implies (exist-LSRM-in-ROB-p idx MT)
	     (dispatched-p (LSRM-in-ROB idx MT)))
  :hints (("goal" :in-theory (enable exist-LSRM-in-ROB-p
				     LSRM-in-ROB))))
)

(encapsulate nil
(defthm not-committed-p-LSRM-in-ROB-help
    (implies (trace-exist-LSRM-in-ROB-p idx trace)
	     (not (committed-p (trace-LSRM-in-ROB idx trace)))))

; The (special) register modifier in the ROB is not committed.
(defthm not-committed-p-LSRM-in-ROB
    (implies (exist-LSRM-in-ROB-p idx MT)
	     (not (committed-p (LSRM-in-ROB idx MT))))
  :hints (("Goal" :in-theory (enable exist-LSRM-in-ROB-p
				     LSRM-in-ROB))))
)

; The instruction at the head of the ROB commits when ROB-write-sreg?
; is 1.
(defthm INST-commit-LSRM-in-ROB
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (b1p (ROB-write-sreg? (MA-ROB MA)))
		  (dispatched-p i)
		  (not (committed-p i))
		  (equal (MT-ROB-head MT) (INST-tag i))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-commit? i MA) 1))
  :Hints (("Goal" :in-theory (enable ROB-write-sreg? INST-commit?
				     commit-inst?
				     INST-commit? equal-b1p-converter
				     committed-p dispatched-p
				     lift-b-ops))))

; If the dispatched instruction is a special register modifier,
; dispatch-dest-reg designates the modified special register. 
(defthm not-sreg-modifier-if-not-dispatch-dest-reg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (b1p (dispatch-inst? MA))
		  (not (b1p (INST-specultv? (INST-at-stg '(DQ 0) MT))))
		  (not (b1p (INST-modified? (INST-at-stg '(DQ 0) MT))))
		  (not (INST-fetch-error-detected-p (INST-at-stg '(DQ 0) MT)))
		  (not (equal idx (dispatch-dest-reg MA))))
	     (not (sreg-modifier-p idx (INST-at-stg '(DQ 0) MT))))
  :hints (("Goal" :in-theory (e/d (sreg-modifier-p dispatch-dest-reg
				     DQ-out-dest-reg
				     dispatch-inst?
				     INST-DEST-REG
				     INST-CNTLV
				     INST-OPCODE
				     DECODE rdb logbit*
				     INST-wb? 
				     lift-b-ops)
				  (DE-VALID-CONSISTENT)))))

;  If the dispatched instruction is a special register modifier,
; the wb? and wb-sreg? fields of the dispatch-cntlv signal
; are 1.
(defthm not-sreg-modifier-if-not-cntlv-wb
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (b1p (dispatch-inst? MA))
		  (not (b1p (INST-specultv? (INST-at-stg '(DQ 0) MT))))
		  (not (b1p (INST-modified? (INST-at-stg '(DQ 0) MT))))
		  (not (INST-fetch-error-detected-p (INST-at-stg '(DQ 0) MT)))
		  (or (not (b1p (cntlv-wb? (dispatch-cntlv MA))))
		      (not (b1p (cntlv-wb-sreg? (dispatch-cntlv MA))))))
	     (not (sreg-modifier-p idx (INST-at-stg '(DQ 0) MT))))
  :hints (("Goal" :in-theory (enable dispatch-cntlv sreg-modifier-p
				     dispatch-inst? DISPATCH-NO-UNIT?
				     dispatch-to-IU? dispatch-to-MU?
				     dispatch-to-BU? dispatch-to-LSU?
				     DQ-READY-NO-UNIT? DQ-READY-TO-BU?
				     DQ-READY-TO-IU? DQ-READY-TO-LSU?
				     DQ-READY-TO-MU?
				     INST-WB-SREG? INST-WB?
				     lift-b-ops))))

(encapsulate nil
(local
(defthm not-LSRM-in-ROB-MT-step-if-flush-all-help
    (implies (and (inv MT MA)
		  (MT-all-commit-before-trace trace MT)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (flush-all? MA sigs)))
	     (not (trace-exist-LSRM-in-ROB-p idx
					     (step-trace trace MT MA sigs
							 ISA spc smc))))
  :hints (("goal" :in-theory (enable committed-p))
	  (when-found (MT-ALL-COMMIT-BEFORE-TRACE (CDR TRACE) MT)
		      (:cases ((committed-p (car trace))))))))

; No register modifier will be in the MAETT after a flush-all.
(defthm not-LSRM-in-ROB-MT-step-if-flush-all
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (flush-all? MA sigs)))
	     (not (exist-LSRM-in-ROB-p idx (MT-step MT MA sigs))))
  :hints (("Goal" :in-theory (enable exist-LSRM-in-ROB-p))))
)

(encapsulate nil
(local
 (defthm local-help
     (implies (and (inv MT MA)
		   (INST-in i MT) (INST-p i)
		   (INST-in j MT) (INST-p j)
		   (INST-in-order-p i j MT)
		   (not (equal i j))
		   (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		   (DQ-stg-p (INST-stg i)) (DQ-stg-p (INST-stg j)))
	      (DQ-stg-p (INST-stg (step-INST j MT MA sigs))))
 :hints (("Goal" :in-theory (enable DQ-stg-p step-inst-dq-inst
				    step-inst-low-level-functions)
		 :use ((:instance uniq-stage-inst)
		       (:instance DQ-stg-index-monotonic))))))

(local
 (defthm not-dispatched-inst-step-inst-if-earlier-non-dispatched
     (implies (and (inv MT MA)
		   (INST-in i MT) (INST-p i)
		   (INST-in j MT) (INST-p j)
		   (INST-in-order-p i j MT)
		   (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		   (not (dispatched-p i)))
	      (not (dispatched-p (step-inst j MT MA sigs))))
   :hints (("Goal" :in-theory (e/d (dispatched-p* IFU-IS-LAST-INST)
				   (inst-is-at-one-of-the-stages))
		   :restrict ((local-help ((i i))))
		   :use (:instance inst-is-at-one-of-the-stages
			 (i j)))
	   (when-found (DQ-stg-p (INST-stg j))
		       (:cases ((equal i j)))))))
		  
; A help lemma
(defthm not-trace-LSRM-in-ROB-step-trace
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (INST-in i MT) (INST-p i)
		  (not (dispatched-p i))
		  (subtrace-after-p i trace MT)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (not (trace-exist-LSRM-in-ROB-p idx
			(step-trace trace MT MA sigs ISA spc smc)))))
)

(local
(defthm not-trace-LSRM-in-ROB-MT-step-if-no-dispatch
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (srname-p idx)
		  (not (trace-exist-LSRM-in-ROB-p idx trace))
		  (not (b1p (dispatch-inst? MA))))
	     (not (trace-exist-LSRM-in-ROB-p idx
		       (step-trace trace MT MA sigs ISA spc smc))))))

(local
(defthm not-trace-LSRM-in-ROB-MT-step-if-not-sreg-modifier
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (srname-p idx)
		  (not (trace-exist-LSRM-in-ROB-p idx trace))
		  (not (sreg-modifier-p idx (INST-at-stg-in-trace '(DQ 0)
								  trace))))
	     (not (trace-exist-LSRM-in-ROB-p idx
			 (step-trace trace MT MA sigs ISA spc smc))))
  :hints (("Goal" :in-theory (enable dispatched-p)
		  :restrict ((not-trace-LSRM-in-ROB-step-trace
			      ((i (car trace)))))))))

; If there is no special register modifier in the ROB in the current cycle,
; and the (possibly) dispatched instruction is not a modifier, then
; there will be no modifier in the ROB in the next cycle.
(defthm not-LSRM-in-ROB-MT-step-if-not-sreg-modifier
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (srname-p idx)
		  (not (exist-LSRM-in-ROB-p idx MT))
		  (not (sreg-modifier-p idx (INST-at-stg '(DQ 0) MT))))
	     (not (exist-LSRM-in-ROB-p idx (MT-step MT MA sigs))))
  :hints (("Goal" :in-theory (enable exist-LSRM-in-ROB-p
				     INST-at-stg))))

(local
(encapsulate nil
(local
 (defthm committed-p-step-inst-if-following-inst-commit
     (implies (and (inv MT MA)
		   (b1p (INST-commit? i MA))
		   (INST-in i MT) (INST-p i)
		   (INST-in j MT) (INST-p j) 
		   (INST-in-order-p j i MT)
		   (MAETT-p MT) (MA-state-p MA))
	      (committed-p (step-INST j MT MA sigs)))
   :hints (("Goal" :in-theory (enable INST-commit? lift-b-ops)
		   :use (:instance UNCOMMITTED-INST-P-IS-AFTER-MT-ROB-HEAD
				   (i j))))))

; A local help lemma.
(defthm commit-inst-step-inst-car-if-LSRM-commit
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (subtrace-p trace MT) (INST-listp trace)
		  (subtrace-after-p i trace MT)
		  (trace-exist-LSRM-in-ROB-p idx trace)
		  (b1p (INST-commit?
			(trace-LSRM-in-ROB idx trace) MA))
		  (MAETT-p MT) (MA-state-p MA))
	     (committed-p (step-inst i MT MA sigs))))
))

(encapsulate nil		      
(local
(defthm LSRM-in-ROB-MT-step-if-inst-commit-LSRM-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (srname-p idx)
		  (not (b1p (dispatch-inst? MA)))
		  (trace-exist-LSRM-in-ROB-p idx trace)
		  (b1p (inst-commit?
			(trace-LSRM-in-ROB idx trace) MA))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (not (trace-exist-LSRM-in-ROB-p idx
			(step-trace trace MT MA sigs ISA spc smc))))
  :hints (("Goal" :restrict
		  ((commit-inst-step-inst-car-if-LSRM-commit
		    ((trace (cdr trace)))))))))

; If the last special register modifier commits in this cycle, and no
; instruction is dispatched, then there will be no modifier in the ROB
; next cycle.
(defthm LSRM-in-ROB-MT-step-if-inst-commit-LSRM
    (implies (and (inv MT MA)
		  (not (b1p (dispatch-inst? MA)))
		  (exist-LSRM-in-ROB-p idx MT)
		  (b1p (inst-commit? (LSRM-in-ROB idx MT) MA))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (srname-p idx))
	     (not (exist-LSRM-in-ROB-p idx (MT-step MT MA sigs))))
  :hints (("Goal" :in-theory (enable exist-LSRM-in-ROB-p
				     LSRM-in-ROB))))
)

(encapsulate nil
(local
(defthm LSRM-in-ROB-MT-step-if-inst-commit-LSRM-2-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (not (sreg-modifier-p idx
					(inst-at-stg-in-trace '(DQ 0) trace)))
		  (trace-exist-LSRM-in-ROB-p idx trace)
		  (b1p (inst-commit?
			(trace-LSRM-in-ROB idx trace) MA))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (srname-p idx))
	     (not (trace-exist-LSRM-in-ROB-p idx
		       (step-trace trace MT MA sigs ISA spc smc))))
  :hints (("Goal" :restrict
		  ((commit-inst-step-inst-car-if-LSRM-commit
		    ((trace (cdr trace)))))))))

; If the last special register modifier commits in this cycle,
; and the dispatched instruction is not a modifier, then
; there will be no register modifier in the ROB next cycle.
(defthm LSRM-in-ROB-MT-step-if-inst-commit-LSRM-2
    (implies (and (inv MT MA)
		  (not (sreg-modifier-p idx (inst-at-stg '(DQ 0) MT)))
		  (exist-LSRM-in-ROB-p idx MT)
		  (b1p (inst-commit? (LSRM-in-ROB idx MT) MA))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (srname-p idx))
	     (not (exist-LSRM-in-ROB-p idx (MT-step MT MA sigs))))
  :hints (("Goal" :in-theory (enable exist-LSRM-in-ROB-p
				     LSRM-in-ROB
				     INST-at-stg))))
)

; If there is no sreg modifier in rob, and if no instruction
; is dispatched, there won't be any sreg-modifier in ROB.
(defthm not-LSRM-in-ROB-MT-step-if-no-dispatch
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (srname-p idx)
		  (not (exist-LSRM-in-ROB-p idx MT))
		  (not (b1p (dispatch-inst? MA))))
	     (not (exist-LSRM-in-ROB-p idx (MT-step MT MA sigs))))
  :hints (("Goal" :in-theory (enable exist-LSRM-in-ROB-p MT-step))))

; The destination special register should be 0 or 1, otherwise an
; illegal instruction is raised. 
(defthm INST-dest-reg-if-INST-wb-sreg
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (not (b1p (INST-decode-error? i)))
		  (b1p (INST-wb-sreg? i))
		  (MAETT-p MT) (MA-state-p MA))
	     (< (INST-dest-reg i) 2))
  :hints (("Goal" :in-theory (enable INST-decode-error? lift-b-ops
				     DECODE-ILLEGAL-INST?
				     INST-WB-SREG? decode rdb logbit*
				     INST-CNTLV INST-opcode
				     INST-DEST-REG INST-rc))))

; Signal ROB-write-rid designates the existing special register
; when a special register is written into.
(defthm srname-p-rob-write-rid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (INST-modified?
			     (inst-of-tag (MT-rob-head MT) MT))))
		  (not (b1p (INST-specultv?
			     (inst-of-tag (MT-rob-head MT) MT))))
		  (not (INST-fetch-error-detected-p 
			(inst-of-tag (MT-rob-head MT) MT)))
		  (b1p (ROB-write-sreg? (MA-rob MA))))
	     (srname-p (ROB-write-rid (MA-ROB MA))))
  :hints (("goal" :in-theory (enable ROB-write-sreg? srname-p ROB-write-rid
				     lift-b-ops exception-relations
				     INST-EXCPT-DETECTED-P)
		  :cases ((b1p (INST-fetch-error?
				(inst-of-tag (MT-rob-head MT) MT)))
			  (not (b1p (INST-decode-error?
				     (inst-of-tag (MT-rob-head MT) MT))))))))

; A landmark lemma
; If the wait? bit of the special register reference table is
; 0, there will not be any special register modifier in the ROB.
(defthm not-LSRM-in-ROB-MT-step-if-not-reg-ref-wait
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (srname-p idx)
		  (not (b1p (MT-specultv-at-dispatch?
			     (MT-step MT MA sigs))))
		  (not (b1p (MT-modified-at-dispatch?
			     (MT-step MT MA sigs))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (not (b1p (reg-ref-wait?
			     (sreg-tbl-nth idx
					   (DQ-sreg-tbl (step-DQ MA sigs)))))))
	     (not (exist-LSRM-in-ROB-p idx (MT-step MT MA sigs))))
  :hints (("Goal" :in-theory (enable STEP-SREG-REF lift-b-ops
				     srname-p rname-p)
		  :cases ((b1p (flush-all? MA sigs))))
	  (use-hint-always (:cases ((b1p (dispatch-inst? MA)))))
	  (use-hint-always
	   (:cases ((b1p (reg-ref-wait?
			  (sreg-tbl-nth (rob-write-rid (MA-rob MA))
					(DQ-sreg-tbl (MA-DQ MA))))))))))

;;;; Proof of LSRM-in-ROB-MT-step-if-reg-ref-wait
(encapsulate nil
(local
(defthm LSRM-in-ROB-if-dispatch-inst-help
    (implies (and (inv MT MA)
		  (b1p (dispatch-inst? MA))
		  (b1p (cntlv-wb? (dispatch-cntlv MA)))
		  (b1p (cntlv-wb-sreg? (dispatch-cntlv MA)))
		  (not (b1p (INST-specultv? (INST-at-stg '(DQ 0) MT))))
		  (not (b1p (INST-modified? (INST-at-stg '(DQ 0) MT))))
		  (not (INST-fetch-error-detected-p (INST-at-stg '(DQ 0) MT)))
		  (MAETT-p MT) (MA-state-p MA))
	     (sreg-modifier-p (dispatch-dest-reg MA)
			      (INST-at-stg '(DQ 0) MT)))
  :hints (("Goal" :in-theory (enable sreg-modifier-p DQ-OUT-DEST-REG
				     dispatch-cntlv INST-WB? INST-wb-sreg?
				     INST-dest-reg INST-cntlv INST-opcode
				     lift-b-ops decode rdb logbit*
				     dispatch-dest-reg)))))

; The dispatched instruction is a special register modifier
; if the wb? and wb-sreg? field of the dispatch-cntlv are 1.
(defthm LSRM-in-ROB-if-dispatch-inst
    (implies (and (inv MT MA)
		  (b1p (dispatch-inst? MA))
		  (b1p (cntlv-wb? (dispatch-cntlv MA)))
		  (b1p (cntlv-wb-sreg? (dispatch-cntlv MA)))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (MT-specultv-at-dispatch? (MT-step MT MA sigs))))
		  (not (b1p (MT-modified-at-dispatch? (MT-step MT MA sigs))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (sreg-modifier-p (dispatch-dest-reg MA)
			      (INST-at-stg '(DQ 0) MT))))
)

; The last special register modifier does not commit in this cycle,
; if it is not at the head of the ROB. 
(defthm not-INST-commit-LSRM-in-ROB-if-not-ROB-head
    (implies (and (inv MT MA)
		  (not (equal (MT-ROB-head MT)
			      (INST-tag (LSRM-in-ROB idx MT))))
		  (exist-LSRM-in-ROB-p idx MT)
		  (MAETT-p MT) (MA-state-p MA) (srname-p idx))
	     (equal (INST-commit? (LSRM-in-ROB idx MT) MA) 0))
  :hints (("Goal" :in-theory (enable INST-commit? equal-b1p-converter
				     lift-b-ops))))

(encapsulate nil
(local
 (defthm ROBE-dest-INST-dest-reg-special
    (implies (and (inv MT MA)
		  (equal (MT-ROB-head MT) (INST-tag i))
		  (INST-writeback-p i)
		  (complete-stg-p (INST-stg i))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (INST-specultv? i)))
		  (not (INST-fetch-error-detected-p i))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)) 
	     (equal (robe-dest (nth-robe (MT-ROB-head MT) (MA-rob MA)))
		    (INST-dest-reg i)))))

(local
(defthm not-INST-commit-LSRM-in-ROB-local
    (implies (and (inv MT MA)
		  (not (equal (rob-write-rid (MA-ROB MA)) idx))
		  (exist-LSRM-in-ROB-p idx MT)
		  (not (b1p (INST-specultv? (LSRM-in-ROB idx MT))))
		  (not (b1p (INST-modified? (LSRM-in-ROB idx MT))))
		  (not (b1p (INST-excpt? (LSRM-in-ROB idx MT))))
		  (MAETT-p MT) (MA-state-p MA) (srname-p idx))
	     (equal (INST-commit? (LSRM-in-ROB idx MT) MA) 0))
  :hints (("Goal" :in-theory (enable rob-write-rid INST-commit? lift-b-ops
				     equal-b1p-converter INST-excpt?)))))

; The last special register modifier of register idx does not commit,
; when ROB-write-rid designates another register than idx.
(defthm not-INST-commit-LSRM-in-ROB-if-rob-write-rid-differs
    (implies (and (inv MT MA)
		  (not (equal (rob-write-rid (MA-ROB MA)) idx))
		  (exist-LSRM-in-ROB-p idx MT)
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (MT-specultv-at-dispatch? (MT-step MT MA sigs))))
		  (not (b1p (MT-modified-at-dispatch? (MT-step MT MA sigs))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (srname-p idx))
	     (equal (INST-commit? (LSRM-in-ROB idx MT) MA) 0))
  :hints (("Goal" :in-theory (enable equal-b1p-converter
				     flush-all? lift-b-ops)
		  :restrict ((MT-CMI-P-IF-MODIFIED-INST-COMMIT
			      ((i (LSRM-in-ROB idx MT)))))
		  :cases ((b1p (INST-specultv?
				(LSRM-in-ROB idx MT)))
			  (b1p (INST-modified?
				(LSRM-in-ROB idx MT)))))
	  ("subgoal 3" :cases ((b1p (INST-excpt?
				     (LSRM-in-ROB idx MT)))))
	  ("subgoal 3.1" :cases
		 ((complete-stg-p (INST-stg (LSRM-IN-ROB IDX MT)))))))
)

(encapsulate nil
(local
(defthm ROBE-WB-INST-WB-special
    (implies (and (inv MT MA)
		  (equal (MT-rob-head MT) (INST-tag i))
		  (INST-in i MT) (INST-p i)
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (INST-specultv? i)))
		  (dispatched-p i) (not (committed-p i))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (robe-wb? (nth-robe (MT-rob-head MT) (MA-rob MA)))
		    (INST-wb? i)))))

(local
(defthm ROBE-WB-INST-WB-SREG-special
    (implies (and (inv MT MA)
		  (equal (MT-rob-head MT) (INST-tag i))
		  (INST-in i MT) (INST-p i)
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (INST-specultv? i)))
		  (dispatched-p i) (not (committed-p i))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (robe-wb-sreg? (nth-robe (MT-rob-head MT) (MA-rob MA)))
		    (INST-wb-sreg? i)))))

(local
 (defthm ROBE-EXCPT-INST-EXCPT-FLAGS-special
    (implies (and (inv MT MA)
		  (equal (MT-ROB-head MT) (INST-tag i))
		  (complete-stg-p (INST-stg i))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (INST-specultv? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)) 
	     (equal (robe-excpt (nth-robe (MT-ROB-head MT) (MA-rob MA)))
		    (INST-excpt-flags i)))))

(local
(defthm not-INST-commit-LSRM-in-ROB-help
    (implies (and (inv MT MA)
		  (not (b1p (ROB-write-sreg? (MA-ROB MA))))
		  (not (b1p (INST-specultv? (LSRM-in-ROB idx MT))))
		  (not (b1p (INST-modified? (LSRM-in-ROB idx MT))))
		  (not (b1p (INST-excpt? (LSRM-in-ROB idx MT))))
		  (exist-LSRM-in-ROB-p idx MT)
		  (MAETT-p MT) (MA-state-p MA) (srname-p idx))
	     (equal (INST-commit? (LSRM-in-ROB idx MT) MA) 0))
  :hints (("Goal" :in-theory
		  (e/d (INST-commit? lift-b-ops
			INST-excpt? equal-b1p-converter
			COMMIT-INST? ROB-write-sreg?)
		       (uniq-inst-of-tag-if-commit-inst
			COMPLETE-INST-OF-TAG-IF-COMMIT-INST
			NOT-EXECUTE-STG-P-INST-AT-ROB-HEAD-IF-COMMIT-INST))))))

; If ROB-write-sreg is 0, a special register modifier does not commit.
(defthm not-INST-commit-LSRM-in-ROB
    (implies (and (inv MT MA)
		  (not (b1p (ROB-write-sreg? (MA-ROB MA))))
		  (NOT (B1P (MT-SPECULTV-AT-DISPATCH? (MT-STEP MT MA SIGS))))
		  (NOT (B1P (MT-MODIFIED-AT-DISPATCH? (MT-STEP MT MA SIGS))))
		  (NOT (MT-CMI-P (MT-STEP MT MA SIGS)))
		  (NOT (B1P (FLUSH-ALL? MA SIGS)))
		  (exist-LSRM-in-ROB-p idx MT)
		  (MAETT-p MT) (MA-state-p MA) (srname-p idx))
	     (equal (INST-commit? (LSRM-in-ROB idx MT) MA) 0))
  :hints (("Goal" :in-theory (enable equal-b1p-converter
				     flush-all? lift-b-ops)
		  :restrict ((MT-CMI-P-IF-MODIFIED-INST-COMMIT
			      ((i (LSRM-in-ROB idx MT)))))
		  :cases ((b1p (INST-specultv?
				(LSRM-in-ROB idx MT)))
			  (b1p (INST-modified?
				(LSRM-in-ROB idx MT)))))
	  ("subgoal 3" :cases ((b1p (INST-excpt?
				     (LSRM-in-ROB idx MT)))))
	  ("subgoal 3.1" :cases
		 ((complete-stg-p (INST-stg (LSRM-IN-ROB IDX MT)))))))
)

(encapsulate nil
(local
(defthm LSRM-in-ROB-MT-step-if-inst-commit-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (trace-exist-LSRM-in-ROB-p idx trace)
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (inst-commit?
			     (trace-LSRM-in-ROB idx trace)
			     MA)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (trace-exist-LSRM-in-ROB-p idx
			(step-trace trace MT MA sigs ISA spc smc))))) 

; If there are special register modifiers in the ROB, and no instruction
; commits in this cycle, then the ROB continues to have the modifiers
; in the next cycle.
(defthm LSRM-in-ROB-MT-step-if-inst-commit
    (implies (and (inv MT MA)
		  (exist-LSRM-in-ROB-p idx MT)
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (inst-commit? (LSRM-in-ROB idx MT) MA)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (exist-LSRM-in-ROB-p idx (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable exist-LSRM-in-ROB-p
				     LSRM-in-ROB))))
)

(encapsulate nil
(local
(defthm LRM-in-ROB-MT-step-if-dispatch-induct
    (implies (and (inv MT MA) 
		  (subtrace-p trace MT) (INST-listp trace) 
		  (member-equal i trace) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-inst? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (sreg-modifier-p idx i)
		  (MAETT-p MT) (MA-state-p MA))
	     (trace-exist-LSRM-in-ROB-p idx
			(step-trace trace MT MA sigs ISA spc smc)))))

(local
(defthm LRM-in-ROB-MT-step-if-dispatch-help
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-inst? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (sreg-modifier-p idx i)
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LSRM-in-ROB-p idx (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable exist-LSRM-in-ROB-p INST-in)))))

; If a special register modifier is dispatched, then there will
; be modifiers in the ROB.
(defthm LSRM-in-ROB-MT-step-if-dispatch
    (implies (and (inv MT MA)
		  (b1p (dispatch-inst? MA))
		  (not (b1p (flush-all? MA sigs)))
		  (sreg-modifier-p idx (INST-at-stg '(DQ 0) MT))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LSRM-in-ROB-p idx (MT-step MT MA sigs)))
  :hints (("Goal" :restrict ((LRM-in-ROB-MT-step-if-dispatch-help
			      ((i (INST-at-stg '(DQ 0) MT))))))))
)

;  A landmark lemma
;  There will be special register modifiers in the ROB in the next cycle
;  if the wait? bit of the special register reference table will be 1. 
(defthm LSRM-in-ROB-MT-step-if-reg-ref-wait
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (srname-p idx)
		  (not (b1p (MT-specultv-at-dispatch? (MT-step MT MA sigs))))
		  (not (b1p (MT-modified-at-dispatch? (MT-step MT MA sigs))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (b1p (reg-ref-wait?
			(sreg-tbl-nth idx
				      (DQ-sreg-tbl (step-DQ MA sigs))))))
	     (exist-LSRM-in-ROB-p idx (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable STEP-SREG-REF lift-b-ops srname-p
				     rname-p))))

;;;;;;; Proof of INST-tag-LSRM-MT-step
(encapsulate nil
(local
(defthm trace-LSRM-in-ROB-step-trace-if-dispatch-inst
    (implies (and (inv MT MA)
		  (member-equal i trace) (INST-p i)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-inst? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (sreg-modifier-p idx i)
		  (MAETT-p MT) (MA-state-p MA))
	     (trace-exist-LSRM-in-ROB-p idx
			  (step-trace trace MT MA sigs ISA spc smc)))))

(local
(defthm LSRM-in-ROB-MT-step-if-dispatch-inst-induct
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (sreg-modifier-p idx i)
		  (member-equal i trace) (INST-p i) 
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-inst? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (trace-LSRM-in-ROB idx
			 (step-trace trace MT MA sigs ISA spc smc)) 
		    (step-INST i MT MA sigs)))
  :hints (("goal" :restrict
		  ((NOT-TRACE-LSRM-IN-ROB-STEP-TRACE
		    ((i (car trace)))))))))

(local
(defthm LSRM-in-ROB-MT-step-if-dispatch-inst-help
    (implies (and (inv MT MA)
		  (sreg-modifier-p idx i)
		  (INST-in i MT) (INST-p i) 
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-inst? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (LSRM-in-ROB idx (MT-step MT MA sigs))
		    (step-INST i MT MA sigs)))
  :hints (("Goal" :in-theory (enable LSRM-in-ROB
				     INST-in)))))

; The dispatched instruction is the last special register modifier
; if the dispatched instruction is a modifier. 
(defthm LSRM-in-ROB-MT-step-if-dispatch-inst
    (implies (and (inv MT MA)
		  (b1p (dispatch-inst? MA))
		  (not (b1p (flush-all? MA sigs)))
		  (sreg-modifier-p idx (INST-at-stg '(DQ 0) MT))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (LSRM-in-ROB idx (MT-step MT MA sigs))
		    (step-INST (INST-at-stg '(DQ 0) MT) MT MA sigs)))
  :hints (("Goal" :restrict
		  ((LSRM-in-ROB-MT-step-if-dispatch-inst-help
		    ((i (INST-at-stg '(DQ 0) MT))))))))
)

(local
(defthm trace-LSRM-in-ROB-step-trace-if-not-INST-commit
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (trace-exist-LSRM-in-ROB-p idx trace)
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (INST-commit?
			     (trace-LSRM-in-ROB idx trace) MA)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (trace-exist-LSRM-in-ROB-p idx
		(step-trace trace MT MA sigs ISA spc smc)))))

(encapsulate nil
(local
(defthm LSRM-in-ROB-MT-step-if-not-dispatch-inst-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (not (b1p (dispatch-inst? MA)))
		  (not (b1p (flush-all? MA sigs)))
		  (trace-exist-LSRM-in-ROB-p idx trace)
		  (not (b1p (INST-commit?
			     (trace-LSRM-in-ROB idx trace) MA)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (srname-p idx))
	     (equal (trace-LSRM-in-ROB idx
			    (step-trace trace MT MA sigs ISA spc smc)) 
		    (step-INST (trace-LSRM-in-ROB idx trace)
			       MT MA sigs)))))

; The last special register modifier in the current cycle is also the
; last register modifier in the next cycle, if no instruction is
; dispatched during this cycle.
(defthm LSRM-in-ROB-MT-step-if-not-dispatch-inst
    (implies (and (inv MT MA)
		  (not (b1p (dispatch-inst? MA)))
		  (not (b1p (flush-all? MA sigs)))
		  (exist-LSRM-in-ROB-p idx MT)
		  (not (b1p (INST-commit? (LSRM-in-ROB idx MT) MA)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (srname-p idx))
	     (equal (LSRM-in-ROB idx (MT-step MT MA sigs))
		    (step-INST (LSRM-in-ROB idx MT) MT MA sigs)))
  :hints (("Goal" :in-theory (enable LSRM-in-ROB
				     exist-LSRM-in-ROB-p))))

)

(encapsulate nil
(local
(defthm LSRM-in-ROB-MT-step-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (not (b1p (flush-all? MA sigs)))
		  (not (sreg-modifier-p idx
					(INST-at-stg-in-trace '(DQ 0) trace)))
		  (trace-exist-LSRM-in-ROB-p idx trace)
		  (not (b1p (INST-commit?
			     (trace-LSRM-in-ROB idx trace) MA)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (srname-p idx))
	     (equal (trace-LSRM-in-ROB idx
			(step-trace trace MT MA sigs ISA spc smc))
		    (step-INST (trace-LSRM-in-ROB idx trace)
			       MT MA sigs)))))

; A landmark lemma
; The last special register modifier continues to be the last modifier,
; if the instruction at DQ0 is not a modifier. 
(defthm LSRM-in-ROB-MT-step
    (implies (and (inv MT MA)
		  (not (b1p (flush-all? MA sigs)))
		  (not (sreg-modifier-p idx (INST-at-stg '(DQ 0) MT)))
		  (exist-LSRM-in-ROB-p idx MT)
		  (not (b1p (INST-commit? (LSRM-in-ROB idx MT) MA)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (srname-p idx))
	     (equal (LSRM-in-ROB idx (MT-step MT MA sigs))
		    (step-INST (LSRM-in-ROB idx MT) MT MA sigs)))
  :hints (("Goal" :in-theory (enable LSRM-in-ROB
				     INST-at-stg
				     exist-LSRM-in-ROB-p))))
)

; The proof of INST-tag-LSRM-MT-step is divided into three
; cases, where dispatch-inst? is 0, where the instruction at DQ0 is not a
; register modifier, and where both conditions are 1.
(defthm INST-tag-LSRM-MT-step-if-not-dispatch-inst
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (srname-p idx)
		  (not (b1p (dispatch-inst? MA)))
		  (not (b1p (MT-specultv-at-dispatch? (MT-step MT MA sigs))))
		  (not (b1p (MT-modified-at-dispatch? (MT-step MT MA sigs))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (b1p (reg-ref-wait?
			(step-sreg-ref (sreg-tbl-nth idx
						     (DQ-sreg-tbl (MA-DQ MA)))
				       idx MA sigs))))
	     (equal (INST-tag (LSRM-in-ROB
			       idx (MT-step MT MA sigs)))
		    (reg-ref-tag (step-sreg-ref
				  (sreg-tbl-nth idx (DQ-sreg-tbl (MA-DQ MA)))
				  idx MA sigs))))
  :hints (("Goal" :in-theory (enable step-sreg-ref lift-b-ops
				     rname-p srname-p))))

(defthm INST-tag-LSRM-MT-step-if-not-sreg-modifier
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (srname-p idx)
		  (not (sreg-modifier-p idx (INST-at-stg '(DQ 0) MT)))
		  (not (b1p (MT-specultv-at-dispatch? (MT-step MT MA sigs))))
		  (not (b1p (MT-modified-at-dispatch? (MT-step MT MA sigs))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (b1p (reg-ref-wait?
			(step-sreg-ref (sreg-tbl-nth idx
						     (DQ-sreg-tbl (MA-DQ MA)))
				       idx MA sigs))))
	     (equal (INST-tag (LSRM-in-ROB
			       idx (MT-step MT MA sigs)))
		    (reg-ref-tag (step-sreg-ref
				  (sreg-tbl-nth idx (DQ-sreg-tbl (MA-DQ MA)))
				  idx MA sigs))))
  :hints (("Goal" :in-theory (enable step-sreg-ref lift-b-ops
				     srname-p))))

(defthm INST-tag-LSRM-MT-step-if-dispatch-inst
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (srname-p idx)
		  (b1p (dispatch-inst? MA))
		  (sreg-modifier-p idx (INST-at-stg '(DQ 0) MT))
		  (not (b1p (MT-specultv-at-dispatch? (MT-step MT MA sigs))))
		  (not (b1p (MT-modified-at-dispatch? (MT-step MT MA sigs))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (b1p (reg-ref-wait?
			(step-sreg-ref (sreg-tbl-nth idx
						     (DQ-sreg-tbl (MA-DQ MA)))
				       idx MA sigs))))
	     (equal (reg-ref-tag (step-sreg-ref
				  (sreg-tbl-nth idx (DQ-sreg-tbl (MA-DQ MA)))
				  idx MA sigs))
		    (INST-tag (LSRM-in-ROB
			       idx (MT-step MT MA sigs)))))
  :hints (("Goal" :in-theory (enable step-sreg-ref lift-b-ops srname-p))))

; An important lemma. Summarizing the three lemmas above.  
; The new value of tag field of register reference table is the Tomasulo's 
; tag of the last special register modifier. 
(defthm INST-tag-LSRM-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (srname-p idx)
		  (not (b1p (MT-specultv-at-dispatch? (MT-step MT MA sigs))))
		  (not (b1p (MT-modified-at-dispatch? (MT-step MT MA sigs))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (b1p (reg-ref-wait?
			(step-sreg-ref (sreg-tbl-nth idx
						     (DQ-sreg-tbl (MA-DQ MA)))
				       idx MA sigs))))
	     (equal (INST-tag (LSRM-in-ROB
			       idx (MT-step MT MA sigs)))
		    (reg-ref-tag (step-sreg-ref
				  (sreg-tbl-nth idx (DQ-sreg-tbl (MA-DQ MA)))
				  idx MA sigs))))
  :hints (("Goal" :cases
		  ((not (b1p (dispatch-inst? MA)))
		   (not (sreg-modifier-p idx (INST-at-stg '(DQ 0) MT)))))))

; A landmark lemma.
; consistent-sreg-ref-p is true for the register idx.
(defthm consistent-sreg-ref-p-MT-step
    (implies (and (inv MT MA)
		  (srname-p idx)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (MT-CMI-p (MT-step MT MA sigs))))
	     (consistent-sreg-ref-p idx (MT-step MT MA sigs)
				    (MA-step MA sigs)))
  :hints (("Goal" :in-theory (enable consistent-sreg-ref-p))))

; A landmark lemma.  Consistent-sreg-tbl-p is preserved.
(defthm consistent-sreg-tbl-p-preserved
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (MT-CMI-p (MT-step MT MA sigs))))
	     (consistent-sreg-tbl-p (MT-step MT MA sigs)
				    (MA-step MA sigs)))
  :hints (("Goal" :in-theory (enable consistent-sreg-tbl-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Proof of consistent-RS-p
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Rules about Common Data Bus and instruction stage.
; If the common data bus is not available, the instruction cannot make
; progress. 
; If instruction i is currently at the integer unit, and the Common data
; bus is not ready for instruction i, then i will stay in the integer unit. 
; Similar lemmas are proven for MU, BU, and LSU in 
;  MU-stg-p-step-inst-if-not-CDB-ready-for
;  BU-stg-p-step-inst-if-not-CDB-ready-for
;  LSU-stg-p-step-inst-if-not-CDB-ready-for
(defthm IU-stg-p-step-inst-if-not-CDB-ready-for
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)   
		  (MAETT-p MT) (MA-state-p MA)
		  (IU-stg-p (INST-stg i))
		  (not (b1p (CDB-ready-for? (INST-tag i) MA))))
	     (IU-stg-p (INST-stg (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (enable IU-stg-p
				     INST-STG-STEP-INST-IU-RS0
				     INST-STG-STEP-INST-IU-RS1
				     lift-b-ops CDB-tag
				     IU-OUTPUT-tag
				     CDB-ready-for? CDB-ready?
				     IU-RS1-ISSUE-READY?
				     CDB-FOR-IU?
				     issue-IU-RS0? issue-IU-RS1?))))

(defthm MU-stg-p-step-inst-if-not-CDB-ready-for
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)   
		  (MAETT-p MT) (MA-state-p MA)
		  (MU-stg-p (INST-stg i))
		  (not (b1p (CDB-ready-for? (INST-tag i) MA))))
	     (MU-stg-p (INST-stg (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (enable MU-stg-p
				     CDB-FOR-IU?
				     INST-STG-STEP-INST-MU-RS0
				     INST-STG-STEP-INST-MU-RS1
				     INST-STG-STEP-INST-MU-LCH1
				     INST-STG-STEP-INST-MU-LCH2
				     lift-b-ops CDB-tag
				     CDB-FOR-MU? CDB-ready-for? CDB-ready?
				     IU-output-tag CDB-FOR-BU?))))
				     

(defthm BU-stg-p-step-inst-if-not-CDB-ready-for
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)   
		  (MAETT-p MT) (MA-state-p MA)
		  (BU-stg-p (INST-stg i))
		  (not (b1p (CDB-ready-for? (INST-tag i) MA))))
	     (BU-stg-p (INST-stg (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (enable BU-stg-p CDB-ready-for?
				     CDB-READY? CDB-for-BU?
				     INST-STG-STEP-INST-BU-RS0
				     INST-STG-STEP-INST-BU-RS1
				     lift-b-ops CDB-tag
				     CDB-FOR-IU? ISSUE-BU-RS0?
				     ISSUE-BU-RS1?
				     BU-RS1-ISSUE-READY?
				     BU-OUTPUT-tag))))

(defthm LSU-stg-p-step-inst-if-not-CDB-ready-for
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)   
		  (MAETT-p MT) (MA-state-p MA)
		  (LSU-stg-p (INST-stg i))
		  (not (b1p (CDB-ready-for? (INST-tag i) MA))))
	     (LSU-stg-p (INST-stg (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (enable LSU-stg-p CDB-ready-for? lift-b-ops
				     CDB-READY? CDB-for-LSU?
				     INST-STG-STEP-INST-LSU-RS0
				     INST-STG-STEP-INST-LSU-RS1
				     INST-STG-STEP-INST-LSU-RBUF
				     INST-STG-STEP-INST-LSU-WBUF1-LCH
				     INST-STG-STEP-INST-LSU-WBUF0
				     INST-STG-STEP-INST-LSU-WBUF1
				     INST-stg-step-INST-LSU-wbuf0-lch
				     CDB-tag))))

; Summarize the four lemmas above.  If the instruction i is in the
; execution stage, and the common data bus is not ready for it, i will stay
; in execution stage.
(defthm execute-stg-p-step-inst-if-not-CDB-ready-for
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)   
		  (MAETT-p MT) (MA-state-p MA)
		  (execute-stg-p (INST-stg i))
		  (not (b1p (CDB-ready-for? (INST-tag i) MA))))
	     (execute-stg-p (INST-stg (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (enable execute-stg-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
; Rewriting Rules derived from consistent-RS-p
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; 
(local
(defthm snrname-p-INST-ra-if-not-decode-error
    (implies (and (INST-p i)
		  (not (b1p (INST-decode-error? i)))
		  (b1p (logbit 3 (cntlv-operand (INST-cntlv i)))))
	     (srname-p (INST-ra i)))
  :hints (("goal" :in-theory (enable srname-p INST-decode-error?
				     decode-illegal-inst? INST-opcode
				     decode rdb logbit*
				     INST-cntlv lift-b-ops)))))

; Some help lemmas about cntlv
(defthm cntlv-operand0-if-logbit1-exunit
    (implies (and (INST-p i) (b1p (logbit 1 (cntlv-exunit (INST-cntlv i)))))
	     (equal (logbit 0 (cntlv-operand (INST-cntlv i))) 1))
  :hints (("Goal" :in-theory (enable INST-cntlv lift-b-ops
				     equal-b1p-converter
				     decode logbit* rdb))))

(defthm cntlv-operand0-if-logbit2-exunit
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i))
		  (b1p (logbit 2 (cntlv-exunit (INST-cntlv i))))
		  (not (b1p (dispatch-ready1? MA)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (logbit 0 (cntlv-operand (INST-cntlv i))) 1))
  :hints (("Goal" :in-theory (enable INST-cntlv lift-b-ops
				     dispatch-ready1? DQ-out-ready1?
				     equal-b1p-converter
				     decode logbit* rdb))))

(defthm cntlv-operand0-if-logbit3-exunit
    (implies (and (INST-p i) (b1p (logbit 3 (cntlv-exunit (INST-cntlv i)))))
	     (equal (logbit 2 (cntlv-operand (INST-cntlv i))) 1))
  :hints (("Goal" :in-theory (enable INST-cntlv lift-b-ops
				     equal-b1p-converter
				     decode logbit* rdb))))

; Lemmas derived from consistent-RS-p
; These rules are used to prove the invariantness lemma for consistent-RS-p.
(encapsulate nil
(local
(defthm consistent-RS-entry-p-inst-in-help
    (implies (and (trace-consistent-RS-p trace MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (member-equal i trace) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA))
	     (consistent-RS-entry-p i MT MA))))

; If invariants hold for MT and MA, consistent-RS-entry-p is
; correct for any instruction in MT.  Intuitively, the reservation
; station storing i contains correct values.  
(defthm consistent-RS-entry-p-inst-in
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA))
	     (consistent-RS-entry-p i MT MA))
  :hints (("Goal" :in-theory (enable inv consistent-RS-p
				     INST-in)))
  :rule-classes nil)
)
; 
; Following 61 lemmas are direct consequence from consistent-RS-entry-p.
; 
; Please see the comments on Consistent-RS-p in invariants-def.lisp for 
; their implication.  We convert the invariants consistent-RS-p into 
; rewriting rules.
; 
; There are some possibilities of generating these lemmas automatically,
; but we have not tried yet. 
; 
(defthm exist-LRM-before-p-IU-RS0-if-logbit0-ra
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(IU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (IU-RS0 (MA-IU MA)))))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LRM-before-p i (INST-ra i) MT))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm execute-stg-p-LRM-before-IU-RS0-if-logbit0-ra
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)  
		  (equal (INST-stg i) '(IU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (IU-RS0 (MA-IU MA)))))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (execute-stg-p (INST-stg (LRM-before i (INST-ra i) MT))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm INST-tag-LRM-before-IU-RS0-if-logbit0-ra
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(IU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (IU-RS0 (MA-IU MA)))))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (LRM-before i (INST-ra i) MT))
		    (RS-src1 (IU-RS0 (MA-IU MA)))))
    :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				       CONSISTENT-IU-RS-P
				       CONSISTENT-IU-RS0-P)
		    :use (:instance consistent-RS-entry-p-inst-in))))

(defthm exist-LRM-before-p-IU-RS0-if-logbit0-rb
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(IU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready2? (IU-RS0 (MA-IU MA)))))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LRM-before-p i (INST-rb i) MT))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm execute-stg-p-LRM-before-IU-RS0-if-logbit0-rb
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(IU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready2? (IU-RS0 (MA-IU MA)))))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (execute-stg-p (INST-stg (LRM-before i (INST-rb i) MT))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm INST-tag-LRM-before-IU-RS0-if-logbit0-rb
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(IU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready2? (IU-RS0 (MA-IU MA)))))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (LRM-before i (INST-rb i) MT))
		    (RS-src2 (IU-RS0 (MA-IU MA)))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm exist-LRM-before-p-IU-RS0-if-logbit2
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(IU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (IU-RS0 (MA-IU MA)))))
		  (b1p (logbit 2 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LRM-before-p i (INST-rc i) MT))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm execute-stg-p-LRM-before-IU-RS0-if-logbit2
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(IU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (IU-RS0 (MA-IU MA)))))
		  (b1p (logbit 2 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (execute-stg-p (INST-stg (LRM-before i (INST-rc i) MT))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm INST-tag-LRM-before-IU-RS0-if-logbit2
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(IU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (IU-RS0 (MA-IU MA)))))
		  (b1p (logbit 2 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (LRM-before i (INST-rc i) MT))
		    (RS-src1 (IU-RS0 (MA-IU MA)))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm exist-LSRM-before-p-IU-RS0-if-logbit3
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(IU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (IU-RS0 (MA-IU MA)))))
		  (b1p (logbit 3 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LSRM-before-p i (INST-ra i) MT))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm execute-stg-p-LSRM-before-IU-RS0-if-logbit3
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(IU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (IU-RS0 (MA-IU MA)))))
		  (b1p (logbit 3 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (execute-stg-p (INST-stg (LSRM-before i (INST-ra i) MT))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm INST-tag-LSRM-before-IU-RS0-if-logbit3
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(IU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (IU-RS0 (MA-IU MA)))))
		  (b1p (logbit 3 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (LSRM-before i (INST-ra i) MT))
		    (RS-src1 (IU-RS0 (MA-IU MA)))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm exist-LRM-before-p-IU-RS1-if-logbit0-ra
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(IU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (IU-RS1 (MA-IU MA)))))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LRM-before-p i (INST-ra i) MT))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm execute-stg-p-LRM-before-IU-RS1-if-logbit0-ra
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)  
		  (equal (INST-stg i) '(IU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (IU-RS1 (MA-IU MA)))))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (execute-stg-p (INST-stg (LRM-before i (INST-ra i) MT))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm INST-tag-LRM-before-if-IU-RS1-logbit0-ra
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(IU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (IU-RS1 (MA-IU MA)))))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (LRM-before i (INST-ra i) MT))
		    (RS-src1 (IU-RS1 (MA-IU MA)))))
    :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				       CONSISTENT-IU-RS-P
				       CONSISTENT-IU-RS1-P)
		    :use (:instance consistent-RS-entry-p-inst-in))))

(defthm exist-LRM-before-p-if-IU-RS1-logbit0-rb
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(IU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready2? (IU-RS1 (MA-IU MA)))))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LRM-before-p i (INST-rb i) MT))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm execute-stg-p-LRM-before-if-IU-RS1-logbit0-rb
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(IU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready2? (IU-RS1 (MA-IU MA)))))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (execute-stg-p (INST-stg (LRM-before i (INST-rb i) MT))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm INST-tag-LRM-before-if-IU-RS1-logbit0-rb
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(IU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready2? (IU-RS1 (MA-IU MA)))))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (LRM-before i (INST-rb i) MT))
		    (RS-src2 (IU-RS1 (MA-IU MA)))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm exist-LRM-before-p-if-IU-RS1-logbit2
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(IU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (IU-RS1 (MA-IU MA)))))
		  (b1p (logbit 2 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LRM-before-p i (INST-rc i) MT))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm execute-stg-p-LRM-before-if-IU-RS1-logbit2
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(IU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (IU-RS1 (MA-IU MA)))))
		  (b1p (logbit 2 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (execute-stg-p (INST-stg (LRM-before i (INST-rc i) MT))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm INST-tag-LRM-before-if-IU-RS1-logbit2
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(IU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (IU-RS1 (MA-IU MA)))))
		  (b1p (logbit 2 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (LRM-before i (INST-rc i) MT))
		    (RS-src1 (IU-RS1 (MA-IU MA)))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm exist-LSRM-before-p-if-IU-RS1-logbit3
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(IU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (IU-RS1 (MA-IU MA)))))
		  (b1p (logbit 3 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LSRM-before-p i (INST-ra i) MT))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm execute-stg-p-LSRM-before-if-IU-RS1-logbit3
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(IU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (IU-RS1 (MA-IU MA)))))
		  (b1p (logbit 3 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (execute-stg-p (INST-stg (LSRM-before i (INST-ra i) MT))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm INST-tag-LSRM-before-if-IU-RS1-logbit3
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(IU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (IU-RS1 (MA-IU MA)))))
		  (b1p (logbit 3 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (LSRM-before i (INST-ra i) MT))
		    (RS-src1 (IU-RS1 (MA-IU MA)))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-IU-RS-P
				     CONSISTENT-IU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm exist-LRM-before-p-if-MU-RS0-ra
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(MU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (MU-RS0 (MA-MU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LRM-before-p i (INST-ra i) MT))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-MU-RS-P
				     CONSISTENT-MU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm execute-stg-p-LRM-before-if-MU-RS0-ra
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(MU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (MU-RS0 (MA-MU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (execute-stg-p (INST-stg (LRM-before i (INST-ra i) MT))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-MU-RS-P
				     CONSISTENT-MU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm INST-tag-LRM-before-if-MU-RS0-ra
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(MU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (MU-RS0 (MA-MU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (LRM-before i (INST-ra i) MT))
		    (RS-src1 (MU-RS0 (MA-MU MA)))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-MU-RS-P
				     CONSISTENT-MU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm exist-LRM-before-p-if-MU-RS0-rb
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(MU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready2? (MU-RS0 (MA-MU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LRM-before-p i (INST-rb i) MT))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-MU-RS-P
				     CONSISTENT-MU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm execute-stg-p-LRM-before-if-MU-RS0-rb
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(MU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready2? (MU-RS0 (MA-MU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (execute-stg-p (INST-stg (LRM-before i (INST-rb i) MT))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-MU-RS-P
				     CONSISTENT-MU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm INST-tag-LRM-before-if-MU-RS0-rb
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(MU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready2? (MU-RS0 (MA-MU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (LRM-before i (INST-rb i) MT))
		    (RS-src2 (MU-RS0 (MA-MU MA)))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-MU-RS-P
				     CONSISTENT-MU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm exist-LRM-before-p-if-MU-RS1-ra
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(MU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (MU-RS1 (MA-MU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LRM-before-p i (INST-ra i) MT))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-MU-RS-P
				     CONSISTENT-MU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm execute-stg-p-LRM-before-if-MU-RS1-ra
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(MU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (MU-RS1 (MA-MU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (execute-stg-p (INST-stg (LRM-before i (INST-ra i) MT))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-MU-RS-P
				     CONSISTENT-MU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm INST-tag-LRM-before-if-MU-RS1-ra
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(MU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready1? (MU-RS1 (MA-MU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (LRM-before i (INST-ra i) MT))
		    (RS-src1 (MU-RS1 (MA-MU MA)))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-MU-RS-P
				     CONSISTENT-MU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm exist-LRM-before-p-if-MU-RS1-rb
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(MU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready2? (MU-RS1 (MA-MU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LRM-before-p i (INST-rb i) MT))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-MU-RS-P
				     CONSISTENT-MU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm execute-stg-p-LRM-before-if-MU-RS1-rb
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(MU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready2? (MU-RS1 (MA-MU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (execute-stg-p (INST-stg (LRM-before i (INST-rb i) MT))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-MU-RS-P
				     CONSISTENT-MU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm INST-tag-LRM-before-if-MU-RS1-rb
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(MU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (RS-ready2? (MU-RS1 (MA-MU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (LRM-before i (INST-rb i) MT))
		    (RS-src2 (MU-RS1 (MA-MU MA)))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-MU-RS-P
				     CONSISTENT-MU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm INST-tag-LRM-before-step-INST-rc
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))		  
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (dispatch-ready3? MA))))
	     (equal (INST-tag (LRM-before (step-INST i MT MA sigs)
					  (INST-rc i)
					  (MT-step MT MA sigs)))
		    (dispatch-src3 MA)))
  :hints (("goal" :in-theory (enable dispatch-src3 DQ-out-tag3
				     DISPATCH-READY3? lift-b-ops
		     MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
		     INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
		     INST-cntlv DQ-out-tag3 DQ-OUT-READY3?)
		  :restrict
		  ((MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
		    ((i i)))
		   (INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
		    ((i i)))))))

(defthm exist-LRM-before-p-if-BU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(BU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (BU-RS-ready? (BU-RS0 (MA-BU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LRM-before-p i (INST-rc i) MT))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-BU-RS-P
				     CONSISTENT-BU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm execute-stg-p-LRM-before-if-BU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(BU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (BU-RS-ready? (BU-RS0 (MA-BU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (execute-stg-p (INST-stg (LRM-before i (INST-rc i) MT))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-BU-RS-P
				     CONSISTENT-BU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm INST-tag-LRM-before-if-BU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(BU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (BU-RS-ready? (BU-RS0 (MA-BU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (LRM-before i (INST-rc i) MT))
		    (BU-RS-src (BU-RS0 (MA-BU MA)))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-BU-RS-P
				     CONSISTENT-BU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm exist-LRM-before-p-if-BU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(BU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (BU-RS-ready? (BU-RS1 (MA-BU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LRM-before-p i (INST-rc i) MT))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-BU-RS-P
				     CONSISTENT-BU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm execute-stg-p-LRM-before-if-BU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(BU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (BU-RS-ready? (BU-RS1 (MA-BU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (execute-stg-p (INST-stg (LRM-before i (INST-rc i) MT))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-BU-RS-P
				     CONSISTENT-BU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm INST-tag-LRM-before-if-BU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(BU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (BU-RS-ready? (BU-RS1 (MA-BU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (LRM-before i (INST-rc i) MT))
		    (BU-RS-src (BU-RS1 (MA-BU MA)))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-BU-RS-P
				     CONSISTENT-BU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm exist-reg-ra-modifier-before-if-LSU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(LSU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (LSU-RS-rdy1? (LSU-RS0 (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LRM-before-p i (INST-ra i) MT))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-LSU-RS-P
				     CONSISTENT-LSU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm execute-stg-p-last-reg-ra-modifier-before-if-LSU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(LSU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (LSU-RS-rdy1? (LSU-RS0 (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (execute-stg-p (INST-stg (LRM-before i (INST-ra i) MT))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-LSU-RS-P
				     CONSISTENT-LSU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm INST-tag-last-reg-ra-modifier-before-if-LSU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(LSU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (LSU-RS-rdy1? (LSU-RS0 (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (LRM-before i (INST-ra i) MT))
		    (LSU-RS-src1 (LSU-RS0 (MA-LSU MA)))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-LSU-RS-P
				     CONSISTENT-LSU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm exist-reg-rb-modifier-before-if-LSU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(LSU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (LSU-RS-rdy2? (LSU-RS0 (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LRM-before-p i (INST-rb i) MT))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-LSU-RS-P
				     CONSISTENT-LSU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm execute-stg-p-last-reg-rb-modifier-before-if-LSU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(LSU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (LSU-RS-rdy2? (LSU-RS0 (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (execute-stg-p (INST-stg (LRM-before i (INST-rb i) MT))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-LSU-RS-P
				     CONSISTENT-LSU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm INST-tag-last-reg-rb-modifier-before-if-LSU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(LSU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (LSU-RS-rdy2? (LSU-RS0 (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (LRM-before i (INST-rb i) MT))
		    (LSU-RS-src2 (LSU-RS0 (MA-LSU MA)))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-LSU-RS-P
				     CONSISTENT-LSU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm exist-reg-rc-modifier-before-if-LSU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(LSU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (LSU-RS-rdy3? (LSU-RS0 (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LRM-before-p i (INST-rc i) MT))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-LSU-RS-P
				     CONSISTENT-LSU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm execute-stg-p-last-reg-rc-modifier-before-if-LSU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(LSU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (LSU-RS-rdy3? (LSU-RS0 (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (execute-stg-p (INST-stg (LRM-before i (INST-rc i) MT))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-LSU-RS-P
				     CONSISTENT-LSU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm INST-tag-last-reg-rc-modifier-before-if-LSU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(LSU RS0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (LSU-RS-rdy3? (LSU-RS0 (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (LRM-before i (INST-rc i) MT))
		    (LSU-RS-src3 (LSU-RS0 (MA-LSU MA)))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-LSU-RS-P
				     CONSISTENT-LSU-RS0-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm exist-reg-ra-modifier-before-if-LSU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(LSU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (LSU-RS-rdy1? (LSU-RS1 (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LRM-before-p i (INST-ra i) MT))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-LSU-RS-P
				     CONSISTENT-LSU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm execute-stg-p-last-reg-ra-modifier-before-if-LSU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(LSU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (LSU-RS-rdy1? (LSU-RS1 (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (execute-stg-p (INST-stg (LRM-before i (INST-ra i) MT))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-LSU-RS-P
				     CONSISTENT-LSU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm INST-tag-last-reg-ra-modifier-before-if-LSU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(LSU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (LSU-RS-rdy1? (LSU-RS1 (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (LRM-before i (INST-ra i) MT))
		    (LSU-RS-src1 (LSU-RS1 (MA-LSU MA)))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-LSU-RS-P
				     CONSISTENT-LSU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm exist-reg-rb-modifier-before-if-LSU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(LSU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (LSU-RS-rdy2? (LSU-RS1 (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LRM-before-p i (INST-rb i) MT))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-LSU-RS-P
				     CONSISTENT-LSU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm execute-stg-p-last-reg-rb-modifier-before-if-LSU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(LSU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (LSU-RS-rdy2? (LSU-RS1 (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (execute-stg-p (INST-stg (LRM-before i (INST-rb i) MT))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-LSU-RS-P
				     CONSISTENT-LSU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm INST-tag-last-reg-rb-modifier-before-if-LSU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(LSU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (LSU-RS-rdy2? (LSU-RS1 (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (LRM-before i (INST-rb i) MT))
		    (LSU-RS-src2 (LSU-RS1 (MA-LSU MA)))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-LSU-RS-P
				     CONSISTENT-LSU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm exist-reg-rc-modifier-before-if-LSU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(LSU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (LSU-RS-rdy3? (LSU-RS1 (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LRM-before-p i (INST-rc i) MT))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-LSU-RS-P
				     CONSISTENT-LSU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm execute-stg-p-last-reg-rc-modifier-before-if-LSU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(LSU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (LSU-RS-rdy3? (LSU-RS1 (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (execute-stg-p (INST-stg (LRM-before i (INST-rc i) MT))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-LSU-RS-P
				     CONSISTENT-LSU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

(defthm INST-tag-last-reg-rc-modifier-before-if-LSU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (equal (INST-stg i) '(LSU RS1))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (LSU-RS-rdy3? (LSU-RS1 (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (LRM-before i (INST-rc i) MT))
		    (LSU-RS-src3 (LSU-RS1 (MA-LSU MA)))))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p
				     CONSISTENT-LSU-RS-P
				     CONSISTENT-LSU-RS1-P)
		  :use (:instance consistent-RS-entry-p-inst-in))))

;;;; end of lemmas derived from consistent-RS-p

;;; Proof of consistent-RS-p for initial states
(defthm consistent-RS-p-init-MT
    (consistent-RS-p (init-MT MA) MA)
  :hints (("goal" :in-theory (enable init-MT consistent-RS-p))))

;;; invariant proof
; The proof approach is showing that each instruction satisfies
; consistent-RS-entry-p. Then prove consistent-RS-p by induction on
; instructions. 

(defthm consistent-RS-entry-p-exintr-INST
    (consistent-RS-entry-p (exintr-INST MT ISA SMC) MT2 MA2)
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p))))

(defthm consistent-RS-entry-p-fetched-inst
    (consistent-RS-entry-p (fetched-inst MT ISA SPC SMC) MT2 MA2)
  :hints (("goal" :in-theory (enable consistent-RS-entry-p))))

; Minor case analysis follows.  Instead of explaining every case,
; I will explain only this case. 
;  
; Suppose dispatch-ready1? is 0 in the current cycle.  Instruction i
; is not speculatively executed, it is not in the self-modified
; instruction stream, or it has not caused any fetch error. (And
; flush-all? is 0, implying that no context switching takes place in
; this cycle.)  Since (logbit 0 (cntlv-operand (INST-cntlv i))) = 1,
; operands of instruction i are source register RA and RB.  If
; dispatch-ready1? is 0, the operand source register RA is not ready
; to supply the register value.  Thus, there should be a register
; modifier of register RA before instruction i, and this is true in
; the next state.
; 
; The list of similar lemmas are:
;  exist-LRM-before-p-step-INST-operand0-rb
;  exist-LRM-before-p-step-INST-operand2
;  exist-LSRM-before-p-step-INST-operand3 
;  exist-LRM-before-p-step-INST-rc
; exist-LRM-before-p-step-INST-operand2
(defthm exist-uncommitted-LRM-before-p-step-INST-operand0-ra
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))		  
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (dispatch-ready1? MA)))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-uncommitted-LRM-before-p (step-INST i MT MA sigs)
					     (INST-ra i)
					     (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory
		  (enable dispatch-ready1? lift-b-ops
			  MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
			  INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
			  DQ-out-tag1 DQ-OUT-READY1?)
		  :restrict
		  ((MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
		    ((i i)))
		   (INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
		    ((i i)))))))

(defthm exist-uncommitted-LRM-before-p-step-INST-operand0-rb
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))		  
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-inst? MA))
		  (not (b1p (dispatch-ready2? MA)))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-uncommitted-LRM-before-p (step-INST i MT MA sigs)
					     (INST-rb i)
					     (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory
		  (enable dispatch-ready2? lift-b-ops
			  MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
			  INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
			  DQ-out-tag2 DQ-OUT-READY2?)
		  :restrict
		  ((MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
		    ((i i)))
		   (INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
		    ((i i)))))))

(defthm exist-uncommitted-LRM-before-p-step-INST-operand2
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(DQ 0))
		  (b1p (dispatch-inst? MA))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))		  
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (dispatch-ready1? MA)))
		  (b1p (logbit 2 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-uncommitted-LRM-before-p (step-INST i MT MA sigs)
					     (INST-rc i)
					     (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory
		  (enable dispatch-ready1? lift-b-ops
			  MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
			  INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
			  DQ-out-tag1 DQ-OUT-READY1? INST-cntlv)
		  :restrict
		  ((MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
		    ((i i)))
		   (INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
		    ((i i)))))))

(defthm exist-uncommitted-LSRM-before-p-step-INST-operand3
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(DQ 0))
		  (b1p (dispatch-inst? MA))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))		  
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (INST-decode-error? i)))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (dispatch-ready1? MA)))
		  (b1p (logbit 3 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-uncommitted-LSRM-before-p (step-INST i MT MA sigs)
					      (INST-ra i)
					      (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory
		  (enable dispatch-ready1? lift-b-ops
			  MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
			  INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
			  INST-cntlv
			  DQ-out-tag1 DQ-OUT-READY1?)
		  :restrict
		  ((MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
		    ((i i)))
		   (INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
		    ((i i)))))))

(defthm exist-uncommitted-LRM-before-p-step-INST-rc
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))		  
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (dispatch-ready3? MA)))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-uncommitted-LRM-before-p (step-INST i MT MA sigs)
					     (INST-rc i)
					     (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory
		  (enable dispatch-ready3? lift-b-ops
			  MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
			  INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
			  DQ-out-tag3 DQ-OUT-READY3?)
		  :restrict
		  ((MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
		    ((i i)))
		   (INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
		    ((i i)))))))

; This lemmas and following similar lemmas are minor case analysis.  I
; will explain only this in detail Suppose instruction i is at the
; head of the dispatch queue.  And the control vector suggests that
; the operands for the instruction are RA and RB.  When instruction i
; is dispatched, dispatch-src1 provides Tomasulo's tag for the
; instruction that generates the source operand.  In fact, this
; indexes the ROB entry to which the last register modifier is
; assigned.  Since the last register modifier is the producer of the
; source operand, dispatch-src1 is correct.
; 
; Similar lemmas are
;  INST-tag-LRM-before-step-INST-logbit0-rb
;  INST-tag-LRM-before-step-INST-logbit2
;  INST-tag-LSRM-before-step-INST-logbit3
(defthm INST-tag-LRM-before-step-INST-logbit0-ra
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)  
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))		  
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (dispatch-ready1? MA)))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i)))))
	     (equal (INST-tag (LRM-before (step-INST i MT MA sigs)
					  (INST-ra i)
					  (MT-step MT MA sigs)))
		    (dispatch-src1 MA)))
  :hints (("goal" :in-theory (enable dispatch-src1 DQ-out-tag1
				     DISPATCH-READY1? lift-b-ops
		     MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
		     INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
		     DQ-out-tag1 DQ-OUT-READY1?)
		  :restrict
		  ((MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
		    ((i i)))
		   (INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
		    ((i i)))))))

(defthm INST-tag-LRM-before-step-INST-logbit0-rb
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))		  
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (dispatch-ready2? MA))))
	     (equal (INST-tag (LRM-before (step-INST i MT MA sigs)
					  (INST-rb i)
					  (MT-step MT MA sigs)))
		    (dispatch-src2 MA)))
  :hints (("goal" :in-theory (enable dispatch-src2 DQ-out-tag2
				     DISPATCH-READY2? lift-b-ops
		     MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
		     INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
		     DQ-out-tag2 DQ-OUT-READY2?)
		  :restrict
		  ((MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
		    ((i i)))
		   (INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
		    ((i i)))))))

(defthm INST-tag-LRM-before-step-INST-logbit2
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))		  
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (dispatch-ready1? MA)))
		  (b1p (logbit 2 (cntlv-operand (INST-cntlv i)))))
	     (equal (INST-tag (LRM-before (step-INST i MT MA sigs)
					  (INST-rc i)
					  (MT-step MT MA sigs)))
		    (dispatch-src1 MA)))
  :hints (("goal" :in-theory (enable dispatch-src1 DQ-out-tag1
				     DISPATCH-READY1? lift-b-ops
		     MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
		     INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
		     INST-cntlv DQ-out-tag1 DQ-OUT-READY1?)
		  :restrict
		  ((MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
		    ((i i)))
		   (INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
		    ((i i)))))))

(defthm INST-tag-LSRM-before-step-INST-logbit3
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))		  
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (INST-decode-error? i)))
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (dispatch-ready1? MA)))
		  (b1p (logbit 3 (cntlv-operand (INST-cntlv i)))))
	     (equal (INST-tag (LSRM-before (step-INST i MT MA sigs)
					   (INST-ra i)
					   (MT-step MT MA sigs)))
		    (dispatch-src1 MA)))
  :hints (("goal" :in-theory (enable dispatch-src1 DQ-out-tag1
				     DISPATCH-READY1? lift-b-ops
		     MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
		     INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
		     INST-cntlv DQ-out-tag1 DQ-OUT-READY1?)
		  :restrict
		  ((MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
		    ((i i)))
		   (INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
		    ((i i)))))))

; Following several lemmas are similar to each other.  I will only explain
; the first lemma.  If instruction i is at the head of dispatch queue, and
; its operand RA is not ready, then the last register modifier 
; of register RA will still be in the execution stage in the next state. 
; 
; Note: If the register modifier completes its operation this cycle, its value
; should be on the CDB.  But dispatch-ready1? is 0 implies that it is not.
; 
; Similar lemmas are proven in:
;  execute-stg-p-LRM-before-step-INST-if-logbit0-rb
;  execute-stg-p-LRM-before-step-INST-if-logbit2
;  execute-stg-p-LSRM-before-step-INST-if-logbit3
;  execute-stg-p-LRM-before-step-INST-rc
(defthm execute-stg-p-LRM-before-step-INST-if-logbit0-ra
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))		  
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (dispatch-ready1? MA)))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i)))))
	     (execute-stg-p (INST-stg (LRM-before (step-INST i MT MA sigs)
						  (INST-ra I)
						  (MT-step MT MA sigs)))))
  :hints (("Goal" :in-theory (enable dispatch-ready1? lift-b-ops
				     DQ-out-tag1
		     MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
		     INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
		     DQ-out-ready1?))))

(defthm execute-stg-p-LRM-before-step-INST-if-logbit0-rb
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))		  
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (dispatch-ready2? MA))))
	     (execute-stg-p
	      (INST-stg (LRM-before (step-INST i MT MA sigs)
				    (INST-rb I)
				    (MT-step MT MA sigs)))))
  :hints (("Goal" :in-theory (enable dispatch-ready2? lift-b-ops
				     DQ-out-tag2
		     MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
		     INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
		     DQ-out-ready2?))))

(defthm execute-stg-p-LRM-before-step-INST-if-logbit2
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))		  
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (dispatch-ready1? MA)))
		  (b1p (logbit 2 (cntlv-operand (INST-cntlv i)))))
	     (execute-stg-p (INST-stg (LRM-before (step-INST i MT MA sigs)
						  (INST-rc I)
						  (MT-step MT MA sigs)))))
  :hints (("Goal" :in-theory (enable dispatch-ready1? lift-b-ops
				     DQ-out-tag1
				     INST-cntlv
		     MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
		     INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
		     DQ-out-ready1?))))

(defthm execute-stg-p-LSRM-before-step-INST-if-logbit3
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))		  
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (INST-decode-error? I)))
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (dispatch-ready1? MA)))
		  (b1p (logbit 3 (cntlv-operand (INST-cntlv i)))))
	     (execute-stg-p (INST-stg (LSRM-before (step-INST i MT MA sigs)
						   (INST-ra I)
						   (MT-step MT MA sigs)))))
  :hints (("Goal" :in-theory (enable dispatch-ready1? lift-b-ops
				     DQ-out-tag1
				     INST-cntlv
		     MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
		     INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
		     DQ-out-ready1?))))

(defthm execute-stg-p-LRM-before-step-INST-rc
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))		  
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (dispatch-ready3? MA))))
	     (execute-stg-p (INST-stg (LRM-before (step-INST i MT MA sigs)
						  (INST-rc I)
						  (MT-step MT MA sigs)))))
  :hints (("Goal" :in-theory (enable dispatch-ready3? lift-b-ops
				     DQ-out-tag3
				     INST-cntlv
		     MT-SPECULTV-AT-DISPATCH-OFF-IF-NON-SPECULTV-INST-IN
		     INST-MODIFIED-AT-DISPATCH-OFF-IF-UNDISPATCHED-INST-IN
		     DQ-out-ready3?))))

; Proof of consistent-RS-entry-p-step-INST starts here. 
; Following 28 lemmas are preparation for the final proof of
; consistent-RS-entry-p-step-INST, which is basically done by case 
; analysis based on the current and next stage of i.
; For instance, consistent-IU-RS0-p-step-INST-DQ0 shows that
; consistent-IU-RS0-p is correct for i if its current stage is DQ0, and
; next stage is IU-RS0.
; Consistent-IU-RS0-p-step-INST proves consistent-IU-RS0-p for 
; i whose next stage is IU-RS0, regardless of the current stage..  
; 
; Let me list all the 28 lemmas here.
;    consistent-IU-RS0-p-step-INST-DQ0
;    consistent-IU-RS0-p-step-INST-RS0
;   consistent-IU-RS0-p-step-INST
;    consistent-IU-RS1-p-step-INST-DQ0
;    consistent-IU-RS1-p-step-INST-RS1
;   consistent-IU-RS1-p-step-INST
; consistent-IU-RS-p-step-INST
;    consistent-MU-RS0-p-step-INST-DQ0
;    consistent-MU-RS0-p-step-INST-MU-RS0
;   consistent-MU-RS0-p-step-INST
;    consistent-MU-RS1-p-step-INST-DQ0
;    consistent-MU-RS1-p-step-INST-MU-RS1
;   consistent-MU-RS1-p-step-INST
; consistent-MU-RS-p-step-INST
;    consistent-BU-RS0-p-step-INST-DQ0
;    consistent-BU-RS0-p-step-INST-BU-RS0
;   consistent-BU-RS0-p-step-INST
;    consistent-BU-RS1-p-step-INST-DQ0
;    consistent-BU-RS1-p-step-INST-BU-RS1
;   consistent-BU-RS1-p-step-INST
; consistent-BU-RS-p-step-INST
;    consistent-LSU-RS0-p-step-INST-DQ0
;    consistent-LSU-RS0-p-step-INST-LSU-RS0
;   consistent-LSU-RS0-p-step-INST
;    consistent-LSU-RS1-p-step-INST-DQ0
;    consistent-LSU-RS1-p-step-INST-LSU-RS1
;   consistent-LSU-RS1-p-step-INST
; consistent-LSU-RS-p-step-INST

(defthm consistent-IU-RS0-p-step-INST-DQ0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(DQ 0))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(IU RS0))
		  (not (b1p (flush-all? MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-IU-RS0-p (step-INST i MT MA sigs)
				  (MT-step MT MA sigs)
				  (MA-step MA sigs)))
  :hints (("Goal" :cases ((b1p (dispatch-to-IU? MA))))
	  ("subgoal 2" :in-theory (enable step-inst-dq-inst
					  step-inst-low-level-functions))
	  ("subgoal 1" :in-theory (enable consistent-IU-RS0-p
					  INST-STG-STEP-INST-IF-DISPATCH-IU
					  dispatch-inst?
					  step-IU step-IU-RS0
					  lift-b-ops)
		       :cases ((b1p (INST-fetch-error? i))))
	  ("subgoal 1.2" :cases ((b1p (INST-decode-error? i))))
	  ("subgoal 1.2.1" :in-theory (enable dispatch-to-IU? lift-b-ops
					      CONSISTENT-IU-RS0-P
					      DQ-ready-to-IU?
					      exception-relations
					      INST-EXCPT-DETECTED-P))
	  ("subgoal 1.1" :in-theory (enable dispatch-to-IU? lift-b-ops
					    CONSISTENT-IU-RS0-P
					    DQ-ready-to-IU?
					    INST-EXCPT-DETECTED-P))))

(defthm consistent-IU-RS0-p-step-INST-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(IU RS0))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(IU RS0))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-IU-RS0-p (step-INST i MT MA sigs)
				  (MT-step MT MA sigs)
				  (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable consistent-IU-RS0-p
				     lift-b-ops
				     SELECT-IU-RS0?
				     DISPATCH-TO-IU?
				     IU-READY?
				     INST-STG-STEP-INST-IU-RS0
				     step-IU step-IU-RS0))))

(defthm consistent-IU-RS0-p-step-INST
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(IU RS0))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-IU-RS0-p (step-INST i MT MA sigs)
				  (MT-step MT MA sigs)
				  (MA-step MA sigs)))
  :hints (("Goal" :use ((:instance stages-reachable-to-IU-RS0)))))

(defthm consistent-IU-RS1-p-step-INST-DQ0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(DQ 0))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(IU RS1))
		  (not (b1p (flush-all? MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-IU-RS1-p (step-INST i MT MA sigs)
				  (MT-step MT MA sigs)
				  (MA-step MA sigs)))
  :hints (("Goal" :cases ((b1p (dispatch-to-IU? MA))))
	  ("subgoal 2" :in-theory (enable step-inst-dq-inst
					  step-inst-low-level-functions))
	  ("subgoal 1" :in-theory (enable consistent-IU-RS1-p
					  INST-STG-STEP-INST-IF-DISPATCH-IU
					  dispatch-inst?
					  SELECT-IU-RS0? SELECT-IU-RS1?
					  DISPATCH-TO-IU? IU-READY?
					  step-IU step-IU-RS1
					  lift-b-ops)
		       :cases ((b1p (INST-fetch-error? i))))
	  ("subgoal 1.2" :cases ((b1p (INST-decode-error? i))))
	  ("subgoal 1.2.1" :in-theory (enable dispatch-to-IU? lift-b-ops
					      CONSISTENT-IU-RS1-P
					      DQ-ready-to-IU?
					      exception-relations
					      INST-EXCPT-DETECTED-P))
	  ("subgoal 1.1" :in-theory (enable dispatch-to-IU? lift-b-ops
					    CONSISTENT-IU-RS1-P
					    DQ-ready-to-IU?
					    INST-EXCPT-DETECTED-P))))

(defthm consistent-IU-RS1-p-step-INST-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(IU RS1))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(IU RS1))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-IU-RS1-p (step-INST i MT MA sigs)
				  (MT-step MT MA sigs)
				  (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable consistent-IU-RS1-p
				     lift-b-ops
				     SELECT-IU-RS1?
				     DISPATCH-TO-IU?
				     IU-READY?
				     INST-STG-STEP-INST-IU-RS1
				     step-IU step-IU-RS1))))

(defthm consistent-IU-RS1-p-step-INST
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(IU RS1))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-IU-RS1-p (step-INST i MT MA sigs)
				  (MT-step MT MA sigs)
				  (MA-step MA sigs)))
  :hints (("Goal" :use ((:instance stages-reachable-to-IU-RS1)))))

(defthm consistent-IU-RS-p-step-INST
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (IU-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-IU-RS-p (step-INST i MT MA sigs)
				 (MT-step MT MA sigs)
				 (MA-step MA sigs)))
  :hints (("Goal" :in-theory (enable consistent-IU-RS-p))))

(defthm consistent-MU-RS0-p-step-INST-DQ0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(DQ 0))
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU RS0))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-MU-RS0-p (step-INST i MT MA sigs)
				  (MT-step MT MA sigs)
				  (MA-step MA sigs)))
    :hints (("Goal" :cases ((b1p (dispatch-to-MU? MA))))
	    ("subgoal 2" :in-theory (enable step-inst-dq-inst
					    step-inst-low-level-functions))
	    ("subgoal 1" :in-theory (enable consistent-MU-RS0-p
					    INST-STG-STEP-INST-IF-DISPATCH-MU
					    DQ-READY-TO-MU?
					    dispatch-inst?
					    DISPATCH-TO-MU? MU-READY?
					    step-MU step-MU-RS0
					    lift-b-ops)
			 :cases ((b1p (INST-fetch-error? i))))
	    ("subgoal 1.2" :cases ((b1p (INST-decode-error? i))))
	    ("subgoal 1.2.1" :in-theory (enable dispatch-to-MU? lift-b-ops
						CONSISTENT-MU-RS0-P
						DQ-READY-TO-MU?
						exception-relations
						INST-EXCPT-DETECTED-P))
	    ("subgoal 1.1" :in-theory (enable dispatch-to-MU? lift-b-ops
					      CONSISTENT-MU-RS0-P
					      DQ-ready-to-MU?
					      INST-EXCPT-DETECTED-P))))

(defthm consistent-MU-RS0-p-step-INST-MU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(MU RS0))
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU RS0))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-MU-RS0-p (step-INST i MT MA sigs)
				  (MT-step MT MA sigs)
				  (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable consistent-MU-RS0-p
				     lift-b-ops
				     SELECT-MU-RS0?
				     DISPATCH-TO-MU?
				     MU-READY?
				     INST-STG-STEP-INST-MU-RS0
				     step-MU step-MU-RS0))))

(defthm consistent-MU-RS0-p-step-INST
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU RS0))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-MU-RS0-p (step-INST i MT MA sigs)
				  (MT-step MT MA sigs)
				  (MA-step MA sigs)))
  :hints (("Goal" :use ((:instance stages-reachable-to-MU-RS0)))))

(defthm consistent-MU-RS1-p-step-INST-DQ0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(DQ 0))
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU RS1))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-MU-RS1-p (step-INST i MT MA sigs)
				  (MT-step MT MA sigs)
				  (MA-step MA sigs)))
    :hints (("Goal" :cases ((b1p (dispatch-to-MU? MA))))
	    ("subgoal 2" :in-theory (enable step-inst-dq-inst
					    step-inst-low-level-functions))
	    ("subgoal 1" :in-theory (enable consistent-MU-RS1-p
					    INST-STG-STEP-INST-IF-DISPATCH-MU
					    DQ-READY-TO-MU?
					    dispatch-inst?
					    SELECT-MU-RS0? SELECT-MU-RS1?
					    DISPATCH-TO-MU? MU-READY?
					    step-MU step-MU-RS1
					    lift-b-ops)
			 :cases ((b1p (INST-fetch-error? i))))
	    ("subgoal 1.2" :cases ((b1p (INST-decode-error? i))))
	    ("subgoal 1.2.1" :in-theory (enable dispatch-to-MU? lift-b-ops
						CONSISTENT-MU-RS1-P
						DQ-READY-TO-MU?
						exception-relations
						INST-EXCPT-DETECTED-P))
	    ("subgoal 1.1" :in-theory (enable dispatch-to-MU? lift-b-ops
					      CONSISTENT-MU-RS1-P
					      DQ-ready-to-MU?
					      INST-EXCPT-DETECTED-P))))

(defthm consistent-MU-RS1-p-step-INST-MU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(MU RS1))
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU RS1))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-MU-RS1-p (step-INST i MT MA sigs)
				  (MT-step MT MA sigs)
				  (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable consistent-MU-RS1-p
				     lift-b-ops
				     SELECT-MU-RS1?
				     DISPATCH-TO-MU?
				     MU-READY?
				     INST-STG-STEP-INST-MU-RS1
				     step-MU step-MU-RS1))))

(defthm consistent-MU-RS1-p-step-INST
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU RS1))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-MU-RS1-p (step-INST i MT MA sigs)
				  (MT-step MT MA sigs)
				  (MA-step MA sigs)))
  :hints (("Goal" :use ((:instance stages-reachable-to-MU-RS1)))))

(defthm consistent-MU-RS-p-step-INST
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (MU-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-MU-RS-p (step-INST i MT MA sigs)
				 (MT-step MT MA sigs)
				 (MA-step MA sigs)))
  :hints (("Goal" :in-theory (enable consistent-MU-RS-p))))

(defthm consistent-BU-RS0-p-step-INST-DQ0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(DQ 0))
		  (equal (INST-stg (step-INST i MT MA sigs)) '(BU RS0))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-BU-RS0-p (step-INST i MT MA sigs)
				  (MT-step MT MA sigs)
				  (MA-step MA sigs)))
  :hints (("Goal" :cases ((b1p (dispatch-to-BU? MA))))
	    ("subgoal 2" :in-theory (enable step-inst-dq-inst
					    step-inst-low-level-functions))
	    ("subgoal 1" :in-theory (enable consistent-BU-RS0-p
					    INST-STG-STEP-INST-IF-DISPATCH-BU
					    DQ-READY-TO-BU?
					    dispatch-inst?
					    SELECT-BU-RS0? SELECT-BU-RS1?
					    DISPATCH-TO-BU? BU-READY?
					    step-BU step-BU-RS0
					    lift-b-ops)
			 :cases ((b1p (INST-fetch-error? i))))
	    ("subgoal 1.2" :cases ((b1p (INST-decode-error? i))))
	    ("subgoal 1.2.1" :in-theory (enable dispatch-to-BU? lift-b-ops
						CONSISTENT-BU-RS0-P
						DQ-READY-TO-BU?
						exception-relations
						INST-EXCPT-DETECTED-P))
	    ("subgoal 1.1" :in-theory (enable dispatch-to-BU? lift-b-ops
					      CONSISTENT-BU-RS0-P
					      DQ-ready-to-BU?
					      INST-EXCPT-DETECTED-P))))

(defthm consistent-BU-RS0-p-step-INST-BU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(BU RS0))
		  (equal (INST-stg (step-INST i MT MA sigs)) '(BU RS0))
		  (MAETT-p MT) (MA-state-p MA)  (MA-input-p sigs))
	     (consistent-BU-RS0-p (step-INST i MT MA sigs)
				  (MT-step MT MA sigs)
				  (MA-step MA sigs)))
    :hints (("goal" :in-theory (enable consistent-BU-RS0-p
				     lift-b-ops
				     SELECT-BU-RS0?
				     DISPATCH-TO-BU?
				     BU-READY?
				     INST-STG-STEP-INST-BU-RS0
				     step-BU step-BU-RS0))))

(defthm consistent-BU-RS0-p-step-INST
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg (step-INST i MT MA sigs)) '(BU RS0))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-BU-RS0-p (step-INST i MT MA sigs)
				  (MT-step MT MA sigs)
				  (MA-step MA sigs)))
    :hints (("Goal" :use ((:instance stages-reachable-to-BU-RS0)))))

(defthm consistent-BU-RS1-p-step-INST-DQ0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(DQ 0))
		  (equal (INST-stg (step-INST i MT MA sigs)) '(BU RS1))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-BU-RS1-p (step-INST i MT MA sigs)
				  (MT-step MT MA sigs)
				  (MA-step MA sigs)))
    :hints (("Goal" :cases ((b1p (dispatch-to-BU? MA))))
	    ("subgoal 2" :in-theory (enable step-inst-dq-inst
					    step-inst-low-level-functions))
	    ("subgoal 1" :in-theory (enable consistent-BU-RS1-p
					    INST-STG-STEP-INST-IF-DISPATCH-BU
					    DQ-READY-TO-BU?
					    dispatch-inst?
					    SELECT-BU-RS0? SELECT-BU-RS1?
					    DISPATCH-TO-BU? BU-READY?
					    step-BU step-BU-RS1
					    lift-b-ops)
			 :cases ((b1p (INST-fetch-error? i))))
	    ("subgoal 1.2" :cases ((b1p (INST-decode-error? i))))
	    ("subgoal 1.2.1" :in-theory (enable dispatch-to-BU? lift-b-ops
						CONSISTENT-BU-RS1-P
						DQ-READY-TO-BU?
						exception-relations
						INST-EXCPT-DETECTED-P))
	    ("subgoal 1.1" :in-theory (enable dispatch-to-BU? lift-b-ops
					      CONSISTENT-BU-RS1-P
					      DQ-ready-to-BU?
					      INST-EXCPT-DETECTED-P))))

(defthm consistent-BU-RS1-p-step-INST-BU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(BU RS1))
		  (equal (INST-stg (step-INST i MT MA sigs)) '(BU RS1))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-BU-RS1-p (step-INST i MT MA sigs)
				  (MT-step MT MA sigs)
				  (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable consistent-BU-RS1-p
				     lift-b-ops
				     SELECT-BU-RS1?
				     DISPATCH-TO-BU?
				     BU-READY?
				     INST-STG-STEP-INST-BU-RS1
				     step-BU step-BU-RS1))))

(defthm consistent-BU-RS1-p-step-INST
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg (step-INST i MT MA sigs)) '(BU RS1))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-BU-RS1-p (step-INST i MT MA sigs)
				  (MT-step MT MA sigs)
				  (MA-step MA sigs)))
     :hints (("Goal" :use ((:instance stages-reachable-to-BU-RS1)))))

(defthm consistent-BU-RS-p-step-INST
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (BU-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-BU-RS-p (step-INST i MT MA sigs)
				 (MT-step MT MA sigs)
				 (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable consistent-BU-RS-p))))

(defthm consistent-LSU-RS0-p-step-INST-DQ0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(DQ 0))
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU RS0))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-LSU-RS0-p (step-INST i MT MA sigs)
				   (MT-step MT MA sigs)
				   (MA-step MA sigs)))
  :hints (("Goal" :cases ((b1p (dispatch-to-LSU? MA))))
	  ("subgoal 2" :in-theory (enable step-inst-dq-inst
					  DISPATCH-INST? lift-b-ops
					  step-inst-low-level-functions))
	  ("subgoal 1" :in-theory
		       (e/d  (consistent-LSU-RS0-p
			      INST-STG-STEP-INST-IF-DISPATCH-LSU
			      DQ-READY-TO-LSU?
			      dispatch-inst?
			      SELECT-LSU-RS0? SELECT-LSU-RS1?
			      DISPATCH-TO-LSU? LSU-READY?
			      step-LSU step-LSU-RS0
			      lift-b-ops)
			     (DQ-DE0-CNTLV-=-INST-CNTLV-2
			      DQ-DE0-EXCPT-=-INST-EXCPT-FLAGS-2
			      INST-SPECULTV-INST-AT-DQ0-IF-DISPATCH-INST
			      UNIQ-INST-AT-DQ0-IF-DISPATCH-INST))
		       :cases ((b1p (INST-fetch-error? i))))
	  ("subgoal 1.2" :cases ((b1p (INST-decode-error? i))))
	  ("subgoal 1.2.1" :in-theory (enable dispatch-to-LSU? lift-b-ops
					      CONSISTENT-LSU-RS0-P
					      DQ-READY-TO-LSU?
					      exception-relations
					      INST-EXCPT-DETECTED-P))
	  ("subgoal 1.1" :in-theory (enable dispatch-to-LSU? lift-b-ops
					    CONSISTENT-LSU-RS0-P
					    DQ-ready-to-LSU?
					    INST-EXCPT-DETECTED-P))))

(defthm consistent-LSU-RS0-p-step-INST-LSU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(LSU RS0))
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU RS0))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-LSU-RS0-p (step-INST i MT MA sigs)
				   (MT-step MT MA sigs)
				   (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable consistent-LSU-RS0-p
				     lift-b-ops
				     SELECT-LSU-RS0?
				     DISPATCH-TO-LSU?
				     LSU-READY?
				     INST-STG-STEP-INST-LSU-RS0
				     step-LSU step-LSU-RS0))))

(defthm consistent-LSU-RS0-p-step-INST
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU RS0))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-LSU-RS0-p (step-INST i MT MA sigs)
				   (MT-step MT MA sigs)
				   (MA-step MA sigs)))
  :Hints (("goal" :use (:instance stages-reachable-to-LSU-RS0))))

(defthm consistent-LSU-RS1-p-step-INST-DQ0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(DQ 0))
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU RS1))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-LSU-RS1-p (step-INST i MT MA sigs)
				   (MT-step MT MA sigs)
				   (MA-step MA sigs)))
  :hints (("Goal" :cases ((b1p (dispatch-to-LSU? MA))))
	  ("subgoal 2" :in-theory (enable step-inst-dq-inst
					  DISPATCH-INST? lift-b-ops
					  step-inst-low-level-functions))
	  ("subgoal 1" :in-theory
		       (e/d  (consistent-LSU-RS1-p
			      INST-STG-STEP-INST-IF-DISPATCH-LSU
			      DQ-READY-TO-LSU?
			      dispatch-inst?
			      SELECT-LSU-RS0? SELECT-LSU-RS1?
			      DISPATCH-TO-LSU? LSU-READY?
			      step-LSU step-LSU-RS1
			      lift-b-ops)
			     (DQ-DE0-CNTLV-=-INST-CNTLV-2
			      DQ-DE0-EXCPT-=-INST-EXCPT-FLAGS-2
			      INST-SPECULTV-INST-AT-DQ0-IF-DISPATCH-INST
			      UNIQ-INST-AT-DQ0-IF-DISPATCH-INST))
		       :cases ((b1p (INST-fetch-error? i))))
	  ("subgoal 1.2" :cases ((b1p (INST-decode-error? i))))
	  ("subgoal 1.2.1" :in-theory (enable dispatch-to-LSU? lift-b-ops
					      CONSISTENT-LSU-RS1-P
					      DQ-READY-TO-LSU?
					      exception-relations
					      INST-EXCPT-DETECTED-P))
	  ("subgoal 1.1" :in-theory (enable dispatch-to-LSU? lift-b-ops
					    CONSISTENT-LSU-RS1-P
					    DQ-ready-to-LSU?
					    INST-EXCPT-DETECTED-P))))

(defthm consistent-LSU-RS1-p-step-INST-LSU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg i) '(LSU RS1))
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU RS1))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-LSU-RS1-p (step-INST i MT MA sigs)
				   (MT-step MT MA sigs)
				   (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable consistent-LSU-RS1-p
				     lift-b-ops
				     SELECT-LSU-RS1?
				     DISPATCH-TO-LSU?
				     LSU-READY?
				     INST-STG-STEP-INST-LSU-RS1
				     step-LSU step-LSU-RS1))))

(defthm consistent-LSU-RS1-p-step-INST
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU RS1))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-LSU-RS1-p (step-INST i MT MA sigs)
				   (MT-step MT MA sigs)
				   (MA-step MA sigs)))
  :Hints (("goal" :use (:instance stages-reachable-to-LSU-RS1))))

(defthm consistent-LSU-RS-p-step-INST
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (LSU-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-LSU-RS-p (step-INST i MT MA sigs)
				  (MT-step MT MA sigs)
				  (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable consistent-LSU-RS-p))))

; A landmark lemma.
; A consistent-RS-entry-p is true for the instruction i in the next
; state.
(defthm consistent-RS-entry-p-step-INST
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-RS-entry-p (step-INST i MT MA sigs)
				    (MT-step MT MA sigs)
				    (MA-step MA sigs)))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p))))

(defthm trace-consistent-RS-p-step-trace
    (implies (and (inv MT MA)
		  (not (b1p (flush-all? MA sigs)))
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (trace-consistent-RS-p (step-trace trace MT MA sigs ISA spc smc)
				    (MT-step MT MA sigs)
				    (MA-step MA sigs))))

; a help lemma.
(defthm consistent-RS-entry-p-if-committed-p
    (implies (and (INST-p i) (committed-p i))
	     (consistent-RS-entry-p i MT MA))
  :hints (("Goal" :in-theory (enable consistent-RS-entry-p committed-p
				     EXECUTE-STG-P))))

(defthm trace-consistent-RS-p-step-trace-if-flush-all
    (implies (and (inv MT MA)
		  (b1p (flush-all? MA sigs))
		  (MT-all-commit-before-trace trace MT)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (trace-consistent-RS-p (step-trace trace MT MA sigs ISA spc smc)
				    (MT-step MT MA sigs)
				    (MA-step MA sigs)))
  :hints ((when-found (MT-ALL-COMMIT-BEFORE-TRACE (CDR TRACE) MT)
		      (:cases ((committed-p (car trace)))))))

;; consistent-RS-p is preserved during the MA transition.
(defthm consistent-RS-p-preserved
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-RS-p (MT-step MT MA sigs) (MA-step MA sigs)))
  :hints (("Goal" :in-theory (enable consistent-RS-p )
		  :cases ((b1p (flush-all? MA sigs))))))
