(in-package "ACL2")


;(include-book "utils")
(include-book "basic-def")
(include-book "model")
(include-book "table-def")
(include-book "basic-lemmas")

(deflabel begin-proof)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; In this file, we prove our correctness criterion. First we prove that
; our invariant conditions hold for all micro-architectural states
; reachable from initial states.  Then we prove the correctness of
; the criterion using the invariant.
;
; We verify two lemmas about invariant conditions: invariant-init-MT
; and invariant-step.  Lemma invariant-init-MT shows that invariant
; conditions are true for all initial states, while lemma
; invariant-step shows that conditions are invariantly held during
; the micro-architecture machine transitions.
;
; Predicate invariant is a conjunction of seven conditions,
; pc-match-p, regs-match-p, mem-match-p, ISA-chain-p,
; MT-inst-invariant, MT-contains-all-insts, and MT-in-order-p.  We
; prove that individual conditions are held at the initial states, and
; that they are preserved over the machine state transition.  For instance,
; pc-match-p-init-MT shows that condition pc-match-p is true for
; initial states.  And lemma pc-match-p-MT-step shows that pc-match-p
; is preserved during machine transitions.
;

;
;;;;;;; Proof of pc-match-p ;;;
; PC-match-p is true for initial states.
(defthm pc-match-p-init-MT
    (pc-match-p (init-MT MA) MA)
  :hints (("Goal" :in-theory (enable pc-match-p init-MT MT-pc))))

(encapsulate nil
(local
(defthm pc-match-p-MT-step-induction
    (implies (and (equal (trace-pc trace ISA) (MA-pc MA))
		  (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (trace-pc (step-trace trace MA sig ISA) ISA)
		    (step-pc MA sig)))
  :hints (("Goal" :in-theory (enable STEP-PC ISA-STEP
				     ISA-add ISA-sub ISA-default)
		  :expand (TRACE-PC (LIST (NEW-INST ISA))
					    ISA)))))
; PC-match-p is preserved during MA state transitions.
(defthm pc-match-p-MT-step
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (pc-match-p (MT-step MT MA sig) (MA-step MA sig)))
  :hints (("Goal" :in-theory (enable pc-match-p MT-step MA-step
				     invariant MT-pc))))
)

;;;;;;; Proof of regs-match-p
; Register file is in the correct state in the initial states.
(defthm regs-match-p-init-MT
    (regs-match-p (init-MT MA) MA)
  :hints (("Goal" :in-theory (enable init-MT regs-match-p MT-regs))))

(encapsulate nil
(local
(defthm INST-pre-ISA-INST-at-latch2-induction
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (trace-INST-at 'latch2 trace))
	     (equal (ISA-regs (INST-pre-ISA (trace-INST-at 'latch2 trace)))
		    (trace-regs trace (INST-pre-ISA (car trace)))))
  :hints (("subgoal *1/3" :cases ((consp (cdr trace))))
	  ("subgoal *1/2" :use (:instance stages-of-inst (i (car trace)))))))


(local
(defthm INST-pre-ISA-INST-at-latch2-help
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-at 'latch2 MT))
	     (equal (ISA-regs (INST-pre-ISA (INST-at 'latch2 MT)))
		    (MT-regs MT)))
  :hints (("Goal" :in-theory (enable MT-regs INST-at)
		  :cases ((consp (MT-trace MT)))))
  :rule-classes nil))


; If an instruction I is in stage latch2, the register file of the MA
; state looks like the register file in the pre-ISA state  I.  This is
; because the register file reflects the result of all
; retired instructions, while the result of partially executed
; instructions are not written in the register file.
(defthm INST-pre-ISA-INST-at-latch2
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-at 'latch2 MT))
	     (equal (ISA-regs (INST-pre-ISA (INST-at 'latch2 MT)))
		    (MA-regs MA)))
  :hints (("Goal" :in-theory (enable invariant regs-match-p)
		  :use (:instance INST-pre-ISA-INST-at-latch2-help))))
)

(encapsulate nil
(local
(defthm MT-regs-MT-step-if-latch2-valid-help-help
    (implies (and (INST-listp trace)
		  (not (trace-INST-at 'latch2 trace))
		  (not (trace-INST-at 'retire trace)))
	     (equal (trace-regs (step-trace trace MA sig ISA) ISA)
		    (ISA-regs ISA)))
  :hints (("Goal" :cases ((consp trace))))))


(local
(defthm MT-regs-MT-step-if-latch2-valid-help
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (trace-INST-at 'latch2 trace))
	     (equal (trace-regs (step-trace trace MA sig ISA) ISA)
		    (ISA-regs (INST-post-ISA (trace-INST-at 'latch2 trace)))))
  :hints (("Subgoal *1/6" :use (:instance stages-of-inst (i (car trace)))))))


; The correct register file state for the next cycle is defined here.
; If instruction I is at latch2, I retires in this cycle and the
; effect of I appears in the register file.
(defthm MT-regs-MT-step-if-latch2-valid
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-at 'latch2 MT))
	     (equal (MT-regs (MT-step MT MA sig))
		    (ISA-regs (INST-post-ISA (INST-at 'latch2 MT)))))
  :hints (("Goal" :in-theory (enable MT-regs INST-at MT-step))))
)

; The effect of ISA execution of instruction I is described by this
; lemma.  If instruction is add (0) or sub (1), the destination register
; will contain the result of the instruction.  If the instruction
; is a NOP, the register file is unchanged.
(defthm ISA-regs-INST-post-ISA
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i))
	     (equal (ISA-regs (ISA-step (INST-pre-ISA i)))
		    (if (or (equal (INST-op i) 0) (equal (INST-op i) 1))
			(write-reg (INST-result i) (INST-rc i)
				   (ISA-regs (INST-pre-ISA i)))
			(ISA-regs (INST-pre-ISA i)))))
  :hints (("Goal" :in-theory (enable ISA-step ISA-add ISA-sub ISA-default
				     INST-attrb ALU-output))))
(in-theory (disable ISA-regs-INST-post-ISA))


(encapsulate nil
(local
(defthm MT-regs-MT-step-induction
    (implies (and (INST-listp trace) (not (trace-INST-at 'latch2 trace)))
	     (equal (trace-regs (step-trace trace MA sig ISA) ISA)
		    (trace-regs trace ISA)))
  :hints (("Goal" :expand (TRACE-REGS (CONS (STEP-INST (CAR TRACE) MA)
                            (STEP-TRACE (CDR TRACE)
                                        MA SIG (INST-POST-ISA (CAR TRACE))))
                      ISA)))))


; If there is no instruction at latch2, the register file in MA is not
; updated in this cycle.  Correct register file states calculated from the
; MAETT does not change.
(defthm MT-regs-MT-step
    (implies (and (MAETT-p MT) (not (INST-at 'latch2 MT)))
	     (equal (MT-regs (MT-step MT MA sig))
		    (MT-regs MT)))
  :hints (("Goal" :in-theory (enable MT-regs MT-step
				     INST-at))))
)

(encapsulate nil
; This is a help lemma.
(local
(defthm MT-regs-MA-regs
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (equal (MT-regs MT) (MA-regs MA)) t))
  :hints (("Goal" :in-theory (enable invariant regs-match-p)))))


; Finally, we prove that predicate regs-match-p is preserved during MA
; machine cycles.  Predicate regs-match-p holds after one MA  machine cycle
; of execution.
(defthm regs-match-p-MT-step
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (regs-match-p (MT-step MT MA sig) (MA-step MA sig)))
  :hints (("Goal" :in-theory (enable regs-match-p MA-step step-regs
				     ISA-regs-INST-post-ISA
				     lift-b-ops bv-eqv-iff-equal
				     INST-result)
		  :cases ((b1p (latch2-valid? (MA-latch2 MA)))))))
)

;;;;;;; Proof of mem-match-p
; Predicate mem-match-p is true for the initial states.
(defthm mem-match-p-init-MT
    (mem-match-p (init-MT MA) MA)
  :hints (("Goal" :in-theory (enable mem-match-p))))

; Predicate mem-match-p is preserved during MA machines state transitions.
(defthm mem-match-p-MT-step
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (mem-match-p (MT-step MT MA sig) (MA-step MA sig)))
  :hints (("Goal" :in-theory (enable mem-match-p MA-STEP
				     invariant))))

;;;;;;; Proof of ISA-chain-p
; ISA-chain-p is true for initial tables.
(defthm ISA-chain-p-init-MT
    (ISA-chain-p (init-MT MA))
  :hints (("Goal" :in-theory (enable ISA-chain-p init-MT))))

(encapsulate nil
(local
(defthm ISA-chain-p-step-MT-induction
    (implies (and (INST-listp trace) (ISA-chain-trace-p trace ISA))
	     (ISA-chain-trace-p (step-trace trace MA sig ISA) ISA))))

; And it is also preserved during MAETT updates.
(defthm ISA-chain-p-step-MT
    (implies (and (invariant MT MA)
		  (MAETT-p MT))
	     (ISA-chain-p (MT-step MT MA sig)))
  :hints (("Goal" :in-theory (enable ISA-chain-p MT-step invariant
				     MAETT-p))))
)

;;;;;; MT-inst-invariant

; MT-inst-invariant are true for initial states.
(defthm MT-inst-invariant-init-MT
    (MT-inst-invariant (init-MT MA) MA)
  :hints (("Goal" :in-theory (enable MT-inst-invariant init-MT
				     trace-INST-invariant))))


; Proof of MT-inst-invariant-MT-step.
;
; MT-inst-invariant checks recursively every instruction in the MAETT
; satisfies predicate inst-invariant.  Predicate inst-invariant
; represents the conditions that each instructions should satisfy,
; depending on the current stage.
; We prove that every instruction invariantly satisfy inst-invariant,
; and then prove the lemma MT-inst-invariant-MT-step using induction.
;
; The check for individual instructions needs to consider two cases:
; the case in which the instruction is a newly fetched instruction,
; and the case in which the instruction is in the current MAETT.  The
; first case is proven as lemma inst-invariant-new-INST, and the
; second case as INST-invariant-step-INST.
;

; Inst-invariant-new-INST shows that inst-invariant is true for
; the instruction entry (new-INST (ISA-before nil MT)), which
; represents the newly fetched instruction.
(defthm inst-invariant-new-INST
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (fetch-inst? MA sig)))
	     (inst-invariant (new-INST (ISA-before nil MT))
			      (MA-step MA sig)))
  :hints (("Goal" :in-theory (enable new-INST inst-invariant
				     INST-LATCH1-INV fetch-inst?
				     stall-cond?
				     MA-STEP step-latch1 lift-b-ops
				     INST-attrb))))


; From here, we prove lemma INST-invariant-step-INST, which asserts
; that an instruction satisfies inst-invariant at the next machine
; cycle.

; Read-reg-ISA-step-if-target-reg-differs proves the fact that
; the value of register is not updated by an instruction whose destination
; register is different.
; (INST-rc i) represents the destination register for the instruction
; i. Suppose register (INST-rc i) differs from register rix.  Then
; ISA execution of instruction i does not update register rix, and the
; value of register rix is unchanged.
(defthm read-reg-ISA-step-if-target-reg-differs
    (implies (and (INST-p i) (rname-p rix) (not (equal (INST-rc i) rix)))
	     (equal (read-reg rix (ISA-regs (ISA-step (INST-pre-ISA i))))
		    (read-reg rix (ISA-regs (INST-pre-ISA i)))))
  :hints (("Goal" :in-theory (enable ISA-step ISA-add ISA-sub ISA-default
				     INST-attrb))))

; This lemmas assures that the pipeline interlock is working
; correctly.
; Briefly speaking, the fact that (dependency? MA) is off implies that
; instruction i at latch1 and instruction (car trace) at latch2 have
; no true (RAW) dependencies.  Therefore, execution of instruction
; (car trace) does not change the register (INST-ra i), which is a
; source register of instruction i.  As a result, we don't have to
; stall the instruction i.
;
; Note: trace is a subtrace of the current MAETT MT.  We consider the
; interlocks between instructions represented by (car trace) and i.
; This is one of the easiest ways to represent the lemma
; without a fully developed supporting theory, although the resulting
; lemma is not beautifully formulated.
(defthm read-regs-latch1-INST-ra-special-case
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (consp trace)
		  (equal (INST-stg (car trace)) 'latch2)
		  (member-equal i (cdr trace))
		  (equal (INST-stg i) 'latch1)
		  (not (b1p (dependency? MA))))
	     (equal (read-reg (INST-ra i)
			      (ISA-regs (INST-pre-ISA (car trace))))
		    (read-reg (INST-ra i)
			      (ISA-regs (INST-pre-ISA i)))))
  :hints (("Goal" :cases ((consp (cdr trace))))
	  ("Subgoal 1" :cases ((equal (cadr trace) i)))
	  ("Subgoal 1.1" :in-theory (enable dependency? lift-b-ops)
			 :restrict
			 ((latch2-rc-INST-rc-if-INST-in ((i (car trace))))
			  (latch1-ra-INST-ra-if-INST-in ((i (cadr trace))))))))

; Similar lemma for source register (INST-rb i).
(defthm read-regs-latch1-INST-rb-special-case
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (consp trace)
		  (equal (INST-stg (car trace)) 'latch2)
		  (member-equal i (cdr trace))
		  (equal (INST-stg i) 'latch1)
		  (not (b1p (dependency? MA))))
	     (equal (read-reg (INST-rb i)
			      (ISA-regs (INST-pre-ISA (car trace))))
		    (read-reg (INST-rb i)
			      (ISA-regs (INST-pre-ISA i)))))
  :hints (("Goal" :cases ((consp (cdr trace))))
	  ("Subgoal 1" :cases ((equal (cadr trace) i)))
	  ("Subgoal 1.1" :in-theory (enable DEPENDENCY? lift-b-ops)
			 :restrict
			 ((latch2-rc-INST-rc-if-INST-in ((i (car trace))))
			  (latch1-rb-INST-rb-if-INST-in ((i (cadr trace))))))))

(encapsulate nil
(local
(defthm read-regs-latch1-INST-ra-if-not-stall-cond-help
   (implies (and (invariant MT MA)
		 (MAETT-p MT) (MA-state-p MA)
		 (subtrace-p trace MT)
		 (INST-listp trace)
		 (member-equal i trace) (INST-p i)
		 (equal (INST-stg i) 'latch1)
		 (not (b1p (dependency? MA))))
	    (equal (read-reg (INST-ra I)
			     (trace-regs trace (ISA-before trace MT)))
		   (read-reg (INST-ra I) (ISA-regs (INST-pre-ISA I)))))
  :hints (("Goal" :in-theory (enable ISA-before-INST-pre-ISA-car))
	  ("subgoal *1/2" :use (:instance stages-of-INST (i (car trace)))))
  :rule-classes nil))

; Suppose instruction i is at latch1, and (dependency? MA) is off.  It
; means there is no instruction at latch2 which updates i's source register
; (INST-ra i).  This lemma proves that the register (INST-ra i) in the MA
; state contains the correct source value for instruction i.
(defthm read-regs-latch1-INST-ra-if-not-stall-cond
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) 'latch1)
		  (not (b1p (dependency? MA))))
	     (equal (read-reg (INST-ra I) (MA-regs MA))
		    (read-reg (INST-ra I) (ISA-regs (INST-pre-ISA I)))))
  :hints (("Goal"
	   :use
	   (:instance read-regs-latch1-INST-ra-if-not-stall-cond-help
		      (trace (MT-trace MT)))
	   :in-theory (enable invariant regs-match-p INST-in
			      MT-REGS))))
)

(encapsulate nil
(local
(defthm read-regs-latch1-INST-rb-if-not-stall-cond-help
   (implies (and (invariant MT MA)
		 (MAETT-p MT) (MA-state-p MA)
		 (subtrace-p trace MT)
		 (INST-listp trace)
		 (member-equal i trace) (INST-p i)
		 (equal (INST-stg i) 'latch1)
		 (not (b1p (dependency? MA))))
	    (equal (read-reg (INST-rb I)
			     (trace-regs trace (ISA-before trace MT)))
		   (read-reg (INST-rb I) (ISA-regs (INST-pre-ISA I)))))
  :hints (("Goal" :in-theory (enable ISA-before-INST-pre-ISA-car))
	  ("subgoal *1/2" :use (:instance stages-of-INST (i (car trace)))))
  :rule-classes nil))

; Similar lemma for RB.
(defthm read-regs-latch1-INST-rb-if-not-stall-cond
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) 'latch1)
		  (not (b1p (dependency? MA))))
	     (equal (read-reg (INST-rb I) (MA-regs MA))
		    (read-reg (INST-rb I) (ISA-regs (INST-pre-ISA I)))))
    :hints (("Goal"
	   :use
	   (:instance read-regs-latch1-INST-rb-if-not-stall-cond-help
		      (trace (MT-trace MT)))
	   :in-theory (enable invariant regs-match-p INST-in
			      MT-REGS))))
)

(encapsulate nil
(local
(defthm ISA-regs-MA-regs-if-not-latch2-valid-induction
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (member-equal i trace)
		  (equal (INST-stg i) 'latch1)
		  (not (b1p (latch2-valid? (MA-latch2 MA)))))
	     (equal (ISA-regs (INST-pre-ISA I))
		    (trace-regs trace (ISA-before trace MT))))
  :hints (("goal" :in-theory (enable ISA-BEFORE-INST-PRE-ISA-CAR)
		  :restrict ((LATCH2-VALID-IF-INST-IN ((i (car trace))))))
	  ("subgoal *1/2" :use ((:instance stages-of-inst (I (car trace))))))
  :rule-classes nil))

;
; If instruction i is at latch1 and no instruction is at latch2, i is the
; only instruction in the pipeline, and i has not updated the register file
; in the MA. So, the register file in the MA state is the same as in pre-ISA
; of i.
(defthm ISA-regs-MA-regs-if-not-latch2-valid
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) 'latch1)
		  (not (b1p (latch2-valid? (MA-latch2 MA)))))
	     (equal (ISA-regs (INST-pre-ISA I)) (MA-regs MA)))
  :hints (("goal" :in-theory (enable invariant regs-match-p
				     MT-REGS INST-in)
		  :use (:instance
			ISA-regs-MA-regs-if-not-latch2-valid-induction
			(trace (MT-trace MT))))))
)

(encapsulate nil
(local
(defthm INST-latch1-inv-step-INST-help
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) 'latch1)
		  (equal (INST-stg (step-INST i MA)) 'latch1))
	     (inst-latch1-inv (step-INST i MA) (MA-step MA sig)))
  :hints (("Goal" :use (:instance INST-invariant-INST-in)
		  :in-theory (enable INST-invariant INST-latch1-inv
				     MA-step step-latch1 lift-b-ops
				     STEP-INST step-latch1-inst)))))


; Instruction i will satisfy predicate inst-latch1-inv in the next
; machine cycle, if its stage will be latch1.
(defthm INST-latch1-inv-step-INST
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg (step-INST i MA)) 'latch1))
	     (inst-latch1-inv (step-INST i MA) (MA-step MA sig)))
  :hints (("Goal" :use ((:instance stages-of-inst)))))
)


(encapsulate nil
(local
(defthm INST-latch2-inv-step-INST-help
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) 'latch1)
		  (equal (INST-stg (step-INST i MA)) 'latch2))
	     (inst-latch2-inv (step-INST i MA) (MA-step MA sig)))
  :hints (("Goal" :use (:instance INST-invariant-INST-in)
		  :in-theory (enable INST-invariant INST-latch2-inv
				     STALL-COND?
				     INST-latch1-inv INST-RA-VAL INST-RB-VAL
				     MA-step step-latch2 lift-b-ops)))))

; Similarly, instruction i satisfies inst-latch2-inv in the next
; machine cycle if it will be in the stage latch2.
(defthm INST-latch2-inv-step-INST
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg (step-INST i MA)) 'latch2))
	     (inst-latch2-inv (step-INST i MA) (MA-step MA sig)))
  :hints (("Goal" :use ((:instance stages-of-inst)))))
)


; Instruction i will satisfy predicate INST-invariant in the next
; machine cycle.
(defthm INST-invariant-step-INST
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i))
	     (inst-invariant (step-INST i MA) (MA-step MA sig)))
  :hints (("Goal" :in-theory (enable inst-invariant))))


(encapsulate nil
(local
(defthm MT-init-invariant-MT-step-induction
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT) (INST-listp trace))
	     (trace-inst-invariant (step-trace trace MA sig
						(ISA-before trace MT))
				    (MA-step MA sig)))
  :rule-classes nil))

; MT-init-invariant is true for the next machine state.
; With induction, we prove that MT-inst-invariant is true for the
; next MA state and the update table.
(defthm MT-init-invariant-MT-step
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (MT-inst-invariant (MT-step MT MA sig)
				 (MA-step MA sig)))
  :hints (("Goal" :in-theory (enable MT-inst-invariant MT-step)
		  :use (:instance MT-init-invariant-MT-step-induction
				  (trace (MT-trace MT))))))
)

; MT-contains-all-insts is correct for initial states.
(defthm MT-contains-all-insts-init-MT
    (implies (b1p (flushed? MA))
	     (MT-contains-all-insts (init-MT MA) MA))
  :hints (("Goal" :in-theory (enable MT-contains-all-insts flushed?
				     lift-b-ops))))

; Proof of MT-contains-all-insts-MT-step.
; A MAETT represents all instructions currently in the pipeline, as
; well as those retired.  If flag latch1-valid? is on, there must be
; an instruction at latch1.  Similarly, there must be an instruction
; at latch2 if latch2-valid? is on.  We prove them one by one.
(encapsulate nil
(local
(defthm INST-at-latch1-MT-step-if-fetch-inst-induction
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (fetch-inst? MA sig)))
	     (trace-INST-at 'latch1 (step-trace trace MA sig ISA)))))


; INST-at-latch1-MT-step is proven by case analysis.  In one case,
; fetch-inst? is on.  In other case, dependency? is on.  (They are
; exclusive.)  INST-at-latch1-MT-step-if-fetch-inst and
; INST-at-latch1-MT-step-if-stall-cond covers the two cases, respectively.
(defthm INST-at-latch1-MT-step-if-fetch-inst
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (fetch-inst? MA sig)))
	     (INST-at 'latch1 (MT-step MT MA sig)))
  :hints (("Goal" :in-theory (enable MT-step INST-at))))
)

(encapsulate nil
(local
(defthm INST-at-latch1-MT-step-if-stall-cond-induction
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (stall-cond? MA))
		  (trace-INST-at 'latch1 trace))
	     (trace-INST-at 'latch1 (step-trace trace MA sig ISA)))))

(defthm INST-at-latch1-MT-step-if-stall-cond
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (stall-cond? MA))
		  (b1p (latch1-valid? (MA-latch1 MA))))
	     (INST-at 'latch1 (MT-step MT MA sig)))
  :hints (("Goal" :in-theory (e/d (INST-at MT-step)
				  (INST-AT-LATCH1-IF-LATCH1-VALID))
		  :use (:instance INST-AT-LATCH1-IF-LATCH1-VALID))))
)

; If latch1-valid? is on for the next MA state, the updated MAETT
; contains an entry representing the instruction at latch1.
(defthm INST-at-latch1-MT-step
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (latch1-valid? (step-latch1 MA sig))))
	     (INST-at 'latch1 (MT-step MT MA sig)))
  :hints (("Goal" :cases ((b1p (fetch-inst? MA sig))))
	  ("subgoal 2" :in-theory (enable step-latch1 lift-b-ops
					  stall-cond? fetch-inst?))))

(encapsulate nil
(local
(defthm INST-at-latch2-MT-step-induction
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (not (b1p (dependency? MA)))
		      (not (b1p (latch2-valid? (MA-latch2 MA)))))
		  (trace-INST-at 'latch1 trace))
	     (trace-INST-at 'latch2 (step-trace trace MA sig ISA)))
  :hints (("Goal" :in-theory (enable step-latch2 lift-b-ops STALL-COND?)))))

; Similarly for latch2.
(defthm INST-at-latch2-MT-step
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (latch2-valid? (step-latch2 MA))))
	     (INST-at 'latch2 (MT-step MT MA sig)))
  :hints (("Goal" :in-theory (e/d (step-latch2 lift-b-ops INST-at MT-step
)
				  (INST-AT-LATCH1-IF-LATCH1-VALID))
		  :use (:instance INST-AT-LATCH1-IF-LATCH1-VALID))))
)

; MT-contains-all-insts is true for the next machine state.
(defthm MT-contains-all-insts-MT-step
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (MT-contains-all-insts (MT-step MT MA sig)
				    (MA-step MA sig)))
  :hints (("Goal" :in-theory (enable MT-contains-all-insts MA-step))))

;;;;;; Proof of MT-in-order-p
;
; MT-in-order-p is true for initial case.
(defthm MT-in-order-p-init-MT
    (MT-in-order-p (init-MT MA))
  :hints (("Goal" :in-theory (enable init-MT MT-in-order-p))))


; Instruction at latch1 is the last fetched instruction in the
; pipeline.  MAETT records fetched and executed instructions in ISA
; execution order, so the entry representing the instruction at latch1
; is the last in a MAETT.
(defthm endp-step-trace-cdr-if-step-INST-latch1
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (consp trace)
		  (equal (INST-stg (step-INST (car trace) MA)) 'latch1))
	     (not (consp (step-trace (cdr trace) MA sig ISA))))
  :hints (("Goal" :use ((:instance stages-of-inst (i (car trace)))
			(:instance no-inst-after-INST-latch1)
			(:instance latch1-valid-if-INST-in (i (car trace))))
		  :in-theory (enable fetch-inst? stall-cond? lift-b-ops))))


; There cannot be more than two entries of MAETT representing an
; instruction at latch2.
(defthm not-trace-INST-at-latch2-step-trace
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (consp trace)
		  (INST-listp trace)
		  (equal (INST-stg (step-INST (car trace) MA)) 'latch2))
	     (not (trace-INST-at 'latch2 (step-trace (cdr trace) MA sig ISA))))
  :hints (("Goal" :use ((:instance stages-of-inst (i (car trace)))
			(:instance no-inst-after-INST-latch1)))))


; Instructions retire in order.  So no retired instruction follows
; an instruction at latch2.
(defthm not-trace-INST-at-retire-step-trace
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (consp trace)
		  (INST-listp trace)
		  (equal (INST-stg (step-INST (car trace) MA)) 'latch2))
	     (not (trace-INST-at 'retire (step-trace (cdr trace) MA sig ISA))))
  :hints (("Goal" :use ((:instance stages-of-inst (i (car trace)))
			(:instance no-inst-after-INST-latch1)))))


(encapsulate nil
(local
(defthm MT-in-order-p-MT-step-induction
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace))
	     (trace-in-order-p (step-trace trace MA sig ISA)))))

; MT-in-order-p is true for the next machine state.
(defthm MT-in-order-p-MT-step
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (MT-in-order-p (MT-step MT MA sig)))
  :hints (("Goal" :in-theory (enable MT-step MT-in-order-p))))
)

;;;;;;;; Proof of invariant
; Invariant are true for the initial MA state and its MAETT.
(defthm invariant-init-MT
    (implies (and (MA-state-p MA) (b1p (flushed? MA)))
	     (invariant (init-MT MA) MA))
  :hints (("Goal" :in-theory (enable invariant))))

; Predicate Invariant is actually an invariant condition.
(defthm invariant-step
    (implies (and (invariant MT MA) (MAETT-p MT) (MA-state-p MA)
		  (MA-sig-p sig))
	     (invariant (MT-step MT MA sig)
			 (MA-step MA sig)))
  :Hints (("Goal" :in-theory (enable invariant))))

; By induction, invariant is correct after n cycles of MA
; execution.
(defthm invariant-stepn
    (implies (and (invariant MT MA) (MAETT-p MT) (MA-state-p MA)
		  (MA-sig-listp sig-list)
		  (<= n (len sig-list)))
	     (invariant (MT-stepn MT MA sig-list n)
			 (MA-stepn MA sig-list n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Proof of the correctness criterion.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The number of instructions recorded in the MAETT.  This is the
; number of fetched instructions since the initial machine state.
(defun MT-num-insts (MT) (len (MT-trace MT)))

; The number of instructions fetched and executed during the n cycles
; of machine execution from the initial state MA with input signal list
; sig-list.
(defun num-insts (MA sig-list n)
  (MT-num-insts (MT-stepn (init-MT MA) MA sig-list n)))

(defthm integerp-MT-num-insts (integerp (MT-num-insts MT)))

(defthm integerp-num-insts (integerp (num-insts MA sig-list n)))

(in-theory (disable MT-num-insts num-insts))

(defun trace-all-retired (trace)
  (if (endp trace)
      t
      (and (equal (INST-stg (car trace)) 'retire)
	   (trace-all-retired (cdr trace)))))

; (MT-all-retires MT) is true if all instructions recorded by MT is
; retired.
(defun MT-all-retired (MT)
    (trace-all-retired (MT-trace MT)))

(encapsulate nil
(local
(defthm flushed-implies-MT-all-retired-help
    (implies (and (INST-listp trace)
		  (trace-inst-invariant trace MA)
		  (b1p (flushed? MA)))
	     (trace-all-retired trace))
  :hints (("goal" :in-theory (enable flushed? lift-b-ops INST-p stage-p
				     inst-invariant INST-latch1-inv
				     INST-latch2-inv)))))

; If a MA state, MA, is flushed, the corresponding MAETT, MT, contains
; only retired instructions.
(defthm flushed-implies-MT-all-retired
    (implies (and (invariant MT MA)
		  (MAETT-p MT)
		  (b1p (flushed? MA)))
	     (MT-all-retired MT))
  :hints (("goal" :in-theory (enable MT-all-retired invariant
				     MT-inst-invariant))))
)

; ; A help lemma
(defthm ISA-extensionality
    (implies (and (ISA-state-p ISA1)
		  (ISA-state-p ISA2)
		  (equal (ISA-pc ISA1) (ISA-pc ISA2))
		  (equal (ISA-regs ISA1) (ISA-regs ISA2))
		  (equal (ISA-mem ISA1) (ISA-mem ISA2)))
	     (equal ISA1 ISA2))
  :rule-classes nil)

; Lemma flushed-MA-=-MT-final-ISA is proven by showing the equivalence
; of LHS and RHS with respect to each programmer visible components such
; as program counter, register file and memory.
(encapsulate nil
(local
(defthm ISA-pc-ISA-stepn-if-flushed-induction
    (implies (ISA-chain-trace-p trace ISA)
	     (equal (ISA-pc (ISA-stepn ISA (len trace)))
		    (trace-pc trace ISA)))))

(local
(defthm ISA-pc-ISA-stepn-if-flushed-help
    (implies (invariant MT MA)
	     (equal (ISA-pc (ISA-stepn (MT-init-ISA MT) (MT-num-insts MT)))
		    (MT-pc MT)))
  :hints (("Goal" :in-theory (enable MT-pc MT-num-insts
				     invariant ISA-chain-p)))))


; Equivalence with respect to PC.
(defthm ISA-pc-ISA-stepn-if-flushed
    (implies (and (invariant MT MA)
		  (MT-all-retired MT))
	     (equal (ISA-pc (ISA-stepn (MT-init-ISA MT) (MT-num-insts MT)))
		    (MA-pc MA)))
  :hints (("Goal" :in-theory (enable invariant pc-match-p)
		  :restrict ((ISA-pc-ISA-stepn-if-flushed-help
			      ((MT MT) (MA MA)))))))
)

(encapsulate nil
(local
 (defthm ISA-regs-ISA-stepn-if-flushed-induction
     (implies (and (ISA-chain-trace-p trace ISA)
		   (trace-all-retired trace))
	      (equal (ISA-regs (ISA-stepn ISA (len trace)))
		     (trace-regs trace ISA)))))
(local
(defthm ISA-regs-ISA-stepn-if-flushed-help
    (implies (and (invariant MT MA) (MT-all-retired MT))
	     (equal (ISA-regs (ISA-stepn (MT-init-ISA MT) (MT-num-insts MT)))
		    (MT-regs MT)))
  :hints (("goal" :in-theory (enable MT-init-ISA MT-all-retired
				     MT-num-insts MT-regs
				     invariant ISA-chain-p)))))

; Equivalence with respect to the register file.
(defthm ISA-regs-ISA-stepn-if-flushed
    (implies (and (invariant MT MA)
		  (MT-all-retired MT))
	     (equal (ISA-regs (ISA-stepn (MT-init-ISA MT) (MT-num-insts MT)))
		    (MA-regs MA)))
  :hints (("Goal" :in-theory (enable invariant regs-match-p)
		  :restrict ((ISA-regs-ISA-stepn-if-flushed-help
			      ((MT MT) (MA MA)))))))
)

; Equivalence with respect to the memory.
(defthm ISA-mem-MT-init-ISA-=-MA-mem
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (ISA-mem (MT-init-ISA MT)) (MA-mem MA)))
  :hints (("Goal" :in-theory (enable invariant mem-match-p))))

; One step before the final lemma.  Consider a flushed micro-state MA
; and its MAETT.  MAETT contains (MT-num-INST MT) instruction
; entries.  (MT-init-ISA MT) is the initial ISA state before executing
; the first instruction recorded in MAETT.  Therefore,
; (ISA-stepn (MT-init-ISA MT) (MT-num-insts MT)) is the final ISA state
; after executing all instructions recorded in MT.  Our invariant
; guarantees that the projection of MA to an ISA state is equal to
; this final ISA state.
(defthm flushed-MA-=-MT-final-ISA
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (flushed? MA)))
	     (equal (ISA-stepn (MT-init-ISA MT) (MT-num-insts MT))
		    (proj MA)))
  :hints (("Goal" :in-theory (enable proj)
		  :use
		  (:instance ISA-extensionality
		     (ISA1 (ISA-stepn (MT-init-ISA MT) (MT-num-insts MT)))
		     (ISA2 (proj MA)))))
  :rule-classes nil)

;  Correctness diagram.
(defthm commutative-diagram
    (implies (and (MA-state-p MA)
		  (MA-sig-listp sig-list)
		  (<= n (len sig-list))
		  (b1p (flushed? MA))
		  (b1p (flushed? (MA-stepn MA sig-list n))))
	     (equal (proj (MA-stepn MA sig-list n))
		    (ISA-stepn (proj MA)
			       (num-insts MA sig-list n))))
  :hints (("Goal" :use (:instance flushed-MA-=-MT-final-ISA
				  (MT (MT-stepn (init-MT MA) MA sig-list n))
				  (MA (MA-stepn MA sig-list n)))
		  :in-theory (enable num-insts))))

; Define the weight of an MA state.
(defun MA-weight (MA)
  (+ (if (b1p (latch1-valid? (MA-latch1 MA))) 2 0)
     (if (b1p (latch2-valid? (MA-latch2 MA))) 1 0)))

; The weight decreases unless MA is flushed.
(defthm MA-weight-MT-step
    (implies (not (b1p (flushed? MA)))
	     (< (MA-weight (MA-step MA 0)) (MA-weight MA)))
  :hints (("Goal" :in-theory (enable flushed? lift-b-ops b1p-b-and
				     MA-step step-latch1 b-and b-nand
				     step-latch2
				     stall-cond?))))

(in-theory (disable MA-weight))

; The number of the cycles to flush the pipeline.
(defun flush-cycles (MA)
  (declare (xargs :measure (MA-weight MA)))
  (if (b1p (flushed? MA))
      0
      (1+ (flush-cycles (MA-step MA 0)))))

; Generate a list of 0 with length n.
(defun zeros (n)
  (if (zp n) nil (cons 0 (zeros (1- n)))))

; The MA state after (flush-cycles MA) cycles of MA execution with
; sig-list 0's is flushed.
(defthm liveness
    (implies (MA-state-p MA)
	     (b1p (flushed? (MA-stepn MA
				      (zeros (flush-cycles MA))
				      (flush-cycles MA))))))
