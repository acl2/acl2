;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; MI-inv.lisp
; Author  Jun Sawada, University of Texas at Austin
;
;  This book proves the weak invariant wk-inv.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "ACL2")

(include-book "MA2-lemmas")
(include-book "MAETT-lemmas")

(deflabel begin-wk-inv)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Invariant proof of MT-new-ID-distinct-p MT-distinct-IDs-p
; and MT-distinct-INST-p
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm MT-new-ID-distinct-p-init-MT
    (implies (MA-state-p MA)
	     (MT-new-ID-distinct-p (init-MT MA)))
  :hints (("Goal" :in-theory (enable init-MT MT-new-ID-distinct-p))))

(defthm ID-lt-all-p-step-trace
    (implies (ID-lt-all-p trace (MT-new-ID MT))
	     (ID-lt-all-p (step-trace trace MT MA sigs ISA spc smc)
			  (1+ (MT-new-ID MT))))
  :hints (("Goal" :in-theory (enable exintr-INST fetched-inst))))

(defthm MT-new-ID-distinct-p-MT-step
    (implies (MT-new-ID-distinct-p MT)
	     (MT-new-ID-distinct-p (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable MT-new-ID-distinct-p MT-step))))

(defthm MT-distinct-IDs-p-init-MT
    (implies (MA-state-p MA)
	     (MT-distinct-IDs-p (init-MT MA)))
  :hints (("Goal" :in-theory (enable init-MT MT-distinct-IDs-p))))

(local
(defthm not-member-eq-ID-step-trace
    (implies (and (weak-inv MT)
		  (subtrace-p trace MT)
		  (INST-in i MT)
		  (not (member-eq-ID i trace)))
	     (not (member-eq-ID (step-INST i MT MA sigs)
				(step-trace trace MT MA sigs
					    ISA spc smc))))
  :hints (("goal" :in-theory (enable exintr-INST fetched-inst)))))

(local
(defthm distinct-IDs-p-step-trace
    (implies (and (weak-inv MT)
		  (subtrace-p trace MT)
		  (distinct-IDs-p trace))
	     (distinct-IDs-p (step-trace trace MT MA sigs ISA spc smc)))))

(defthm MT-distinct-IDs-p-MT-step
    (implies (weak-inv MT)
	     (MT-distinct-IDs-p (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable MT-distinct-IDs-p MT-step
				     weak-inv))))

(defthm MT-distinct-INST-p-init-MT
    (implies (MA-state-p MA)
	     (MT-distinct-INST-p (init-MT MA)))
  :hints (("Goal" :in-theory (enable MT-distinct-INST-p init-MT))))

(local
(encapsulate nil
(local
(defthm distinct-member-p-if-distinct-IDs-p
    (implies (distinct-IDs-p trace)
	     (distinct-member-p trace))))

(defthm MT-distinct-INST-p-if-MT-distinct-IDs-p
    (implies (MT-distinct-IDs-p MT)
	     (MT-distinct-INST-p MT))
  :hints (("Goal" :in-theory (enable MT-distinct-INST-p MT-distinct-IDs-p))))
))

(defthm MT-distinct-INST-p-MT-step
    (implies (weak-inv MT)
	     (MT-distinct-INST-p (MT-step MT MA sigs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Invariant proof of ISA-step-chain-p
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm ISA-step-chain-p-init-MT
    (implies (MA-state-p MA)
	     (ISA-step-chain-p (init-MT MA)))
  :hints (("Goal" :in-theory (enable init-MT ISA-step-chain-p))))

(local
(defthm ISA-chained-trace-p-step-trace 
    (implies (ISA-chained-trace-p trace ISA)
	     (ISA-chained-trace-p (step-trace trace MT MA sigs ISA spc smc)
				  ISA))
  :hints (("goal" :in-theory (enable exintr-INST fetched-inst)))))

(defthm ISA-step-chain-p-step
    (implies (ISA-step-chain-p MT)
	     (ISA-step-chain-p (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable MT-step ISA-step-chain-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Invariant Proof of correct-modified-flgs-p
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm correct-modified-flgs-p-init-MT
    (implies (MA-state-p MA)
	     (correct-modified-flgs-p (init-MT MA)))
  :hints (("goal" :in-theory (enable correct-modified-flgs-p init-MT))))

(local
(encapsulate nil
(local
(defthm MT-modify-p-step-INST-help
    (implies (and (weak-inv MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace2 MT)
		  (INST-listp trace2)
		  (subtrace-p trace MT)
		  (tail-p trace trace2)
		  (consp trace)
		  (INST-listp trace)
		  (MA-input-p sigs)
		  (trace-no-jmp-exintr-before-trace trace trace2 MT MA sigs))
	     (equal (trace-modify-p (step-INST (car trace) MT MA sigs)
				    (step-trace trace2 MT MA sigs
						ISA spc smc))
		    (trace-modify-p (car trace) trace2)))
  :hints (("goal" :in-theory (enable INST-MODIFY-P))
	  (when-found (step-INST (CAR TRACE) MT MA SIGS)
		      (:expand ((STEP-TRACE TRACE MT MA SIGS ISA SPC SMC)))))))

(defthm MT-modify-p-step-INST
    (implies (and (weak-inv MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (consp trace)
		  (INST-listp trace)
		  (MA-input-p sigs)
		  (MT-no-jmp-exintr-before-trace trace MT MA sigs))
	     (equal (MT-modify-p (step-INST (car trace) MT MA sigs)
				 (MT-step MT MA sigs))
		    (MT-modify-p (car trace) MT)))
  :hints (("Goal" :in-theory (enable MT-modify-p MT-step
				     MT-no-jmp-exintr-before-trace
				     subtrace-p
				     INST-in)
		  :restrict ((MT-modify-p-step-INST-help
			      ((trace2 (MT-trace MT))))))))
))

(local
(encapsulate nil
(local
(defthm local-help
    (implies (and (weak-inv MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (MA-input-p sigs)
		  (trace-no-jmp-exintr-before-trace nil trace MT MA sigs))
      (equal (trace-modify-p (fetched-inst MT
					   (MT-final-ISA MT)
					   (specultv-before? nil MT)
					   (MT-self-modify? MT))
			     (step-trace trace MT MA sigs
					 (ISA-before trace MT)
					 (specultv-before? trace MT)
					 (modified-inst-before? trace MT)))
	     (not (trace-no-write-at (ISA-pc (MT-final-ISA MT)) trace))))
  :hints (("goal" :in-theory (enable INST-MODIFY-P)))))

(defthm not-MT-modify-p-if-MT-no-write-at
    (implies (and (weak-inv MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (MT-no-jmp-exintr-before-trace nil MT MA sigs))
     (equal (MT-modify-p (fetched-inst MT (MT-final-ISA MT)
				       (specultv-before? nil MT)
				       (MT-self-modify? MT))
			 (MT-step MT MA sigs))
	    (not (MT-no-write-at (ISA-pc (MT-final-ISA MT)) MT))))
  :hints (("Goal" :in-theory (enable MT-modify-p MT-no-write-at
				     MT-no-jmp-exintr-before-trace)
		  :use (:instance local-help
				  (trace (MT-trace MT))))))
))
	   

(local
(defthm trace-correct-modified-flgs-p-step-trace
    (implies (and (weak-inv MT)
		  (INST-listp trace)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (INST-listp trace)
		  (subtrace-p trace MT)
		  (MA-input-p sigs)
		  (MT-no-jmp-exintr-before-trace trace MT MA sigs)
		  (trace-correct-modified-flgs-p trace MT
					 (modified-inst-before? trace MT)))
   (trace-correct-modified-flgs-p (step-trace trace MT MA sigs
					      (ISA-before trace MT)
					      (specultv-before? trace MT)
					      (modified-inst-before? trace MT))
				     (MT-step MT MA sigs)
				     (modified-inst-before? trace MT)))
  :hints (("goal" :induct (step-trace trace MT MA sigs ISA
						   spc smc))
	  (when-pattern-found
	   (TRACE-CORRECT-modified-flgs-P (CDR TRACE) MT (@ smc))
	   (:expand ((trace-correct-modified-flgs-p trace MT
				    (modified-inst-before? trace MT)))))
	  (when-pattern-found
	   (STEP-TRACE (CDR TRACE)
		       (@ MT) (@ ma) (@ sigs)
		       (@ isa) (@ spc) (@ smc))
	   (:expand (STEP-TRACE TRACE MT MA SIGS (ISA-BEFORE TRACE MT)
				(SPECULTV-BEFORE? TRACE MT)
				(Modified-inst-BEFORE? TRACE MT)))))))

(defthm correct-modified-flgs-p-MT-step
    (implies (and (weak-inv MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs))
	     (correct-modified-flgs-p (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable weak-inv
				     correct-modified-flgs-p)
		  :USE (:INSTANCE trace-correct-modified-flgs-p-step-trace
				  (trace (MT-trace MT))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Proof of correct-modified-first-preserved
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Proof of correct-modified-first for initial states
(defthm correct-modified-first-init-MT
    (correct-modified-first (init-MT MA))
  :hints (("goal" :in-theory (enable init-MT correct-modified-first))))

;;; invariant proof
(encapsulate nil
(local
(defthm correct-modified-first-preserved-help
    (implies (and (trace-correct-modified-first trace)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA))
	     (trace-correct-modified-first (step-trace trace MT MA sigs
						       ISA spc smc)))
  :hints (("Goal" :in-theory (enable lift-b-ops)))))

(defthm correct-modified-first-preserved
    (implies (and (correct-modified-first MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (correct-modified-first (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable correct-modified-first
				     inv correct-modified-first))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Final theorems for weak-inv
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Weak invariants are true for the initial MAETT.
(defthm weak-inv-init-MT
    (implies (MA-state-p MA)
	     (weak-inv (init-MT MA)))
  :hints (("goal" :in-theory (enable weak-inv))))

; Weak invariants is held during MAETT update.
(defthm weak-inv-step
    (implies (and (weak-inv MT)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (MA-input-p sigs))
	     (weak-inv (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable weak-inv))))

(deflabel end-wk-inv)
