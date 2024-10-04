;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; MI-inv.lisp
; Author  Jun Sawada, University of Texas at Austin
;
;  This book proves the invariant properties no-stage-conflict and
;  no-tag-conflict.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "ACL2")

(include-book "MA2-lemmas")
(include-book "MAETT-lemmas")

(deflabel begin-uniq-inv)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Proof of no-stage-conflict
; Prove that no instruction are in the same pipeline latch. 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; index
; no-stage-conflict-init-MT
;   no-IFU-stg-conflict-preserved
;   no-DQ-stg-conflict-preserved
;     uniq-inst-at-DE0-mt-step
;     no-inst-at-DE0-mt-step
;     uniq-inst-at-DE1-mt-step
;     no-inst-at-DE1-mt-step
;     uniq-inst-at-DE2-mt-step
;     no-inst-at-DE2-mt-step
;     uniq-inst-at-DE3-mt-step
;     no-inst-at-DE3-mt-step
;   no-IU-stg-conflict
;     uniq-inst-at-IU-RS0-MT-step
;     no-inst-at-IU-RS0-MT-step
;     uniq-inst-at-IU-RS1-MT-step
;     no-inst-at-IU-RS1-MT-step
;   no-BU-stg-conflict-preserved
;     uniq-inst-at-BU-RS0-MT-step
;     no-inst-at-BU-RS0-MT-step
;     uniq-inst-at-BU-RS1-MT-step
;     no-inst-at-BU-RS1-MT-step
;   no-MU-stg-conflict-preserved
;     uniq-INST-at-MU-RS0-MT-step
;     no-INST-at-MU-RS0-MT-step
;     uniq-INST-at-MU-RS1-MT-step
;     no-INST-at-MU-RS1-MT-step
;     uniq-INST-at-MU-lch1-MT-step
;     no-INST-at-MU-lch1-MT-step
;     uniq-INST-at-MU-lch2-MT-step
;     no-INST-at-MU-lch2-MT-step
;   no-LSU-stg-conflict-preserved
;     uniq-inst-at-LSU-RS0-MT-step
;     no-inst-at-LSU-RS0-MT-step
;     uniq-inst-at-LSU-RS1-MT-step
;     no-inst-at-LSU-RS1-MT-step
;     uniq-inst-at-LSU-rbuf-MT-step
;     no-inst-at-LSU-rbuf-MT-step
;     uniq-inst-at-LSU-wbuf0-MT-step
;     no-inst-at-LSU-wbuf0-MT-step
;     uniq-inst-at-LSU-wbuf1-MT-step
;     no-inst-at-LSU-wbuf1-MT-step
;     uniq-inst-at-LSU-lch-MT-step
;     no-inst-at-LSU-lch-MT-step

;;;; Proof of no-stage-conflict for initial states
(defthm no-stage-conflict-init-MT
    (implies (and (MA-state-p MA) (b1p (MA-flushed? MA)))
	     (no-stage-conflict (init-MT MA) MA))
  :Hints (("goal" :in-theory (enable init-MT no-stage-conflict
				     NO-IFU-STG-CONFLICT
				     NO-DQ-STG-CONFLICT
				     NO-IU-STG-CONFLICT
				     NO-MU-STG-CONFLICT
				     NO-BU-STG-CONFLICT
				     NO-LSU-STG-CONFLICT
				     NO-INST-AT-STGS
				     MA-flushed? lift-b-ops
				     IFU-empty? DQ-empty?
				     IU-empty? BU-empty? LSU-empty?
				     MU-empty? NO-INST-AT-STG))))

;; Proof of no-inst-at-non-retire-MT-step-if-flush-all
;; This lemma says that after flush-all? is asserted, only committed
;; instructions can be in a MAETT.

(encapsulate nil
(local
(defthm no-inst-at-non-retire-MT-step-if-flush-all-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (MT-all-commit-before-trace trace MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (flush-all? MA sigs))
		  (not (retire-stg-p stg))
		  (not (commit-stg-p stg)))
	     (no-inst-at-stg-in-trace stg (step-trace trace MT MA sigs
						      ISA spc smc)))
  :hints ((when-found (INST-CAUSE-JMP? (CAR TRACE) MT MA SIGS)
		      (:cases ((committed-p (car trace)))))
	  ("goal" :in-theory (enable committed-p)))))

(defthm no-inst-at-non-retire-MT-step-if-flush-all
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (flush-all? MA sigs))
		  (not (retire-stg-p stg))
		  (not (commit-stg-p stg)))
	     (no-inst-at-stg stg (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg MT-step))))
)

;;; Proof of no-IFU-stg-conflict-preserved
;;; There exists an instruction at IFU stage iff IFU-valid? is on.
(encapsulate nil
(local
(defthm uniq-inst-at-IFU-MT-step-help-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (b1p (DQ-full? (MA-dq MA)))
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (IFU-valid? (MA-IFU MA)))
		  (no-inst-at-stg-in-trace '(IFU) trace))
	     (no-inst-at-stg-in-trace '(IFU) (step-trace trace MT MA sigs
							 ISA spc smc)))
  :hints (("goal" :in-theory (enable IFU-stg-p)))))

(local
(defthm uniq-inst-at-IFU-MT-step-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (b1p (DQ-full? (MA-dq MA)))
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (IFU-valid? (MA-IFU MA)))
		  (uniq-inst-at-stg-in-trace '(IFU) trace))
	     (uniq-inst-at-stg-in-trace '(IFU) (step-trace trace MT MA sigs
							   ISA spc smc)))
  :hints (("goal" :in-theory (enable IFU-stg-p)))))

(defthm uniq-inst-at-IFU-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (DQ-full? (MA-dq MA)))
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (IFU-valid? (MA-IFU MA))))
	     (uniq-inst-at-stg '(IFU) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (e/d (uniq-inst-at-stg)
				  (UNIQ-INST-AT-IFU-IF-IFU-VALID))
		  :use ((:instance UNIQ-INST-AT-IFU-IF-IFU-VALID)))))
)

(defthm not-inst-step-inst-if-fetch-inst
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (b1p (fetch-inst? MA sigs))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (equal (INST-stg (step-inst i MT MA sigs)) '(IFU))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (fetch-inst? lift-b-ops
				     new-dq-stage)
				  (inst-is-at-one-of-the-stages)))))
				  

(encapsulate nil
(local
(defthm uniq-inst-at-IFU-MT-step-if-fetch-inst-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (fetch-inst? MA sigs)))
	     (uniq-inst-at-stg-in-trace '(IFU)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-IFU-MT-step-if-fetch-inst
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (fetch-inst? MA sigs)))
	     (uniq-inst-at-stg '(IFU) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stg))))
)

(defthm not-INST-stg-step-INST-IFU-if-not-DQ-full
    (implies (and (INST-p i) (not (b1p (DQ-full? (MA-DQ MA)))))
	     (not (equal (INST-stg (step-INST i MT MA sigs)) '(IFU))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (new-dq-stage)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-IFU-MT-step-if-not-fetch-inst-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (fetch-inst? MA sigs)))
		  (not (b1p (DQ-full? (MA-DQ MA)))))
	     (no-inst-at-stg-in-trace '(IFU)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-IFU-MT-step-if-not-fetch-inst
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (fetch-inst? MA sigs)))
		  (not (b1p (DQ-full? (MA-DQ MA)))))
	     (no-inst-at-stg '(IFU) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg))))
)

(encapsulate nil
(local
(defthm no-inst-at-IFU-MT-step-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (fetch-inst? MA sigs)))
		  (no-inst-at-stg-in-trace '(IFU) trace))
	     (no-inst-at-stg-in-trace '(IFU) (step-trace trace MT MA sigs
							 ISA spc smc)))
  :hints (("goal" :in-theory (enable IFU-stg-p)))))

(defthm no-inst-at-IFU-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (fetch-inst? MA sigs)))
		  (no-inst-at-stg '(IFU) MT))
	     (no-inst-at-stg '(IFU) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable MT-step no-inst-at-stg))))
)

(defthm no-IFU-stg-conflict-preserved
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA))
	     (no-IFU-stg-conflict (MT-step MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable no-IFU-stg-conflict fetch-inst?
				     step-IFU lift-b-ops))))

;;;  Proof of no-DQ-stg-conflict-preserved
;; Proof of uniq-inst-at-DE0-mt-step
(defthm not-INST-stg-step-inst-DE0-if-not-DE0-valid
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (IFU-stg-p (INST-stg i)))
		  (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (equal (INST-stg (step-inst i MT MA sigs)) '(DQ 0))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (disable inst-is-at-one-of-the-stages))))

(encapsulate nil
(local
(defthm uniq-inst-at-DE0-if-IFU-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (b1p (IFU-valid? (MA-IFU MA)))
		  (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
		  (not (b1p (flush-all? MA sigs)))
		  (no-inst-at-stg-in-trace '(IFU) trace)
		  (MAETT-p MT) (MA-state-p MA))
	     (no-inst-at-stg-in-trace '(DQ 0) (step-trace trace MT MA sigs
							  ISA spc smc)))
  :hints (("goal" :in-theory (enable lift-b-ops dq-full? new-dq-stage
				     IFU-stg-p)))))

(local
(defthm uniq-inst-at-DE0-if-IFU-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (b1p (IFU-valid? (MA-IFU MA)))
		  (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
		  (not (b1p (flush-all? MA sigs)))
		  (INST-listp trace)
		  (uniq-inst-at-stg-in-trace '(IFU) trace)
		  (MAETT-p MT) (MA-state-p MA))
	     (uniq-inst-at-stg-in-trace '(DQ 0) (step-trace trace MT MA sigs
							    ISA spc smc)))
  :hints (("goal" :in-theory (enable lift-b-ops dq-full? new-dq-stage
				     IFU-stg-p)))))

(defthm uniq-inst-at-DE0-MT-step-if-IFU-valid
    (implies (and (inv MT MA)
		  (b1p (IFU-valid? (MA-IFU MA)))
		  (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
		  (not (b1p (flush-all? MA sigs)))
		  (MAETT-p MT) (MA-state-p MA))
	     (uniq-inst-at-stg '(DQ 0) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance UNIQ-INST-AT-IFU-IF-IFU-VALID))
		  :in-theory (e/d (uniq-inst-at-stg)
				  (UNIQ-INST-AT-IFU-IF-IFU-VALID)))))
)

(defthm not-INST-stg-step-inst-DE0-if-DE1-empty
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (IFU-stg-p (INST-stg i)))
		  (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA)))))
		  (b1p (dispatch-inst? MA))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (equal (INST-stg (step-inst i MT MA sigs)) '(DQ 0))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (dq-stg-p)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-DE0-if-DE1-empty-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (b1p (IFU-valid? (MA-IFU MA)))
		  (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA)))))
		  (b1p (dispatch-inst? MA))
		  (no-inst-at-stg-in-trace '(IFU) trace)
		  (not (b1p (flush-all? MA sigs)))
		  (MAETT-p MT) (MA-state-p MA))
	     (no-inst-at-stg-in-trace '(DQ 0)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))
  :hints (("goal" :in-theory (enable lift-b-ops dq-full? new-dq-stage
				     IFU-stg-p)))))

(local
(defthm uniq-inst-at-DE0-if-DE1-empty-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (b1p (IFU-valid? (MA-IFU MA)))
		  (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA)))))
		  (b1p (dispatch-inst? MA))
		  (uniq-inst-at-stg-in-trace '(IFU) trace)
		  (not (b1p (flush-all? MA sigs)))
		  (MAETT-p MT) (MA-state-p MA))
	     (uniq-inst-at-stg-in-trace '(DQ 0)
					(step-trace trace MT MA sigs
						    ISA spc smc)))
  :hints (("goal" :in-theory (enable lift-b-ops dq-full? new-dq-stage
				     IFU-stg-p))
	  (when-found-multiple ((B1P (DE-VALID? (DQ-DE1 (MA-DQ MA))))
				(B1P (DISPATCH-INST? MA))
				(MT-DQ-LEN MT))
		       (:cases ((b1p (DE-VALID? (DQ-DE0 (MA-DQ MA))))))))))

(defthm uniq-inst-at-DE0-MT-step-if-DE1-empty
    (implies (and (inv MT MA)
		  (b1p (IFU-valid? (MA-IFU MA)))
		  (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA)))))
		  (b1p (dispatch-inst? MA))
		  (not (b1p (flush-all? MA sigs)))
		  (MAETT-p MT) (MA-state-p MA))
	     (uniq-inst-at-stg '(DQ 0) (MT-step MT MA sigs)))
    :hints (("goal" :use ((:instance UNIQ-INST-AT-IFU-IF-IFU-VALID))
		  :in-theory (e/d (uniq-inst-at-stg)
				  (UNIQ-INST-AT-IFU-IF-IFU-VALID)))))
)

(defthm not-INST-stg-step-inst-DE0-if-DE1-valid
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (equal (INST-stg i) '(DQ 1)))
		  (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))
		  (b1p (dispatch-inst? MA))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (equal (INST-stg (step-inst i MT MA sigs)) '(DQ 0))))
  :hints (("goal" :use ((:instance inst-is-at-one-of-the-stages)
			(:instance mt-dq-len-ge-2))
		  :in-theory (e/d (dq-stg-p new-dq-stage COERCE-DQ-STG)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-DE0-if-DE1-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))
		  (b1p (dispatch-inst? MA))
		  (not (b1p (flush-all? MA sigs)))
		  (no-inst-at-stg-in-trace '(DQ 1) trace)
		  (MAETT-p MT) (MA-state-p MA))
	     (no-inst-at-stg-in-trace '(DQ 0) (step-trace trace MT MA sigs
							  ISA spc smc)))))

(local
(defthm uniq-inst-at-DE0-if-DE1-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))
		  (b1p (dispatch-inst? MA))
		  (not (b1p (flush-all? MA sigs)))
		  (uniq-inst-at-stg-in-trace '(DQ 1) trace)
		  (MAETT-p MT) (MA-state-p MA))
	     (uniq-inst-at-stg-in-trace '(DQ 0) (step-trace trace MT MA sigs
							    ISA spc smc)))))

(defthm uniq-inst-at-DE0-MT-step-if-DE1-valid
    (implies (and (inv MT MA)
		  (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))
		  (b1p (dispatch-inst? MA))
		  (not (b1p (flush-all? MA sigs)))
		  (MAETT-p MT) (MA-state-p MA))
	     (uniq-inst-at-stg '(DQ 0) (MT-step MT MA sigs)))
      :hints (("goal" :use ((:instance UNIQ-INST-AT-STG-IF-DQ-DE1-valid))
		  :in-theory (e/d (uniq-inst-at-stg)
				  (UNIQ-INST-AT-STG-IF-DQ-DE1-valid)))))
)

(defthm not-INST-stg-step-inst-DE0-if-DE0-valid
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (equal (INST-stg i) '(DQ 0)))
		  (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))
		  (not (b1p (dispatch-inst? MA)))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (equal (INST-stg (step-inst i MT MA sigs)) '(DQ 0))))
  :hints (("goal" :use ((:instance inst-is-at-one-of-the-stages)
			(:instance MT-dq-len-ge-1))
		  :in-theory (e/d (dq-stg-p new-dq-stage coerce-dq-stg)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-DE0-MT-step-if-dq-de0-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))
		  (not (b1p (dispatch-inst? MA)))
		  (not (b1p (flush-all? MA sigs)))
		  (no-inst-at-stg-in-trace '(DQ 0) trace)
		  (MAETT-p MT) (MA-state-p MA))
	     (no-inst-at-stg-in-trace '(DQ 0) (step-trace trace MT MA sigs
							  ISA spc smc)))))
(local
(defthm uniq-inst-at-DE0-MT-step-if-dq-de0-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))
		  (not (b1p (dispatch-inst? MA)))
		  (not (b1p (flush-all? MA sigs)))
		  (uniq-inst-at-stg-in-trace '(DQ 0) trace)
		  (MAETT-p MT) (MA-state-p MA))
	     (uniq-inst-at-stg-in-trace '(DQ 0) (step-trace trace MT MA sigs
							    ISA spc smc)))))

(defthm uniq-inst-at-DE0-MT-step-if-dq-de0-valid
    (implies (and (inv MT MA)
		  (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))
		  (not (b1p (dispatch-inst? MA)))
		  (not (b1p (flush-all? MA sigs)))
		  (MAETT-p MT) (MA-state-p MA))
	     (uniq-inst-at-stg '(DQ 0) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance UNIQ-INST-AT-STG-IF-DQ-DE0-valid))
		  :in-theory (e/d (uniq-inst-at-stg)
				  (UNIQ-INST-AT-STG-IF-DQ-DE0-valid)))))
)

(defthm uniq-inst-at-DE0-mt-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (DE-valid? (DQ-DE0 (MA-DQ (MA-step MA sigs))))))
	     (uniq-INST-at-stg '(DQ 0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-dq step-DE0 lift-b-ops
				     decode-output
				     DE3-out DE2-out DE1-out))))

;; Proof of no-inst-at-DE0-mt-step
(encapsulate nil
(local
(defthm no-inst-at-DE0-mt-step-if-not-IFU-valid-help-lemma1
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(IFU) trace)
		  (no-inst-at-stg-in-trace '(DQ 0) trace)
		  (no-inst-at-stg-in-trace '(DQ 1) trace)
		  (no-inst-at-stg-in-trace '(DQ 2) trace)
		  (no-inst-at-stg-in-trace '(DQ 3) trace))
	     (no-inst-at-stg-in-trace '(DQ 0)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))
  :hints (("goal" :in-theory (enable IFU-stg-p DQ-stg-p)))))

(defthm no-inst-at-DE0-mt-step-if-not-IFU-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
		  (not (b1p (IFU-valid? (MA-IFU MA)))))
	     (no-inst-at-stg '(DQ 0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg)
		  :use ((:instance NO-INST-AT-IFU-IF-IFU-INVALID)
			(:instance NO-INST-AT-STG-IF-NO-DQ-DE0-VALID)
			(:instance NO-INST-AT-STG-IF-NO-DQ-DE1-VALID)
			(:instance NO-INST-AT-STG-IF-NO-DQ-DE2-VALID)
			(:instance NO-INST-AT-STG-IF-NO-DQ-DE3-VALID)))))
)

(defthm not-INST-stg-step-INST-DE0-if-not-IFU-DE1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA))
		  (not (equal (INST-stg i) '(IFU)))
		  (not (equal (INST-stg i) '(DQ 1))))
	     (not (equal (inst-stg (step-INST i MT MA sigs)) '(DQ 0))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (dq-stg-p new-dq-stage IFU-stg-p
				     DQ-stg-p coerce-dq-stg)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-DE0-mt-step-if-dispatch-inst-help-lemma1
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA))
		  (no-inst-at-stg-in-trace '(IFU) trace)
		  (no-inst-at-stg-in-trace '(DQ 1) trace))
	     (no-inst-at-stg-in-trace '(DQ 0)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-DE0-mt-step-if-dispatch-inst
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA))
		  (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA)))))
		  (not (b1p (IFU-valid? (MA-IFU MA)))))
	     (no-inst-at-stg '(DQ 0) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance NO-INST-AT-IFU-IF-IFU-INVALID)
			(:instance NO-INST-AT-STG-IF-NO-DQ-DE1-VALID))
		  :in-theory (enable no-inst-at-stg))))
)

(defthm no-inst-at-DE0-mt-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (DE-valid? (DQ-DE0 (MA-DQ (MA-step MA sigs)))))))
	     (no-INST-at-stg '(DQ 0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-dq step-DE0 lift-b-ops
				     decode-output
				     DE3-out DE2-out DE1-out))))

;; Proof of uniq-inst-at-DE1-mt-step
(defthm not-INST-stg-step-INST-DE1-if-not-dispatch-inst
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (dispatch-inst? MA)))
		  (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))
		  (not (equal (INST-stg i) '(DQ 1))))
	     (not (equal (inst-stg (step-INST i MT MA sigs)) '(DQ 1))))
  :hints (("goal" :use ((:instance inst-is-at-one-of-the-stages)
			(:instance mt-dq-len-ge-2))
		  :in-theory (e/d (dq-stg-p new-dq-stage IFU-stg-p
				     DQ-stg-p coerce-dq-stg)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-DE1-MT-step-if-DE1-valid-help-lemma2
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (dispatch-inst? MA)))
		  (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))
		  (no-inst-at-stg-in-trace '(DQ 1) trace))
	     (no-inst-at-stg-in-trace '(DQ 1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-DE1-MT-step-if-DE1-valid-help-lemma1
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (dispatch-inst? MA)))
		  (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (uniq-inst-at-stg-in-trace '(DQ 1) trace))
	     (uniq-inst-at-stg-in-trace '(DQ 1)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-DE1-MT-step-if-DE1-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (dispatch-inst? MA)))
		  (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg '(DQ 1) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance UNIQ-INST-AT-STG-IF-DQ-DE1-VALID))
		  :in-theory (e/d (uniq-inst-at-stg)
				  (UNIQ-INST-AT-STG-IF-DQ-DE1-VALID)))))
)

(defthm not-INST-stg-step-INST-DE2-if-DE2-valid
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA))
		  (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))
		  (not (equal (INST-stg i) '(DQ 2))))
	     (not (equal (inst-stg (step-INST i MT MA sigs)) '(DQ 1))))
  :hints (("goal" :use ((:instance inst-is-at-one-of-the-stages)
			(:instance mt-dq-len-ge-3))
		  :in-theory (e/d (dq-stg-p new-dq-stage IFU-stg-p
				     DQ-stg-p coerce-dq-stg)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-DE1-MT-step-if-de2-valid-help-lemma2
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA))
		  (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))
		  (no-inst-at-stg-in-trace '(DQ 2) trace))
	     (no-inst-at-stg-in-trace '(DQ 1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-DE1-MT-step-if-de2-valid-help-lemma1
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA))
		  (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (uniq-inst-at-stg-in-trace '(DQ 2) trace))
	     (uniq-inst-at-stg-in-trace '(DQ 1)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-DE1-MT-step-if-de2-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA))
		  (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg '(DQ 1) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance UNIQ-INST-AT-STG-IF-DQ-DE2-VALID))
		  :in-theory (e/d (uniq-inst-at-stg)
				  (UNIQ-INST-AT-STG-IF-DQ-DE2-VALID)))))
)

(defthm not-INST-stg-step-INST-DE1-if-IFU
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (and (not (b1p (dispatch-inst? MA)))
			   (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))
			   (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))))
		      (and (b1p (dispatch-inst? MA))
			   (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))
			   (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA)))))))
		  (not (equal (INST-stg i) '(IFU))))
	     (not (equal (inst-stg (step-INST i MT MA sigs)) '(DQ 1))))
  :hints (("goal" :use ((:instance inst-is-at-one-of-the-stages))
		  :in-theory (e/d (dq-stg-p new-dq-stage IFU-stg-p
				     DQ-stg-p coerce-dq-stg)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-DE1-MT-step-if-DE1-empty-help-lemma2
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (and (not (b1p (dispatch-inst? MA)))
			   (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))
			   (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))))
		      (and (b1p (dispatch-inst? MA))
			   (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))
			   (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA)))))))
		  (no-inst-at-stg-in-trace '(IFU) trace))
	     (no-inst-at-stg-in-trace '(DQ 1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-DE1-MT-step-if-DE1-empty-help-lemma1
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (and (not (b1p (dispatch-inst? MA)))
			   (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))
			   (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))))
		      (and (b1p (dispatch-inst? MA))
			   (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))
			   (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA)))))))
		  (not (b1p (flush-all? MA sigs)))
		  (uniq-inst-at-stg-in-trace '(IFU) trace))
	     (uniq-inst-at-stg-in-trace '(DQ 1)
					(step-trace trace MT MA sigs
						    ISA spc smc)))
  :hints (("goal" :in-theory (enable DQ-FULL? new-dq-stage lift-b-ops)))))

(defthm uniq-inst-at-DE1-MT-step-if-DE1-empty
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (and (not (b1p (dispatch-inst? MA)))
			   (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))
			   (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))))
		      (and (b1p (dispatch-inst? MA))
			   (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))
			   (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA)))))))
		  (b1p (IFU-valid? (MA-IFU MA)))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg '(DQ 1) (MT-step MT MA sigs)))
    :hints (("goal" :use (
			(:instance UNIQ-INST-AT-IFU-IF-IFU-VALID))
		  :in-theory (e/d (uniq-inst-at-stg)
				  (UNIQ-INST-AT-IFU-IF-IFU-VALID)))))
)

(defthm uniq-inst-at-DE1-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (DE-valid? (DQ-DE1 (MA-DQ (MA-step MA sigs))))))
	     (uniq-INST-at-stg '(DQ 1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-dq step-DE1 lift-b-ops
				     decode-output DE3-out DE2-out))))

;; Proof of no-inst-at-DE1-mt-step
(defthm not-INST-stg-step-INST-DE1-if-not-DQ-stg-p
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (not (DQ-stg-p (INST-stg i)))
		  (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))))
	     (not (equal (INST-stg (step-INST i MT MA sigs)) '(DQ 1))))
  :hints  (("goal" :use ((:instance inst-is-at-one-of-the-stages)
			 (:instance MT-DQ-len-ge-1))
		   :in-theory (e/d (dq-stg-p new-dq-stage IFU-stg-p
				      DQ-stg-p coerce-dq-stg)
				   (inst-is-at-one-of-the-stages)))))
  

(encapsulate nil
(local
(defthm no-inst-at-DE1-mt-step-if-not-DE0-valid-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
		  (no-INST-at-stg-in-trace '(DQ 0) trace)
		  (no-INST-at-stg-in-trace '(DQ 1) trace)
		  (no-INST-at-stg-in-trace '(DQ 2) trace)
		  (no-INST-at-stg-in-trace '(DQ 3) trace))
	     (no-INST-at-stg-in-trace '(DQ 1) (step-trace trace MT MA sigs
							  ISA spc smc)))
  :hints (("goal" :in-theory (enable DQ-stg-p)))))

(defthm no-inst-at-DE1-mt-step-if-not-DE0-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))))
	     (no-INST-at-stg '(DQ 1) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance NO-INST-AT-STG-IF-NO-DQ-DE0-VALID)
			(:instance NO-INST-AT-STG-IF-NO-DQ-DE1-VALID)
			(:instance NO-INST-AT-STG-IF-NO-DQ-DE2-VALID)
			(:instance NO-INST-AT-STG-IF-NO-DQ-DE3-VALID))
		  :in-theory (e/d (no-inst-at-stg) ()))))
)

(defthm not-INST-stg-step-INST-DE1-if-not-DE2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (not (equal (INST-stg i) '(DQ 2)))
		  (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA)))))
		  (b1p (dispatch-inst? MA)))
	     (not (equal (INST-stg (step-INST i MT MA sigs)) '(DQ 1))))
  :hints  (("goal" :use ((:instance inst-is-at-one-of-the-stages)
			 (:instance MT-DQ-len-lt-2))
		   :in-theory (e/d (dq-stg-p new-dq-stage IFU-stg-p
				      DQ-stg-p coerce-dq-stg)
				   (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-DE1-mt-step-if-not-DE1-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA))
		  (no-inst-at-stg-in-trace '(DQ 2) trace)
		  (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))))
	     (no-INST-at-stg-in-trace '(DQ 1) (step-trace trace MT MA sigs
							  ISA spc smc)))))

(defthm no-inst-at-DE1-mt-step-if-not-DE1-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA))
		  (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))))
	     (no-INST-at-stg '(DQ 1) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance NO-INST-AT-STG-IF-NO-DQ-DE2-VALID))
		  :in-theory (e/d (no-inst-at-stg) ()))))
)

(defthm not-INST-stg-step-INST-DE1-if-not-IFU-DE1-DE2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (not (equal (INST-stg i) '(IFU)))
		  (not (equal (INST-stg i) '(DQ 1)))
		  (not (equal (INST-stg i) '(DQ 2))))
	     (not (equal (INST-stg (step-INST i MT MA sigs)) '(DQ 1))))
  :hints  (("goal" :use ((:instance inst-is-at-one-of-the-stages))
		   :in-theory (e/d (dq-stg-p new-dq-stage IFU-stg-p
				      DQ-stg-p coerce-dq-stg
				      STEP-INST-DQ-INST step-inst-dq
				      dispatch-inst)
				   (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-DE1-mt-step-if-not-IFU-DE1-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(DQ 1) trace)
		  (no-inst-at-stg-in-trace '(DQ 2) trace)
		  (no-inst-at-stg-in-trace '(IFU) trace))
	     (no-INST-at-stg-in-trace '(DQ 1) (step-trace trace MT MA sigs
							  ISA spc smc)))))

(defthm no-inst-at-DE1-mt-step-if-not-IFU-DE1-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA)))))
		  (not (b1p (IFU-valid? (MA-IFU MA)))))
	     (no-INST-at-stg '(DQ 1) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance NO-INST-AT-STG-IF-NO-DQ-DE1-VALID)
			(:instance NO-INST-AT-STG-IF-NO-DQ-DE2-VALID)
			(:instance NO-INST-AT-IFU-IF-IFU-INVALID))
		  :in-theory (enable no-inst-at-stg))))
)

(defthm not-INST-stg-step-inst-DE1-if-not-IFU-DE2 
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (b1p (dispatch-inst? MA))
		  (not (equal (INST-stg i) '(IFU)))
		  (not (equal (INST-stg i) '(DQ 2))))
	     (not (equal (INST-stg (step-INST i MT MA sigs)) '(DQ 1))))
  :hints (("goal" :use ((:instance inst-is-at-one-of-the-stages))
		  :in-theory (e/d (new-dq-stage coerce-dq-stg
				     IFU-stg-p DQ-stg-p)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-DE1-mt-step-if-not-IFU-DE2-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA))
		  (no-INST-at-stg-in-trace '(DQ 2) trace)
		  (no-INST-at-stg-in-trace '(IFU) trace))
	     (no-INST-at-stg-in-trace '(DQ 1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-DE1-mt-step-if-not-IFU-DE2-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA))
		  (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA)))))
		  (not (b1p (IFU-valid? (MA-IFU MA)))))
	     (no-INST-at-stg '(DQ 1) (MT-step MT MA sigs)))
    :hints (("goal" :in-theory (enable no-INST-at-stg)
		    :use ((:instance NO-INST-AT-STG-IF-NO-DQ-DE2-VALID)
			  (:instance NO-INST-AT-IFU-IF-IFU-INVALID)))))
)

(defthm no-inst-at-DE1-mt-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (DE-valid? (DQ-DE1 (MA-DQ (MA-step MA sigs)))))))
	     (no-INST-at-stg '(DQ 1) (MT-step MT MA sigs)))
    :hints (("goal" :in-theory (enable step-dq step-DE1 lift-b-ops
				     decode-output DE3-out DE2-out))))

;; Proof of uniq-inst-at-DE2-mt-step
(defthm not-INST-stg-step-INST-DE2-if-not-dispatch-inst
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (dispatch-inst? MA)))
		  (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))
		  (not (equal (INST-stg i) '(DQ 2))))
	     (not (equal (inst-stg (step-INST i MT MA sigs)) '(DQ 2))))
  :hints (("goal" :use ((:instance inst-is-at-one-of-the-stages)
			(:instance mt-dq-len-ge-3))
		  :in-theory (e/d (dq-stg-p new-dq-stage IFU-stg-p
				     DQ-stg-p coerce-dq-stg)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-DE1-MT-step-if-DE1-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (dispatch-inst? MA)))
		  (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))
		  (no-inst-at-stg-in-trace '(DQ 2) trace))
	     (no-inst-at-stg-in-trace '(DQ 2)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-DE2-MT-step-if-de2-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (dispatch-inst? MA)))
		  (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (uniq-inst-at-stg-in-trace '(DQ 2) trace))
	     (uniq-inst-at-stg-in-trace '(DQ 2)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-DE2-MT-step-if-de2-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (dispatch-inst? MA)))
		  (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg '(DQ 2) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance UNIQ-INST-AT-STG-IF-DQ-DE2-VALID))
		  :in-theory (e/d (uniq-inst-at-stg)
				  (UNIQ-INST-AT-STG-IF-DQ-DE2-VALID)))))
)

(defthm not-INST-stg-step-INST-DE2-if-DE3-valid
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA))
		  (b1p (DE-valid? (DQ-DE3 (MA-DQ MA))))
		  (not (equal (INST-stg i) '(DQ 3))))
	     (not (equal (inst-stg (step-INST i MT MA sigs)) '(DQ 2))))
  :hints (("goal" :use ((:instance inst-is-at-one-of-the-stages))
		  :in-theory (e/d (dq-stg-p new-dq-stage IFU-stg-p
				     DQ-stg-p coerce-dq-stg)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-DE1-MT-step-if-de2-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA))
		  (b1p (DE-valid? (DQ-DE3 (MA-DQ MA))))
		  (no-inst-at-stg-in-trace '(DQ 3) trace))
	     (no-inst-at-stg-in-trace '(DQ 2)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-DE2-MT-step-if-de3-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA))
		  (b1p (DE-valid? (DQ-DE3 (MA-DQ MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (uniq-inst-at-stg-in-trace '(DQ 3) trace))
	     (uniq-inst-at-stg-in-trace '(DQ 2)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-DE1-MT-step-if-de3-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA))
		  (b1p (DE-valid? (DQ-DE3 (MA-DQ MA))))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg '(DQ 2) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance UNIQ-INST-AT-STG-IF-DQ-DE3-VALID))
		  :in-theory (e/d (uniq-inst-at-stg)
				  (UNIQ-INST-AT-STG-IF-DQ-DE3-VALID)))))
)

(defthm not-INST-stg-step-INST-DE2-if-IFU
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (and (not (b1p (dispatch-inst? MA)))
			   (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))
			   (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))))
		      (and (b1p (dispatch-inst? MA))
			   (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))
			   (not (b1p (DE-valid? (DQ-DE3 (MA-DQ MA)))))))
		  (not (equal (INST-stg i) '(IFU))))
	     (not (equal (inst-stg (step-INST i MT MA sigs)) '(DQ 2))))
  :hints (("goal" :use ((:instance inst-is-at-one-of-the-stages))
		  :in-theory (e/d (dq-stg-p new-dq-stage IFU-stg-p
				     DQ-stg-p coerce-dq-stg)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-DE1-MT-step-if-DE1-empty-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (and (not (b1p (dispatch-inst? MA)))
			   (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))
			   (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))))
		      (and (b1p (dispatch-inst? MA))
			   (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))
			   (not (b1p (DE-valid? (DQ-DE3 (MA-DQ MA)))))))
		  (no-inst-at-stg-in-trace '(IFU) trace))
	     (no-inst-at-stg-in-trace '(DQ 2)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-DE2-MT-step-if-DE1-empty-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (and (not (b1p (dispatch-inst? MA)))
			   (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))
			   (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))))
		      (and (b1p (dispatch-inst? MA))
			   (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))
			   (not (b1p (DE-valid? (DQ-DE3 (MA-DQ MA)))))))
		  (not (b1p (flush-all? MA sigs)))
		  (uniq-inst-at-stg-in-trace '(IFU) trace))
	     (uniq-inst-at-stg-in-trace '(DQ 2)
					(step-trace trace MT MA sigs
						    ISA spc smc)))
  :hints (("goal" :in-theory (enable DQ-FULL? new-dq-stage lift-b-ops)))))

(defthm uniq-inst-at-DE1-MT-step-if-de2-empty
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (and (not (b1p (dispatch-inst? MA)))
			   (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))
			   (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))))
		      (and (b1p (dispatch-inst? MA))
			   (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))
			   (not (b1p (DE-valid? (DQ-DE3 (MA-DQ MA)))))))
		  (b1p (IFU-valid? (MA-IFU MA)))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg '(DQ 2) (MT-step MT MA sigs)))
    :hints (("goal" :use ((:instance UNIQ-INST-AT-IFU-IF-IFU-VALID))
		  :in-theory (e/d (uniq-inst-at-stg)
				  (UNIQ-INST-AT-IFU-IF-IFU-VALID)))))
)

(defthm uniq-inst-at-DE2-mt-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (DE-valid? (DQ-DE2 (MA-DQ (MA-step MA sigs))))))
	     (uniq-INST-at-stg '(DQ 2) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-dq step-DE2 lift-b-ops
				     decode-output DE3-out))))

;; Proof of no-inst-at-DE2-mt-step
(defthm not-INST-stg-step-INST-DE2-if-not-DQ-stg-p
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (not (equal (INST-stg i) '(DQ 2)))
		  (not (equal (INST-stg i) '(DQ 3)))
		  (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))))
	     (not (equal (INST-stg (step-INST i MT MA sigs)) '(DQ 2))))
  :hints  (("goal" :use ((:instance inst-is-at-one-of-the-stages)
			 (:instance MT-DQ-len-lt-2))
		   :in-theory (e/d (dq-stg-p new-dq-stage IFU-stg-p
				      step-INST-DQ-INST
				      step-inst-dq dispatch-inst
				      DQ-stg-p coerce-dq-stg)
				   (inst-is-at-one-of-the-stages)))))
  

(encapsulate nil
(local
(defthm no-inst-at-DE2-mt-step-if-not-DE1-valid-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA)))))
		  (no-INST-at-stg-in-trace '(DQ 2) trace)
		  (no-INST-at-stg-in-trace '(DQ 3) trace))
	     (no-INST-at-stg-in-trace '(DQ 2) (step-trace trace MT MA sigs
							  ISA spc smc)))
  :hints (("goal" :in-theory (enable DQ-stg-p)))))

(defthm no-inst-at-DE2-mt-step-if-not-DE1-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))))
	     (no-INST-at-stg '(DQ 2) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance NO-INST-AT-STG-IF-NO-DQ-DE2-VALID)
			(:instance NO-INST-AT-STG-IF-NO-DQ-DE3-VALID))
		  :in-theory (e/d (no-inst-at-stg) ()))))
)

(defthm not-INST-stg-step-INST-DE2-if-not-DE3
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (not (equal (INST-stg i) '(DQ 3)))
		  (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA)))))
		  (b1p (dispatch-inst? MA)))
	     (not (equal (INST-stg (step-INST i MT MA sigs)) '(DQ 2))))
  :hints  (("goal" :use ((:instance inst-is-at-one-of-the-stages)
			 (:instance MT-DQ-len-lt-3))
		   :in-theory (e/d (dq-stg-p new-dq-stage IFU-stg-p
				      DQ-stg-p coerce-dq-stg)
				   (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-DE2-mt-step-if-not-DE2-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA))
		  (no-inst-at-stg-in-trace '(DQ 3) trace)
		  (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))))
	     (no-INST-at-stg-in-trace '(DQ 2) (step-trace trace MT MA sigs
							  ISA spc smc)))))

(defthm no-inst-at-DE2-mt-step-if-not-DE2-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA))
		  (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))))
	     (no-INST-at-stg '(DQ 2) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance NO-INST-AT-STG-IF-NO-DQ-DE3-VALID))
		  :in-theory (e/d (no-inst-at-stg) ()))))
)

(defthm not-INST-stg-step-INST-DE2-if-not-IFU-DE1-DE3
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (not (equal (INST-stg i) '(IFU)))
		  (not (equal (INST-stg i) '(DQ 2)))
		  (not (equal (INST-stg i) '(DQ 3))))
	     (not (equal (INST-stg (step-INST i MT MA sigs)) '(DQ 2))))
  :hints  (("goal" :use ((:instance inst-is-at-one-of-the-stages))
		   :in-theory (e/d (dq-stg-p new-dq-stage IFU-stg-p
				      DQ-stg-p coerce-dq-stg
				      STEP-INST-DQ-INST step-inst-dq
				      dispatch-inst)
				   (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-DE2-mt-step-if-not-IFU-DE2-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(DQ 2) trace)
		  (no-inst-at-stg-in-trace '(DQ 3) trace)
		  (no-inst-at-stg-in-trace '(IFU) trace))
	     (no-INST-at-stg-in-trace '(DQ 2) (step-trace trace MT MA sigs
							  ISA spc smc)))))

(defthm no-inst-at-DE2-mt-step-if-not-IFU-DE2-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA)))))
		  (not (b1p (IFU-valid? (MA-IFU MA)))))
	     (no-INST-at-stg '(DQ 2) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance NO-INST-AT-STG-IF-NO-DQ-DE2-VALID)
			(:instance NO-INST-AT-STG-IF-NO-DQ-DE3-VALID)
			(:instance NO-INST-AT-IFU-IF-IFU-INVALID))
		  :in-theory (enable no-inst-at-stg))))
)

(defthm not-INST-stg-step-inst-DE2-if-not-IFU-DE3 
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (b1p (dispatch-inst? MA))
		  (not (equal (INST-stg i) '(IFU)))
		  (not (equal (INST-stg i) '(DQ 3))))
	     (not (equal (INST-stg (step-INST i MT MA sigs)) '(DQ 2))))
  :hints (("goal" :use ((:instance inst-is-at-one-of-the-stages))
		  :in-theory (e/d (new-dq-stage coerce-dq-stg
				     IFU-stg-p DQ-stg-p)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-DE2-mt-step-if-not-IFU-DE3-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA))
		  (no-INST-at-stg-in-trace '(DQ 3) trace)
		  (no-INST-at-stg-in-trace '(IFU) trace))
	     (no-INST-at-stg-in-trace '(DQ 2)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-DE2-mt-step-if-not-IFU-DE3-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA))
		  (not (b1p (DE-valid? (DQ-DE3 (MA-DQ MA)))))
		  (not (b1p (IFU-valid? (MA-IFU MA)))))
	     (no-INST-at-stg '(DQ 2) (MT-step MT MA sigs)))
    :hints (("goal" :in-theory (enable no-INST-at-stg)
		    :use ((:instance NO-INST-AT-STG-IF-NO-DQ-DE3-VALID)
			  (:instance NO-INST-AT-IFU-IF-IFU-INVALID)))))
)

(defthm no-inst-at-DE2-mt-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (DE-valid? (DQ-DE2 (MA-DQ (MA-step MA sigs)))))))
	     (no-INST-at-stg '(DQ 2) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-dq step-DE2 lift-b-ops
				     decode-output DE3-out DE2-out))))

;; uniq-inst-at-DE3-mt-step
(defthm not-INST-stg-step-INST-DE3-if-not-dispatch-inst
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (dispatch-inst? MA)))
		  (b1p (DE-valid? (DQ-DE3 (MA-DQ MA))))
		  (not (equal (INST-stg i) '(DQ 3))))
	     (not (equal (inst-stg (step-INST i MT MA sigs)) '(DQ 3))))
  :hints (("goal" :use ((:instance inst-is-at-one-of-the-stages))
		  :in-theory (e/d (dq-stg-p new-dq-stage IFU-stg-p
				     DQ-FULL?
				     DQ-stg-p coerce-dq-stg)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-DE3-MT-step-if-DE3-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (dispatch-inst? MA)))
		  (b1p (DE-valid? (DQ-DE3 (MA-DQ MA))))
		  (no-inst-at-stg-in-trace '(DQ 3) trace))
	     (no-inst-at-stg-in-trace '(DQ 3)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-DE3-MT-step-if-de3-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (dispatch-inst? MA)))
		  (b1p (DE-valid? (DQ-DE3 (MA-DQ MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (uniq-inst-at-stg-in-trace '(DQ 3) trace))
	     (uniq-inst-at-stg-in-trace '(DQ 3)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-DE3-MT-step-if-de3-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (dispatch-inst? MA)))
		  (b1p (DE-valid? (DQ-DE3 (MA-DQ MA))))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg '(DQ 3) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance UNIQ-INST-AT-STG-IF-DQ-DE3-VALID))
		  :in-theory (e/d (uniq-inst-at-stg)
				  (UNIQ-INST-AT-STG-IF-DQ-DE3-VALID)))))
)

(defthm not-INST-stg-step-INST-DE3-if-IFU
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (and (not (b1p (dispatch-inst? MA)))
			   (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))
			   (not (b1p (DE-valid? (DQ-DE3 (MA-DQ MA))))))
		      (and (b1p (dispatch-inst? MA))
			   (b1p (DE-valid? (DQ-DE3 (MA-DQ MA))))))
		  (not (equal (INST-stg i) '(IFU))))
	     (not (equal (inst-stg (step-INST i MT MA sigs)) '(DQ 3))))
  :hints (("goal" :use ((:instance inst-is-at-one-of-the-stages))
		  :in-theory (e/d (dq-stg-p new-dq-stage IFU-stg-p
				     DQ-stg-p coerce-dq-stg)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-DE3-MT-step-if-IFU-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (dispatch-inst? MA)))
		  (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))
		  (not (b1p (DE-valid? (DQ-DE3 (MA-DQ MA)))))
		  (no-inst-at-stg-in-trace '(IFU) trace))
	     (no-inst-at-stg-in-trace '(DQ 3)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-DE3-MT-step-if-IFU-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (dispatch-inst? MA)))
		  (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))
		  (not (b1p (DE-valid? (DQ-DE3 (MA-DQ MA)))))
		  (not (b1p (flush-all? MA sigs)))
		  (uniq-inst-at-stg-in-trace '(IFU) trace))
	     (uniq-inst-at-stg-in-trace '(DQ 3)
					(step-trace trace MT MA sigs
						    ISA spc smc)))
  :hints (("goal" :in-theory (enable DQ-FULL? new-dq-stage lift-b-ops)))))

(defthm uniq-inst-at-DE3-MT-step-if-IFU-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (dispatch-inst? MA)))
		  (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))
		  (not (b1p (DE-valid? (DQ-DE3 (MA-DQ MA)))))
		  (b1p (IFU-valid? (MA-IFU MA)))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg '(DQ 3) (MT-step MT MA sigs)))
    :hints (("goal" :use ((:instance UNIQ-INST-AT-IFU-IF-IFU-VALID))
		  :in-theory (e/d (uniq-inst-at-stg)
				  (UNIQ-INST-AT-IFU-IF-IFU-VALID)))))
)

(defthm uniq-inst-at-DE3-mt-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (DE-valid? (DQ-DE3 (MA-DQ (MA-step MA sigs))))))
	     (uniq-INST-at-stg '(DQ 3) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-dq step-DE3 lift-b-ops
				     decode-output))))

;; Proof of no-inst-at-DE3-mt-step

(defthm not-INST-stg-step-INST-DE3-if-dispatch-inst
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA)))
	     (not (equal (INST-stg (step-INST i MT MA sigs)) '(DQ 3))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (IFU-stg-p new-dq-stage
				     lift-b-ops DQ-stg-p
				     DQ-full? coerce-dq-stg)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-DE3-mt-step-if-dispatch-inst-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA)))
	     (no-INST-at-stg-in-trace '(DQ 3)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))
  :hints (("goal" :use ((:instance NO-INST-AT-STG-IF-NO-DQ-DE3-VALID))
		  :in-theory (e/d (no-inst-at-stg) ())))))

(defthm no-inst-at-DE3-mt-step-if-dispatch-inst
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA)))
	     (no-INST-at-stg '(DQ 3) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (e/d (no-inst-at-stg) ()))))
)

(defthm not-INST-stg-step-INST-DE3-if-not-IFU-DE3
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(DQ 3)))
		  (not (equal (INST-stg i) '(IFU))))
	     (not (equal (INST-stg (step-INST i MT MA sigs)) '(DQ 3))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (IFU-stg-p new-dq-stage
				     step-INST-DQ-INST
				     step-INST-DQ dispatch-inst
				     lift-b-ops DQ-stg-p
				     DQ-full? coerce-dq-stg)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-DE3-mt-step-if-not-IFU-DE3-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-INST-at-stg-in-trace '(DQ 3) trace)
		  (no-INST-at-stg-in-trace '(IFU) trace))
	     (no-INST-at-stg-in-trace '(DQ 3)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-DE3-mt-step-if-not-IFU-DE3-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (DE-valid? (DQ-DE3 (MA-DQ MA)))))
		  (not (b1p (IFU-valid? (MA-IFU MA)))))
	     (no-INST-at-stg '(DQ 3) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance NO-INST-AT-STG-IF-NO-DQ-DE3-VALID)
			(:instance NO-INST-AT-IFU-IF-IFU-INVALID))
		  :in-theory (e/d (no-inst-at-stg) ()))))
)

(defthm not-INST-stg-step-INST-DE3-if-not-DE2-valid
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))))
	     (not (equal (INST-stg (step-INST i MT MA sigs)) '(DQ 3))))
  :hints (("goal" :use ((:instance inst-is-at-one-of-the-stages)
			(:instance MT-dq-len-lt-2))
		  :in-theory (e/d (IFU-stg-p new-dq-stage
				     step-INST-DQ-INST
				     step-INST-DQ dispatch-inst
				     lift-b-ops DQ-stg-p
				     DQ-full? coerce-dq-stg)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-DE3-mt-step-if-not-DE2-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))))
	     (no-INST-at-stg-in-trace '(DQ 3)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-DE3-mt-step-if-not-DE2-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))))
	     (no-INST-at-stg '(DQ 3) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance NO-INST-AT-STG-IF-NO-DQ-DE3-VALID))
		  :in-theory (e/d (no-inst-at-stg) ()))))
)

(defthm no-inst-at-DE3-mt-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (DE-valid? (DQ-DE3 (MA-DQ (MA-step MA sigs)))))))
	     (no-INST-at-stg '(DQ 3) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-dq step-DE3 lift-b-ops
				     decode-output))))

(defthm no-DQ-stg-conflict-preserved
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (no-DQ-stg-conflict (MT-step MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable no-DQ-stg-conflict))))

(in-theory (disable INST-STG-STEP-IFU-INST-IF-DQ-FULL))

;;; Proof of no-IU-stg-conflict
;; Proof of uniq-inst-at-IU-RS0-MT-step
(in-theory (enable inst-stg-step-inst))

(defthm not-INST-stg-step-INST-IU-RS0-if-not-IU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (IU-RS0 (MA-IU MA))))
		  (not (b1p (issue-IU-RS0? (MA-IU MA) MA)))
		  (not (equal (INST-stg i) '(IU RS0))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(IU RS0))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-INST-execute-inst
				     SELECT-IU-RS0? lift-b-ops
				     step-inst-execute
				     step-inst-dq-inst
				     step-INST-low-level-functions)
				  (inst-is-at-one-of-the-stages))))) 
				  
(encapsulate nil
(local
(defthm uniq-inst-at-IU-RS0-MT-step-if-RS0-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-INST-at-stg-in-trace '(IU RS0) trace)
		  (b1p (RS-valid? (IU-RS0 (MA-IU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-IU-RS0? (MA-IU MA) MA))))
	     (no-INST-at-stg-in-trace '(IU RS0)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-IU-RS0-MT-step-if-RS0-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-INST-at-stg-in-trace '(IU RS0) trace)
		  (b1p (RS-valid? (IU-RS0 (MA-IU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-IU-RS0? (MA-IU MA) MA))))
	     (uniq-INST-at-stg-in-trace '(IU RS0)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-IU-RS0-MT-step-if-RS0-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (IU-RS0 (MA-IU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-IU-RS0? (MA-IU MA) MA))))
	     (uniq-INST-at-stg '(IU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance UNIQ-INST-AT-IU-RS0-IF-VALID))
		  :in-theory (e/d (uniq-inst-at-stg) ()))))
)

(defthm not-INST-stg-step-INST-IU-RS0-if-not-DE0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (IU-RS0 (MA-IU MA)))))
		  (not (equal (INST-stg i) '(DQ 0)))
		  (b1p (dispatch-to-IU? MA))
		  (b1p (select-IU-RS0? (MA-IU MA))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(IU RS0))))
    :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		    :in-theory (e/d (step-INST-execute-inst
				       step-INST-dq-inst
				       dq-stg-p
				       step-INST-low-level-functions)
				    (inst-is-at-one-of-the-stages)))))
(encapsulate nil
(local
(defthm uniq-inst-at-IU-RS0-MT-step-if-dispatch-to-IU-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (IU-RS0 (MA-IU MA)))))
		  (no-INST-at-stg-in-trace '(DQ 0) trace)
		  (b1p (dispatch-to-IU? MA))
		  (b1p (select-IU-RS0? (MA-IU MA))))
	     (no-INST-at-stg-in-trace '(IU RS0)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-IU-RS0-MT-step-if-dispatch-to-IU-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (IU-RS0 (MA-IU MA)))))
		  (not (b1p (flush-all? MA sigs)))
		  (uniq-INST-at-stg-in-trace '(DQ 0) trace)
		  (b1p (dispatch-to-IU? MA))
		  (b1p (select-IU-RS0? (MA-IU MA))))
	     (uniq-INST-at-stg-in-trace '(IU RS0)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-IU-RS0-MT-step-if-dispatch-to-IU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (IU-RS0 (MA-IU MA)))))
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-to-IU? MA))
		  (b1p (select-IU-RS0? (MA-IU MA))))
	     (uniq-INST-at-stg '(IU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stg dispatch-to-IU?
				     dq-ready-to-iu? lift-b-ops)
		  :use (:instance UNIQ-INST-AT-STG-IF-DQ-DE0-VALID))))
)

(defthm uniq-inst-at-IU-RS0-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (IU-RS0 (step-IU MA sigs)))))
	     (uniq-inst-at-stg '(IU RS0)
			       (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-IU step-IU-RS0 lift-b-ops))))

;; Proof of no-inst-at-IU-RS0-MT-step
(defthm not-INST-stg-step-INST-if-issue-IU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (IU-RS0 (MA-IU MA))))
		  (b1p (issue-IU-RS0? (MA-IU MA) MA)))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(IU RS0))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-execute-inst
				     step-inst-dq-inst
				     dq-stg-p issue-IU-Rs0?
				     select-IU-RS0? lift-b-ops
				     step-INST-low-level-functions)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-IU-RS0-MT-step-if-issue-IU-RS0-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (IU-RS0 (MA-IU MA))))
		  (b1p (issue-IU-RS0? (MA-IU MA) MA)))
	     (no-INST-at-stg-in-trace '(IU RS0)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-IU-RS0-MT-step-if-issue-IU-RS0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (IU-RS0 (MA-IU MA))))
		  (b1p (issue-IU-RS0? (MA-IU MA) MA)))
	     (no-INST-at-stg '(IU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg))))

)

(defthm not-INST-stg-step-inst-IU-RS0-if-not-dispatch-to-IU
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(IU RS0)))
		  (not (b1p (dispatch-to-IU? MA))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(IU RS0))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-INST-execute-INST
				     step-INST-low-level-functions
				     step-INST-DQ-inst)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-IU-RS0-MT-step-if-not-dispatch-to-IU-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(IU RS0) trace)
		  (not (b1p (dispatch-to-IU? MA))))
	     (no-INST-at-stg-in-trace '(IU RS0)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-IU-RS0-MT-step-if-not-dispatch-to-IU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (IU-RS0 (MA-IU MA)))))
		  (not (b1p (dispatch-to-IU? MA))))
	     (no-INST-at-stg '(IU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg)
		  :use (:instance no-inst-at-IU-RS0))))
)

(defthm no-inst-at-IU-RS0-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (IU-RS0 (step-IU MA sigs))))))
	     (no-inst-at-stg '(IU RS0)
			       (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-IU step-IU-RS0 lift-b-ops
				     select-IU-RS0?))))

;; Proof of uniq-inst-at-IU-RS1-MT-step
(defthm not-INST-stg-step-INST-IU-RS1-if-not-IU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (IU-RS1 (MA-IU MA))))
		  (not (b1p (issue-IU-RS1? (MA-IU MA) MA)))
		  (not (equal (INST-stg i) '(IU RS1))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(IU RS1))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-INST-execute-inst
				     SELECT-IU-RS1? lift-b-ops
				     select-IU-RS0? dq-stg-p
				     IU-ready? dispatch-to-IU?
				     step-inst-execute
				     step-inst-dq-inst
				     step-INST-low-level-functions)
				  (inst-is-at-one-of-the-stages))))) 
(encapsulate nil
(local
(defthm uniq-inst-at-IU-RS1-MT-step-if-RS1-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-INST-at-stg-in-trace '(IU RS1) trace)
		  (b1p (RS-valid? (IU-RS1 (MA-IU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-IU-RS1? (MA-IU MA) MA))))
	     (no-INST-at-stg-in-trace '(IU RS1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-IU-RS1-MT-step-if-RS1-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-INST-at-stg-in-trace '(IU RS1) trace)
		  (b1p (RS-valid? (IU-RS1 (MA-IU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-IU-RS1? (MA-IU MA) MA))))
	     (uniq-INST-at-stg-in-trace '(IU RS1)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-IU-RS1-MT-step-if-RS1-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (IU-RS1 (MA-IU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-IU-RS1? (MA-IU MA) MA))))
	     (uniq-INST-at-stg '(IU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance UNIQ-INST-AT-IU-RS1-IF-VALID))
		  :in-theory (e/d (uniq-inst-at-stg) ()))))
)

(defthm not-INST-stg-step-INST-IU-RS1-if-not-DE1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (IU-RS1 (MA-IU MA)))))
		  (not (equal (INST-stg i) '(DQ 0)))
		  (b1p (dispatch-to-IU? MA))
		  (b1p (select-IU-RS1? (MA-IU MA))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(IU RS1))))
    :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		    :in-theory (e/d (step-INST-execute-inst
				       step-INST-dq-inst
				       dq-stg-p
				       step-INST-low-level-functions)
				    (inst-is-at-one-of-the-stages)))))
(encapsulate nil
(local
(defthm uniq-inst-at-IU-RS1-MT-step-if-dispatch-to-IU-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (IU-RS1 (MA-IU MA)))))
		  (no-INST-at-stg-in-trace '(DQ 0) trace)
		  (b1p (dispatch-to-IU? MA))
		  (b1p (select-IU-RS1? (MA-IU MA))))
	     (no-INST-at-stg-in-trace '(IU RS1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-IU-RS1-MT-step-if-dispatch-to-IU-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (IU-RS1 (MA-IU MA)))))
		  (not (b1p (flush-all? MA sigs)))
		  (uniq-INST-at-stg-in-trace '(DQ 0) trace)
		  (b1p (dispatch-to-IU? MA))
		  (b1p (select-IU-RS1? (MA-IU MA))))
	     (uniq-INST-at-stg-in-trace '(IU RS1)
					(step-trace trace MT MA sigs
						    ISA spc smc)))
  :hints (("goal" :in-theory (enable lift-b-ops select-IU-RS1?
				     select-IU-RS0?)))))

(defthm uniq-inst-at-IU-RS1-MT-step-if-dispatch-to-IU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (IU-RS1 (MA-IU MA)))))
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-to-IU? MA))
		  (b1p (select-IU-RS1? (MA-IU MA))))
	     (uniq-INST-at-stg '(IU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stg dispatch-to-IU?
				     dq-ready-to-iu? lift-b-ops)
		  :use (:instance UNIQ-INST-AT-STG-IF-DQ-DE0-VALID))))
)

(defthm uniq-inst-at-IU-RS1-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (IU-RS1 (step-IU MA sigs)))))
	     (uniq-inst-at-stg '(IU RS1)
			       (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-IU step-IU-RS1
				     lift-b-ops))))

;; Proof of no-inst-at-IU-RS1-MT-step
(defthm not-INST-stg-step-INST-if-issue-IU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (IU-RS1 (MA-IU MA))))
		  (b1p (issue-IU-RS1? (MA-IU MA) MA)))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(IU RS1))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-execute-inst
				     step-inst-dq-inst
				     dq-stg-p issue-IU-RS1?
				     DISPATCH-TO-IU? IU-ready?
				     select-IU-RS0? lift-b-ops
				     step-INST-low-level-functions)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-IU-RS1-MT-step-if-issue-IU-RS1-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (IU-RS1 (MA-IU MA))))
		  (b1p (issue-IU-RS1? (MA-IU MA) MA)))
	     (no-INST-at-stg-in-trace '(IU RS1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-IU-RS1-MT-step-if-issue-IU-RS1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (IU-RS1 (MA-IU MA))))
		  (b1p (issue-IU-RS1? (MA-IU MA) MA)))
	     (no-INST-at-stg '(IU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg))))
)

(defthm not-INST-stg-step-inst-IU-RS1-if-not-dispatch-to-IU
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(IU RS1)))
		  (or (not (b1p (dispatch-to-IU? MA)))
		      (not (b1p (select-IU-RS1? (MA-IU MA))))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(IU RS1))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-INST-execute-INST
				     select-IU-RS1? select-IU-RS0?
				     lift-b-ops dq-stg-p
				     DISPATCH-TO-IU? IU-ready?
				     step-INST-low-level-functions
				     step-INST-DQ-inst)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-IU-RS1-MT-step-if-not-dispatch-to-IU-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(IU RS1) trace)
		  (or (not (b1p (dispatch-to-IU? MA)))
		      (not (b1p (select-IU-RS1? (MA-IU MA))))))
	     (no-INST-at-stg-in-trace '(IU RS1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-IU-RS1-MT-step-if-not-dispatch-to-IU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (IU-RS1 (MA-IU MA)))))
		  (or (not (b1p (dispatch-to-IU? MA)))
		      (not (b1p (select-IU-RS1? (MA-IU MA))))))
	     (no-INST-at-stg '(IU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg)
		  :use (:instance no-inst-at-IU-RS1))))
)

(defthm no-inst-at-IU-RS1-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (IU-RS1 (step-IU MA sigs))))))
	     (no-inst-at-stg '(IU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-IU step-IU-RS1
				     lift-b-ops))))

(defthm no-IU-stg-conflict-preserved
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (no-IU-stg-conflict (MT-step MT MA sigs) (MA-step MA sigs)))
    :hints (("goal" :in-theory (enable no-IU-stg-conflict))))

;;; Proof of no-BU-stg-conflict-preserved
;; Proof of uniq-inst-at-BU-RS0-MT-step
(defthm not-INST-stg-step-INST-BU-RS0-if-not-BU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (BU-RS-valid? (BU-RS0 (MA-BU MA))))
		  (not (b1p (issue-BU-RS0? (MA-BU MA) MA)))
		  (not (equal (INST-stg i) '(BU RS0))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(BU RS0))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-INST-execute-inst
				     SELECT-BU-RS0? lift-b-ops
				     step-inst-execute
				     step-inst-dq-inst
				     step-INST-low-level-functions)
				  (inst-is-at-one-of-the-stages))))) 
				  
(encapsulate nil
(local
(defthm uniq-inst-at-BU-RS0-MT-step-if-RS0-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-INST-at-stg-in-trace '(BU RS0) trace)
		  (b1p (BU-RS-valid? (BU-RS0 (MA-BU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-BU-RS0? (MA-BU MA) MA))))
	     (no-INST-at-stg-in-trace '(BU RS0)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-BU-RS0-MT-step-if-RS0-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-INST-at-stg-in-trace '(BU RS0) trace)
		  (b1p (BU-RS-valid? (BU-RS0 (MA-BU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-BU-RS0? (MA-BU MA) MA))))
	     (uniq-INST-at-stg-in-trace '(BU RS0)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-BU-RS0-MT-step-if-RS0-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (BU-RS-valid? (BU-RS0 (MA-BU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-BU-RS0? (MA-BU MA) MA))))
	     (uniq-INST-at-stg '(BU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance UNIQ-INST-AT-BU-RS0-IF-VALID))
		  :in-theory (e/d (uniq-inst-at-stg) ()))))
)

(defthm not-INST-stg-step-INST-BU-RS0-if-not-DE0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (BU-RS-valid? (BU-RS0 (MA-BU MA)))))
		  (not (equal (INST-stg i) '(DQ 0)))
		  (b1p (dispatch-to-BU? MA))
		  (b1p (select-BU-RS0? (MA-BU MA))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(BU RS0))))
    :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		    :in-theory (e/d (step-INST-execute-inst
				       step-INST-dq-inst
				       dq-stg-p
				       step-INST-low-level-functions)
				    (inst-is-at-one-of-the-stages)))))
(encapsulate nil
(local
(defthm uniq-inst-at-BU-RS0-MT-step-if-dispatch-to-BU-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (BU-RS-valid? (BU-RS0 (MA-BU MA)))))
		  (no-INST-at-stg-in-trace '(DQ 0) trace)
		  (b1p (dispatch-to-BU? MA))
		  (b1p (select-BU-RS0? (MA-BU MA))))
	     (no-INST-at-stg-in-trace '(BU RS0)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-BU-RS0-MT-step-if-dispatch-to-BU-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (BU-RS-valid? (BU-RS0 (MA-BU MA)))))
		  (not (b1p (flush-all? MA sigs)))
		  (uniq-INST-at-stg-in-trace '(DQ 0) trace)
		  (b1p (dispatch-to-BU? MA))
		  (b1p (select-BU-RS0? (MA-BU MA))))
	     (uniq-INST-at-stg-in-trace '(BU RS0)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-BU-RS0-MT-step-if-dispatch-to-BU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (BU-RS-valid? (BU-RS0 (MA-BU MA)))))
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-to-BU? MA))
		  (b1p (select-BU-RS0? (MA-BU MA))))
	     (uniq-INST-at-stg '(BU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stg dispatch-to-BU?
				     dq-ready-to-bu? lift-b-ops)
		  :use (:instance UNIQ-INST-AT-STG-IF-DQ-DE0-VALID))))
)

(defthm uniq-inst-at-BU-RS0-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (BU-RS-valid? (BU-RS0 (step-BU MA sigs)))))
	     (uniq-inst-at-stg '(BU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-BU step-BU-RS0
				     lift-b-ops))))

;; Proof of no-inst-at-BU-RS0-MT-step
(defthm not-INST-stg-step-INST-if-issue-BU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (BU-RS-valid? (BU-RS0 (MA-BU MA))))
		  (b1p (issue-BU-RS0? (MA-BU MA) MA)))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(BU RS0))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-execute-inst
				     step-inst-dq-inst
				     dq-stg-p issue-BU-Rs0?
				     select-BU-RS0? lift-b-ops
				     step-INST-low-level-functions)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-BU-RS0-MT-step-if-issue-BU-RS0-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (BU-RS-valid? (BU-RS0 (MA-BU MA))))
		  (b1p (issue-BU-RS0? (MA-BU MA) MA)))
	     (no-INST-at-stg-in-trace '(BU RS0)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-BU-RS0-MT-step-if-issue-BU-RS0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (BU-RS-valid? (BU-RS0 (MA-BU MA))))
		  (b1p (issue-BU-RS0? (MA-BU MA) MA)))
	     (no-INST-at-stg '(BU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg))))

)

(defthm not-INST-stg-step-inst-BU-RS0-if-not-dispatch-to-BU
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(BU RS0)))
		  (not (b1p (dispatch-to-BU? MA))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(BU RS0))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-INST-execute-INST
				     step-INST-low-level-functions
				     step-INST-DQ-inst)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-BU-RS0-MT-step-if-not-dispatch-to-BU-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(BU RS0) trace)
		  (not (b1p (dispatch-to-BU? MA))))
	     (no-INST-at-stg-in-trace '(BU RS0)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-BU-RS0-MT-step-if-not-dispatch-to-BU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (BU-RS-valid? (BU-RS0 (MA-BU MA)))))
		  (not (b1p (dispatch-to-BU? MA))))
	     (no-INST-at-stg '(BU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg)
		  :use (:instance no-inst-at-BU-RS0))))
)

(defthm no-inst-at-BU-RS0-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (BU-RS-valid? (BU-RS0 (step-BU MA sigs))))))
	     (no-inst-at-stg '(BU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-BU step-BU-RS0 lift-b-ops
				     select-BU-RS0?))))

;; Proof of uniq-inst-at-BU-RS1-MT-step
(defthm not-INST-stg-step-INST-BU-RS1-if-not-BU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (BU-RS-valid? (BU-RS1 (MA-BU MA))))
		  (not (b1p (issue-BU-RS1? (MA-BU MA) MA)))
		  (not (equal (INST-stg i) '(BU RS1))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(BU RS1))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-INST-execute-inst
				     SELECT-BU-RS1? lift-b-ops
				     select-BU-RS0? dq-stg-p
				     BU-ready? dispatch-to-BU?
				     step-inst-execute
				     step-inst-dq-inst
				     step-INST-low-level-functions)
				  (inst-is-at-one-of-the-stages))))) 
(encapsulate nil
(local
(defthm uniq-inst-at-BU-RS1-MT-step-if-RS1-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-INST-at-stg-in-trace '(BU RS1) trace)
		  (b1p (BU-RS-valid? (BU-RS1 (MA-BU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-BU-RS1? (MA-BU MA) MA))))
	     (no-INST-at-stg-in-trace '(BU RS1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-BU-RS1-MT-step-if-RS1-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-INST-at-stg-in-trace '(BU RS1) trace)
		  (b1p (BU-RS-valid? (BU-RS1 (MA-BU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-BU-RS1? (MA-BU MA) MA))))
	     (uniq-INST-at-stg-in-trace '(BU RS1)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-BU-RS1-MT-step-if-RS1-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (BU-RS-valid? (BU-RS1 (MA-BU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-BU-RS1? (MA-BU MA) MA))))
	     (uniq-INST-at-stg '(BU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance UNIQ-INST-AT-BU-RS1-IF-VALID))
		  :in-theory (e/d (uniq-inst-at-stg) ()))))
)

(defthm not-INST-stg-step-INST-BU-RS1-if-not-DE1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (BU-RS-valid? (BU-RS1 (MA-BU MA)))))
		  (not (equal (INST-stg i) '(DQ 0)))
		  (b1p (dispatch-to-BU? MA))
		  (b1p (select-BU-RS1? (MA-BU MA))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(BU RS1))))
    :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		    :in-theory (e/d (step-INST-execute-inst
				       step-INST-dq-inst
				       dq-stg-p
				       step-INST-low-level-functions)
				    (inst-is-at-one-of-the-stages)))))
(encapsulate nil
(local
(defthm uniq-inst-at-BU-RS1-MT-step-if-dispatch-to-BU-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (BU-RS-valid? (BU-RS1 (MA-BU MA)))))
		  (no-INST-at-stg-in-trace '(DQ 0) trace)
		  (b1p (dispatch-to-BU? MA))
		  (b1p (select-BU-RS1? (MA-BU MA))))
	     (no-INST-at-stg-in-trace '(BU RS1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-BU-RS1-MT-step-if-dispatch-to-BU-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (BU-RS-valid? (BU-RS1 (MA-BU MA)))))
		  (not (b1p (flush-all? MA sigs)))
		  (uniq-INST-at-stg-in-trace '(DQ 0) trace)
		  (b1p (dispatch-to-BU? MA))
		  (b1p (select-BU-RS1? (MA-BU MA))))
	     (uniq-INST-at-stg-in-trace '(BU RS1)
					(step-trace trace MT MA sigs
						    ISA spc smc)))
  :hints (("goal" :in-theory (enable lift-b-ops select-BU-RS1?
				     select-BU-RS0?)))))

(defthm uniq-inst-at-BU-RS1-MT-step-if-dispatch-to-BU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (BU-RS-valid? (BU-RS1 (MA-BU MA)))))
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-to-BU? MA))
		  (b1p (select-BU-RS1? (MA-BU MA))))
	     (uniq-INST-at-stg '(BU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stg dispatch-to-BU?
				     dq-ready-to-bu? lift-b-ops)
		  :use (:instance UNIQ-INST-AT-STG-IF-DQ-DE0-VALID))))
)

(defthm uniq-inst-at-BU-RS1-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (BU-RS-valid? (BU-RS1 (step-BU MA sigs)))))
	     (uniq-inst-at-stg '(BU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops step-BU step-BU-RS1))))

;; Proof of no-inst-at-BU-RS1-MT-step
(defthm not-INST-stg-step-INST-if-issue-BU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (BU-RS-valid? (BU-RS1 (MA-BU MA))))
		  (b1p (issue-BU-RS1? (MA-BU MA) MA)))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(BU RS1))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-execute-inst
				     step-inst-dq-inst
				     dq-stg-p issue-BU-RS1?
				     DISPATCH-TO-BU? BU-ready?
				     select-BU-RS0? lift-b-ops
				     step-INST-low-level-functions)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-BU-RS1-MT-step-if-issue-BU-RS1-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (BU-RS-valid? (BU-RS1 (MA-BU MA))))
		  (b1p (issue-BU-RS1? (MA-BU MA) MA)))
	     (no-INST-at-stg-in-trace '(BU RS1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-BU-RS1-MT-step-if-issue-BU-RS1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (BU-RS-valid? (BU-RS1 (MA-BU MA))))
		  (b1p (issue-BU-RS1? (MA-BU MA) MA)))
	     (no-INST-at-stg '(BU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg))))
)

(defthm not-INST-stg-step-inst-BU-RS1-if-not-dispatch-to-BU
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(BU RS1)))
		  (or (not (b1p (dispatch-to-BU? MA)))
		      (not (b1p (select-BU-RS1? (MA-BU MA))))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(BU RS1))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-INST-execute-INST
				     select-BU-RS1? select-BU-RS0?
				     lift-b-ops dq-stg-p
				     DISPATCH-TO-BU? BU-ready?
				     step-INST-low-level-functions
				     step-INST-DQ-inst)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-BU-RS1-MT-step-if-not-dispatch-to-BU-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(BU RS1) trace)
		  (or (not (b1p (dispatch-to-BU? MA)))
		      (not (b1p (select-BU-RS1? (MA-BU MA))))))
	     (no-INST-at-stg-in-trace '(BU RS1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-BU-RS1-MT-step-if-not-dispatch-to-BU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (BU-RS-valid? (BU-RS1 (MA-BU MA)))))
		  (or (not (b1p (dispatch-to-BU? MA)))
		      (not (b1p (select-BU-RS1? (MA-BU MA))))))
	     (no-INST-at-stg '(BU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg)
		  :use (:instance no-inst-at-BU-RS1))))
)

(defthm no-inst-at-BU-RS1-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (BU-RS-valid? (BU-RS1 (step-BU MA sigs))))))
	     (no-inst-at-stg '(BU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-BU step-BU-RS1 lift-b-ops))))

(defthm no-BU-stg-conflict-preserved
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (no-BU-stg-conflict (MT-step MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable no-BU-stg-conflict))))

;;; Proof of no-MU-stg-conflict-preserved
;; Proof of uniq-INST-at-MU-RS0-MT-step
(defthm not-INST-stg-step-INST-MU-RS0-if-not-MU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (MU-RS0 (MA-MU MA))))
		  (not (b1p (issue-MU-RS0? (MA-MU MA) MA)))
		  (not (equal (INST-stg i) '(MU RS0))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU RS0))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-INST-execute-inst
				     SELECT-MU-RS0? lift-b-ops
				     step-inst-execute
				     step-inst-dq-inst
				     step-INST-low-level-functions)
				  (inst-is-at-one-of-the-stages))))) 
				  
(encapsulate nil
(local
(defthm uniq-inst-at-MU-RS0-MT-step-if-RS0-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-INST-at-stg-in-trace '(MU RS0) trace)
		  (b1p (RS-valid? (MU-RS0 (MA-MU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-MU-RS0? (MA-MU MA) MA))))
	     (no-INST-at-stg-in-trace '(MU RS0)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-MU-RS0-MT-step-if-RS0-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-INST-at-stg-in-trace '(MU RS0) trace)
		  (b1p (RS-valid? (MU-RS0 (MA-MU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-MU-RS0? (MA-MU MA) MA))))
	     (uniq-INST-at-stg-in-trace '(MU RS0)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-MU-RS0-MT-step-if-RS0-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (MU-RS0 (MA-MU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-MU-RS0? (MA-MU MA) MA))))
	     (uniq-INST-at-stg '(MU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance UNIQ-INST-AT-MU-RS0-IF-VALID))
		  :in-theory (e/d (uniq-inst-at-stg) ()))))
)

(defthm not-INST-stg-step-INST-MU-RS0-if-not-DE0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (MU-RS0 (MA-MU MA)))))
		  (not (equal (INST-stg i) '(DQ 0)))
		  (b1p (dispatch-to-MU? MA))
		  (b1p (select-MU-RS0? (MA-MU MA))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU RS0))))
    :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		    :in-theory (e/d (step-INST-execute-inst
				       step-INST-dq-inst
				       dq-stg-p
				       step-INST-low-level-functions)
				    (inst-is-at-one-of-the-stages)))))
(encapsulate nil
(local
(defthm uniq-inst-at-MU-RS0-MT-step-if-dispatch-to-MU-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (MU-RS0 (MA-MU MA)))))
		  (no-INST-at-stg-in-trace '(DQ 0) trace)
		  (b1p (dispatch-to-MU? MA))
		  (b1p (select-MU-RS0? (MA-MU MA))))
	     (no-INST-at-stg-in-trace '(MU RS0)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-MU-RS0-MT-step-if-dispatch-to-MU-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (MU-RS0 (MA-MU MA)))))
		  (not (b1p (flush-all? MA sigs)))
		  (uniq-INST-at-stg-in-trace '(DQ 0) trace)
		  (b1p (dispatch-to-MU? MA))
		  (b1p (select-MU-RS0? (MA-MU MA))))
	     (uniq-INST-at-stg-in-trace '(MU RS0)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-MU-RS0-MT-step-if-dispatch-to-MU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (MU-RS0 (MA-MU MA)))))
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-to-MU? MA))
		  (b1p (select-MU-RS0? (MA-MU MA))))
	     (uniq-INST-at-stg '(MU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stg dispatch-to-MU?
				     dq-ready-to-mu? lift-b-ops)
		  :use (:instance UNIQ-INST-AT-STG-IF-DQ-DE0-VALID))))
)

(defthm uniq-INST-at-MU-RS0-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (MU-RS0 (step-MU MA sigs)))))
	     (uniq-inst-at-stg '(MU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-MU step-MU-RS0 lift-b-ops))))

;; Proof of no-INST-at-MU-RS0-MT-step
(defthm not-INST-stg-step-INST-if-issue-MU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (MU-RS0 (MA-MU MA))))
		  (b1p (issue-MU-RS0? (MA-MU MA) MA)))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU RS0))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-execute-inst
				     step-inst-dq-inst
				     dq-stg-p issue-MU-Rs0?
				     select-MU-RS0? lift-b-ops
				     step-INST-low-level-functions)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-MU-RS0-MT-step-if-issue-MU-RS0-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (MU-RS0 (MA-MU MA))))
		  (b1p (issue-MU-RS0? (MA-MU MA) MA)))
	     (no-INST-at-stg-in-trace '(MU RS0)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-MU-RS0-MT-step-if-issue-MU-RS0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (MU-RS0 (MA-MU MA))))
		  (b1p (issue-MU-RS0? (MA-MU MA) MA)))
	     (no-INST-at-stg '(MU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg))))

)

(defthm not-INST-stg-step-inst-MU-RS0-if-not-dispatch-to-MU
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(MU RS0)))
		  (not (b1p (dispatch-to-MU? MA))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU RS0))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-INST-execute-INST
				     step-INST-low-level-functions
				     step-INST-DQ-inst)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-MU-RS0-MT-step-if-not-dispatch-to-MU-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(MU RS0) trace)
		  (not (b1p (dispatch-to-MU? MA))))
	     (no-INST-at-stg-in-trace '(MU RS0)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-MU-RS0-MT-step-if-not-dispatch-to-MU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (MU-RS0 (MA-MU MA)))))
		  (not (b1p (dispatch-to-MU? MA))))
	     (no-INST-at-stg '(MU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg)
		  :use (:instance no-inst-at-MU-RS0))))
)

(defthm no-INST-at-MU-RS0-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (MU-RS0 (step-MU MA sigs))))))
	     (no-inst-at-stg '(MU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-MU step-MU-RS0 lift-b-ops
				     select-MU-RS0?))))

;; Proof of uniq-INST-at-MU-RS1-MT-step
(defthm not-INST-stg-step-INST-MU-RS1-if-not-MU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (MU-RS1 (MA-MU MA))))
		  (not (b1p (issue-MU-RS1? (MA-MU MA) MA)))
		  (not (equal (INST-stg i) '(MU RS1))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU RS1))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-INST-execute-inst
				     SELECT-MU-RS1? lift-b-ops
				     select-MU-RS0? dq-stg-p
				     MU-ready? dispatch-to-MU?
				     step-inst-execute
				     step-inst-dq-inst
				     step-INST-low-level-functions)
				  (inst-is-at-one-of-the-stages))))) 
(encapsulate nil
(local
(defthm uniq-inst-at-MU-RS1-MT-step-if-RS1-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-INST-at-stg-in-trace '(MU RS1) trace)
		  (b1p (RS-valid? (MU-RS1 (MA-MU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-MU-RS1? (MA-MU MA) MA))))
	     (no-INST-at-stg-in-trace '(MU RS1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-MU-RS1-MT-step-if-RS1-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-INST-at-stg-in-trace '(MU RS1) trace)
		  (b1p (RS-valid? (MU-RS1 (MA-MU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-MU-RS1? (MA-MU MA) MA))))
	     (uniq-INST-at-stg-in-trace '(MU RS1)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-MU-RS1-MT-step-if-RS1-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (MU-RS1 (MA-MU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-MU-RS1? (MA-MU MA) MA))))
	     (uniq-INST-at-stg '(MU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :use ((:instance UNIQ-INST-AT-MU-RS1-IF-VALID))
		  :in-theory (e/d (uniq-inst-at-stg) ()))))
)

(defthm not-INST-stg-step-INST-MU-RS1-if-not-DE1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (MU-RS1 (MA-MU MA)))))
		  (not (equal (INST-stg i) '(DQ 0)))
		  (b1p (dispatch-to-MU? MA))
		  (b1p (select-MU-RS1? (MA-MU MA))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU RS1))))
    :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		    :in-theory (e/d (step-INST-execute-inst
				       step-INST-dq-inst
				       dq-stg-p
				       step-INST-low-level-functions)
				    (inst-is-at-one-of-the-stages)))))
(encapsulate nil
(local
(defthm uniq-inst-at-MU-RS1-MT-step-if-dispatch-to-MU-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (MU-RS1 (MA-MU MA)))))
		  (no-INST-at-stg-in-trace '(DQ 0) trace)
		  (b1p (dispatch-to-MU? MA))
		  (b1p (select-MU-RS1? (MA-MU MA))))
	     (no-INST-at-stg-in-trace '(MU RS1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-MU-RS1-MT-step-if-dispatch-to-MU-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (MU-RS1 (MA-MU MA)))))
		  (not (b1p (flush-all? MA sigs)))
		  (uniq-INST-at-stg-in-trace '(DQ 0) trace)
		  (b1p (dispatch-to-MU? MA))
		  (b1p (select-MU-RS1? (MA-MU MA))))
	     (uniq-INST-at-stg-in-trace '(MU RS1)
					(step-trace trace MT MA sigs
						    ISA spc smc)))
  :hints (("goal" :in-theory (enable lift-b-ops select-MU-RS1?
				     select-MU-RS0?)))))

(defthm uniq-inst-at-MU-RS1-MT-step-if-dispatch-to-MU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (MU-RS1 (MA-MU MA)))))
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-to-MU? MA))
		  (b1p (select-MU-RS1? (MA-MU MA))))
	     (uniq-INST-at-stg '(MU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stg dispatch-to-MU?
				     dq-ready-to-mu? lift-b-ops)
		  :use (:instance UNIQ-INST-AT-STG-IF-DQ-DE0-VALID))))
)

(defthm uniq-INST-at-MU-RS1-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (MU-RS1 (step-MU MA sigs)))))
	     (uniq-inst-at-stg '(MU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-MU step-MU-RS1 lift-b-ops))))

;; Proof of no-INST-at-MU-RS1-MT-step
(defthm not-INST-stg-step-INST-if-issue-MU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (MU-RS1 (MA-MU MA))))
		  (b1p (issue-MU-RS1? (MA-MU MA) MA)))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU RS1))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-execute-inst
				     step-inst-dq-inst
				     dq-stg-p issue-MU-RS1?
				     DISPATCH-TO-MU? MU-ready?
				     select-MU-RS0? lift-b-ops
				     step-INST-low-level-functions)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-MU-RS1-MT-step-if-issue-MU-RS1-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (MU-RS1 (MA-MU MA))))
		  (b1p (issue-MU-RS1? (MA-MU MA) MA)))
	     (no-INST-at-stg-in-trace '(MU RS1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-MU-RS1-MT-step-if-issue-MU-RS1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (RS-valid? (MU-RS1 (MA-MU MA))))
		  (b1p (issue-MU-RS1? (MA-MU MA) MA)))
	     (no-INST-at-stg '(MU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg))))
)

(defthm not-INST-stg-step-inst-MU-RS1-if-not-dispatch-to-MU
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(MU RS1)))
		  (or (not (b1p (dispatch-to-MU? MA)))
		      (not (b1p (select-MU-RS1? (MA-MU MA))))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU RS1))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-INST-execute-INST
				     select-MU-RS1? select-MU-RS0?
				     lift-b-ops dq-stg-p
				     DISPATCH-TO-MU? MU-ready?
				     step-INST-low-level-functions
				     step-INST-DQ-inst)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-MU-RS1-MT-step-if-not-dispatch-to-MU-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(MU RS1) trace)
		  (or (not (b1p (dispatch-to-MU? MA)))
		      (not (b1p (select-MU-RS1? (MA-MU MA))))))
	     (no-INST-at-stg-in-trace '(MU RS1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-MU-RS1-MT-step-if-not-dispatch-to-MU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (MU-RS1 (MA-MU MA)))))
		  (or (not (b1p (dispatch-to-MU? MA)))
		      (not (b1p (select-MU-RS1? (MA-MU MA))))))
	     (no-INST-at-stg '(MU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg)
		  :use (:instance no-inst-at-MU-RS1))))
)

(defthm no-INST-at-MU-RS1-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (RS-valid? (MU-RS1 (step-MU MA sigs))))))
	     (no-inst-at-stg '(MU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-MU step-MU-RS1 lift-b-ops))))

;; Proof of uniq-INST-at-MU-lch1-MT-step
(defthm not-INST-stg-step-INST-MU-lch1-if-issue-MU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(MU RS0)))
		  (b1p (issue-MU-RS0? (MA-MU MA) MA)))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU lch1))))
  :hints (("goal" :use (:instance INST-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-execute-inst
				     step-INST-low-level-functions
				     mu-stg-p lift-b-ops
				     issue-mu-rs0? issue-mu-rs1?
				     MU-RS0-ISSUE-READY?
				     MU-RS1-ISSUE-READY?)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-MU-lch1-if-issue-MU-RS0-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(MU RS0) trace)
		  (b1p (issue-MU-RS0? (MA-MU MA) MA)))
	     (no-inst-at-stg-in-trace '(MU lch1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-MU-lch1-if-issue-MU-RS0-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(MU RS0) trace)
		  (b1p (issue-MU-RS0? (MA-MU MA) MA))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg-in-trace '(MU lch1)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-MU-lch1-if-issue-MU-RS0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (issue-MU-RS0? (MA-MU MA) MA))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg '(MU lch1) (MT-step MT MA sigs)))
  :hints (("goal" :use (:instance UNIQ-INST-AT-MU-RS0-IF-VALID)
		  :in-theory (enable uniq-inst-at-stg issue-MU-RS0?
				     lift-b-ops MU-RS0-ISSUE-READY?))))
)

(defthm not-INST-stg-step-INST-MU-lch1-if-issue-MU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(MU RS1)))
		  (b1p (issue-MU-RS1? (MA-MU MA) MA)))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU lch1))))
  :hints (("goal" :use (:instance INST-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-execute-inst
				     step-INST-low-level-functions
				     mu-stg-p lift-b-ops
				     issue-mu-rs0? issue-mu-rs1?
				     MU-RS0-ISSUE-READY?
				     MU-RS1-ISSUE-READY?)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-MU-lch1-if-issue-MU-RS1-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(MU RS1) trace)
		  (b1p (issue-MU-RS1? (MA-MU MA) MA)))
	     (no-inst-at-stg-in-trace '(MU lch1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-MU-lch1-if-issue-MU-RS1-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(MU RS1) trace)
		  (b1p (issue-MU-RS1? (MA-MU MA) MA))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg-in-trace '(MU lch1)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-MU-lch1-if-issue-MU-RS1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (issue-MU-RS1? (MA-MU MA) MA))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg '(MU lch1) (MT-step MT MA sigs)))
  :hints (("goal" :use (:instance UNIQ-INST-AT-MU-RS1-IF-VALID)
		  :in-theory (enable uniq-inst-at-stg issue-MU-RS1?
				     lift-b-ops MU-RS1-ISSUE-READY?))))
)

(defthm not-INST-stg-step-INST-MU-lch1-if-MU-lch1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(MU lch1)))
		  (b1p (MU-latch1-valid? (MU-lch1 (MA-MU MA))))
		  (b1p (MU-latch2-valid? (MU-lch2 (MA-MU MA))))
		  (not (b1p (CDB-for-MU? MA))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU lch1))))
  :hints (("goal" :use (:instance INST-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-execute-inst
				     step-inst-low-level-functions
				     ISSUE-MU-RS1?
				     issue-mu-rs0? lift-b-ops)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-MU-lch1-if-MU-lch1-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(MU lch1) trace)
		  (b1p (MU-latch1-valid? (MU-lch1 (MA-MU MA))))
		  (b1p (MU-latch2-valid? (MU-lch2 (MA-MU MA))))
		  (not (b1p (CDB-for-MU? MA))))
	     (no-inst-at-stg-in-trace '(MU lch1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-MU-lch1-if-MU-lch1-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(MU lch1) trace)
		  (b1p (MU-latch1-valid? (MU-lch1 (MA-MU MA))))
		  (b1p (MU-latch2-valid? (MU-lch2 (MA-MU MA))))
		  (not (b1p (CDB-for-MU? MA)))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg-in-trace '(MU lch1)
					(step-trace trace MT MA sigs
						    ISA spc smc)))
  :hints (("goal" :in-theory (enable lift-b-ops)))))

(defthm uniq-inst-at-MU-lch1-if-MU-lch1-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (MU-latch1-valid? (MU-lch1 (MA-MU MA))))
		  (b1p (MU-latch2-valid? (MU-lch2 (MA-MU MA))))
		  (not (b1p (CDB-for-MU? MA)))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg '(MU lch1) (MT-step MT MA sigs)))
  :hints (("goal" :use (:instance UNIQ-INST-AT-MU-LCH1-IF-VALID)
		  :in-theory (enable uniq-inst-at-stg))))
)
		       

(defthm uniq-INST-at-MU-lch1-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (MU-latch1-valid? (MU-lch1 (step-MU MA sigs)))))
	     (uniq-inst-at-stg '(MU lch1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-MU step-MU-lch1 lift-b-ops))))

;; Proof of no-INST-at-MU-lch1-MT-step
(defthm not-INST-stg-step-INST-MU-lch1-if-not-issue
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (b1p (CDB-for-MU? MA))
		      (not (b1p (MU-latch2-valid? (MU-lch2 (MA-MU MA))))))
		  (not (b1p (issue-MU-RS0? (MA-MU MA) MA)))
		  (not (b1p (issue-MU-RS1? (MA-MU MA) MA))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU lch1))))
  :Hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-INST-execute-INST
				     step-inst-low-level-functions
				     lift-b-ops)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-INST-at-MU-lch1-MT-step-if-no-issue-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (b1p (CDB-for-MU? MA))
		      (not (b1p (MU-latch2-valid? (MU-lch2 (MA-MU MA))))))
		  (not (b1p (issue-MU-RS0? (MA-MU MA) MA)))
		  (not (b1p (issue-MU-RS1? (MA-MU MA) MA))))
	     (no-INST-at-stg-in-trace '(MU lch1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-INST-at-MU-lch1-MT-step-if-no-issue
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (b1p (CDB-for-MU? MA))
		      (not (b1p (MU-latch2-valid? (MU-lch2 (MA-MU MA))))))
		  (not (b1p (issue-MU-RS0? (MA-MU MA) MA)))
		  (not (b1p (issue-MU-RS1? (MA-MU MA) MA))))
	     (no-INST-at-stg '(MU lch1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-INST-at-stg))))
)

(defthm not-INST-stg-step-INST-MU-lch1-if-not-MU-lch1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(MU lch1)))
		  (not (b1p (issue-MU-RS0? (MA-MU MA) MA)))
		  (not (b1p (issue-MU-RS1? (MA-MU MA) MA))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU lch1))))
  :hints (("goal" :in-theory (e/d (step-INST-execute-INST
				     step-inst-low-level-functions)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))

(encapsulate nil
(local
(defthm no-INST-at-MU-lch1-MT-step-if-lch1-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(MU lch1) trace)
		  (not (b1p (issue-MU-RS0? (MA-MU MA) MA)))
		  (not (b1p (issue-MU-RS1? (MA-MU MA) MA))))
	     (no-INST-at-stg-in-trace '(MU lch1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-INST-at-MU-lch1-MT-step-if-lch1-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (MU-latch1-valid? (MU-lch1 (MA-MU MA)))))
		  (not (b1p (issue-MU-RS0? (MA-MU MA) MA)))
		  (not (b1p (issue-MU-RS1? (MA-MU MA) MA))))
	     (no-INST-at-stg '(MU lch1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg)
		  :use (:instance NO-INST-AT-MU-LCH1))))
)
		  
(defthm no-INST-at-MU-lch1-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (MU-latch1-valid? (MU-lch1 (step-MU MA sigs))))))
	     (no-inst-at-stg '(MU lch1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-MU step-MU-lch1 lift-b-ops))))

;; Proof of uniq-INST-at-MU-lch2-MT-step
(defthm not-INST-stg-step-INST-MU-lch2-if-not-MU-lch1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(MU lch1)))
		  (or (b1p (CDB-for-MU? MA))
		      (not (b1p (MU-latch2-valid? (MU-lch2 (MA-MU MA)))))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU lch2))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-execute-inst lift-b-ops
				     execute-stg-p MU-STG-P
				     step-inst-low-level-functions)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-MU-lch2-MT-step-if-MU-lch1-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(MU lch1) trace)
		  (or (b1p (CDB-for-MU? MA))
		      (not (b1p (MU-latch2-valid? (MU-lch2 (MA-MU MA)))))))
	     (no-inst-at-stg-in-trace '(MU lch2)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-MU-lch2-MT-step-if-MU-lch1-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(MU lch1) trace)
		  (or (b1p (CDB-for-MU? MA))
		      (not (b1p (MU-latch2-valid? (MU-lch2 (MA-MU MA))))))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg-in-trace '(MU lch2)
					(step-trace trace MT MA sigs
						    ISA spc smc)))
  :hints (("goal" :in-theory (enable lift-b-ops)))))

(defthm uniq-inst-at-MU-lch2-MT-step-if-MU-lch1-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (b1p (CDB-for-MU? MA))
		      (not (b1p (MU-latch2-valid? (MU-lch2 (MA-MU MA))))))
		  (b1p (MU-latch1-valid? (MU-lch1 (MA-MU MA))))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg '(MU lch2) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stg)
		  :use (:instance UNIQ-INST-AT-MU-LCH1-IF-VALID))))
)

(defthm not-INST-stg-step-INST-MU-lch2-if-not-MU-lch2
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(MU lch2)))
		  (b1p (MU-latch2-valid? (MU-lch2 (MA-MU MA))))
		  (not (b1p (CDB-for-MU? MA))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU lch2))))
  :hints (("goal" :use (:instance INST-is-at-one-of-the-stages)
		  :in-theory (e/d (step-INST-execute-inst
				     step-INST-low-level-functions
				     execute-stg-p MU-stg-p lift-b-ops)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-MU-lch2-MT-step-if-MU-lch2-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (MU-latch2-valid? (MU-lch2 (MA-MU MA))))
		  (no-inst-at-stg-in-trace '(MU lch2) trace)
		  (not (b1p (CDB-for-MU? MA))))
	     (no-inst-at-stg-in-trace '(MU lch2)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(local
(defthm uniq-inst-at-MU-lch2-MT-step-if-MU-lch2-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(MU lch2) trace)
		  (b1p (MU-latch2-valid? (MU-lch2 (MA-MU MA))))
		  (not (b1p (CDB-for-MU? MA)))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg-in-trace '(MU lch2)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-MU-lch2-MT-step-if-MU-lch2-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (MU-latch2-valid? (MU-lch2 (MA-MU MA))))
		  (not (b1p (CDB-for-MU? MA)))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg '(MU lch2) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stg)
		  :use (:instance UNIQ-INST-AT-MU-LCH2-IF-VALID))))
)

(defthm uniq-INST-at-MU-lch2-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (MU-latch2-valid? (MU-lch2 (step-MU MA sigs)))))
	     (uniq-inst-at-stg '(MU lch2) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-MU step-MU-lch2 lift-b-ops))))

;; Proof of no-INST-at-MU-lch2-MT-step
(encapsulate nil
(local
(defthm no-INST-at-MU-lch2-MT-step-if-not-MU-lch1-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(MU lch1) trace)
		  (or (b1p (CDB-for-MU? MA))
		      (not (b1p (MU-latch2-valid? (MU-lch2 (MA-MU MA)))))))
	     (no-inst-at-stg-in-trace '(MU lch2)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-INST-at-MU-lch2-MT-step-if-not-MU-lch1-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (MU-latch1-valid? (MU-lch1 (MA-MU MA)))))
		  (or (b1p (CDB-for-MU? MA))
		      (not (b1p (MU-latch2-valid? (MU-lch2 (MA-MU MA)))))))
	     (no-inst-at-stg '(MU lch2) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg)
		  :use (:instance no-inst-at-MU-lch1))))
)

(defthm no-INST-at-MU-lch2-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (MU-latch2-valid? (MU-lch2 (step-MU MA sigs))))))
	     (no-inst-at-stg '(MU lch2) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-MU step-MU-lch2 lift-b-ops))))

(defthm no-MU-stg-conflict-preserved
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (no-MU-stg-conflict (MT-step MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable no-MU-stg-conflict))))

;;; Proof of no-LSU-stg-conflict-preserved
;; Proof of uniq-inst-at-LSU-RS0-MT-step
(defthm not-INST-stg-step-inst-LSU-RS0-if-not-LSU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(LSU RS0)))
		  (b1p (LSU-RS-valid? (LSU-RS0 (MA-LSU MA))))
		  (not (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU RS0))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-execute-inst lift-b-ops
				     step-inst-dq-inst dq-stg-p
				     step-inst-low-level-functions
				     DISPATCH-INST? LSU-READY?
				     dispatch-to-LSU? SELECT-LSU-RS0?)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-LSU-RS0-MT-step-if-LSU-RS0-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(LSU RS0) trace)
		  (b1p (LSU-RS-valid? (LSU-RS0 (MA-LSU MA))))
		  (not (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))))
	     (no-inst-at-stg-in-trace '(LSU RS0)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))
  :hints (("goal" :in-theory (enable step-LSU step-LSU-RS0 lift-b-ops)))))

(local
(defthm uniq-inst-at-LSU-RS0-MT-step-if-LSU-RS0-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(LSU RS0) trace)
		  (b1p (LSU-RS-valid? (LSU-RS0 (MA-LSU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))))
	     (uniq-inst-at-stg-in-trace '(LSU RS0)
					(step-trace trace MT MA sigs
						    ISA spc smc)))
  :hints (("goal" :in-theory (enable step-LSU step-LSU-RS0 lift-b-ops)))))

(defthm uniq-inst-at-LSU-RS0-MT-step-if-LSU-RS0-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (LSU-RS-valid? (LSU-RS0 (MA-LSU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))))
	     (uniq-inst-at-stg '(LSU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stg)
		  :use (:instance uniq-inst-at-LSU-RS0-if-valid))))
)

(defthm not-INST-stg-step-INST-LSU-RS0-if-not-DE0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(DQ 0)))
		  (not (b1p (LSU-RS-valid? (LSU-RS0 (MA-LSU MA)))))
		  (b1p (dispatch-to-LSU? MA))
		  (b1p (select-LSU-RS0? (MA-LSU MA))))
	     (not (equal (INST-stg (step-inst i MT MA sigs))
			 '(LSU RS0))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-execute-inst
				     execute-stg-p step-inst-dq-inst
				     dq-stg-p
				     step-inst-low-level-functions)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-LSU-RS0-MT-step-if-dispatch-to-LSU-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(DQ 0) trace)
		  (not (b1p (LSU-RS-valid? (LSU-RS0 (MA-LSU MA)))))
		  (b1p (dispatch-to-LSU? MA))
		  (b1p (select-LSU-RS0? (MA-LSU MA))))
	     (no-inst-at-stg-in-trace '(LSU RS0)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-LSU-RS0-MT-step-if-dispatch-to-LSU-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(DQ 0) trace)
		  (not (b1p (LSU-RS-valid? (LSU-RS0 (MA-LSU MA)))))
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-to-LSU? MA))
		  (b1p (select-LSU-RS0? (MA-LSU MA))))
	     (uniq-inst-at-stg-in-trace '(LSU RS0)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-LSU-RS0-MT-step-if-dispatch-to-LSU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (LSU-RS-valid? (LSU-RS0 (MA-LSU MA)))))
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-to-LSU? MA))
		  (b1p (select-LSU-RS0? (MA-LSU MA))))
	     (uniq-inst-at-stg '(LSU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :use (:instance UNIQ-INST-AT-STG-IF-DQ-DE0-VALID)
		  :in-theory (enable dispatch-to-LSU? lift-b-ops
				     uniq-inst-at-stg DQ-ready-to-LSU?))))
)

(defthm uniq-inst-at-LSU-RS0-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (LSU-RS-valid? (LSU-RS0 (step-LSU MA sigs)))))
	     (uniq-inst-at-stg '(LSU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-LSU step-LSU-RS0 lift-b-ops))))

;; Proof of no-inst-at-LSU-RS0-MT-step
(defthm not-INST-stg-step-INST-LSU-RS0-if-issue-LSU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (LSU-RS-valid? (LSU-RS0 (MA-LSU MA))))
		  (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs)))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU RS0))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-execute-inst
				     step-INST-dq-inst dispatch-inst?
				     dispatch-to-LSU? LSU-READY?
				     lift-b-ops SELECT-LSU-RS0?
				     step-inst-low-level-functions)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-LSU-RS0-MT-step-if-issue-LSU-RS0-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (LSU-RS-valid? (LSU-RS0 (MA-LSU MA))))
		  (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs)))
	     (no-inst-at-stg-in-trace '(LSU RS0)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-LSU-RS0-MT-step-if-issue-LSU-RS0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (LSU-RS-valid? (LSU-RS0 (MA-LSU MA))))
		  (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs)))
	     (no-inst-at-stg '(LSU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg))))
)

(defthm not-INST-stg-step-INST-LSU-RS0-if-not-dispatch
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(LSU RS0)))
		  (or (not (b1p (select-LSU-RS0? (MA-LSU MA))))
		      (not (b1p (dispatch-to-LSU? MA)))))
	     (not (equal (INST-stg (step-inst i MT MA sigs))
			 '(LSU RS0))))
  :hints (("goal" :in-theory (e/d (step-INST-execute-inst
				     step-INST-dq-inst
				     step-INST-low-level-functions
				     DISPATCH-INST? lift-b-ops
				     DQ-stg-p)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))

(encapsulate nil
(local
(defthm no-inst-at-LSU-RS0-MT-step-if-not-LSU-RS-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(LSU RS0) trace)
		  (or (not (b1p (select-LSU-RS0? (MA-LSU MA))))
		      (not (b1p (dispatch-to-LSU? MA)))))
	     (no-inst-at-stg-in-trace '(LSU RS0)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-LSU-RS0-MT-step-if-not-LSU-RS-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (LSU-RS-valid? (LSU-RS0 (MA-LSU MA)))))
		  (or (not (b1p (select-LSU-RS0? (MA-LSU MA))))
		      (not (b1p (dispatch-to-LSU? MA)))))
	     (no-inst-at-stg '(LSU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg)
		  :use (:instance no-inst-at-LSU-RS0))))
)

(defthm no-inst-at-LSU-RS0-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (LSU-RS-valid? (LSU-RS0 (step-LSU MA sigs))))))
	     (no-inst-at-stg '(LSU RS0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-LSU step-LSU-RS0 lift-b-ops))))

;; Proofs of uniq-inst-at-LSU-RS1-MT-step
(defthm not-INST-stg-step-inst-LSU-RS1-if-not-LSU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(LSU RS1)))
		  (b1p (LSU-RS-valid? (LSU-RS1 (MA-LSU MA))))
		  (not (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU RS1))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-execute-inst lift-b-ops
				     step-inst-dq-inst dq-stg-p
				     step-inst-low-level-functions
				     DISPATCH-INST? LSU-READY?
				     dispatch-to-LSU? SELECT-LSU-RS1?
				     SELECT-LSU-RS0?)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-LSU-RS1-MT-step-if-LSU-RS1-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(LSU RS1) trace)
		  (b1p (LSU-RS-valid? (LSU-RS1 (MA-LSU MA))))
		  (not (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))))
	     (no-inst-at-stg-in-trace '(LSU RS1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))
  :hints (("goal" :in-theory (enable step-LSU step-LSU-RS1 lift-b-ops)))))

(local
(defthm uniq-inst-at-LSU-RS1-MT-step-if-LSU-RS1-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(LSU RS1) trace)
		  (b1p (LSU-RS-valid? (LSU-RS1 (MA-LSU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))))
	     (uniq-inst-at-stg-in-trace '(LSU RS1)
					(step-trace trace MT MA sigs
						    ISA spc smc)))
  :hints (("goal" :in-theory (enable step-LSU step-LSU-RS1 lift-b-ops)))))

(defthm uniq-inst-at-LSU-RS1-MT-step-if-LSU-RS1-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (LSU-RS-valid? (LSU-RS1 (MA-LSU MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))))
	     (uniq-inst-at-stg '(LSU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stg)
		  :use (:instance uniq-inst-at-LSU-RS1-if-valid))))
)

(defthm not-INST-stg-step-INST-LSU-RS1-if-not-DE0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(DQ 0)))
		  (not (b1p (LSU-RS-valid? (LSU-RS1 (MA-LSU MA)))))
		  (b1p (dispatch-to-LSU? MA))
		  (b1p (select-LSU-RS1? (MA-LSU MA))))
	     (not (equal (INST-stg (step-inst i MT MA sigs))
			 '(LSU RS1))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-execute-inst
				     execute-stg-p step-inst-dq-inst
				     dq-stg-p
				     step-inst-low-level-functions)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-LSU-RS1-MT-step-if-dispatch-to-LSU-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(DQ 0) trace)
		  (not (b1p (LSU-RS-valid? (LSU-RS1 (MA-LSU MA)))))
		  (b1p (dispatch-to-LSU? MA))
		  (b1p (select-LSU-RS1? (MA-LSU MA))))
	     (no-inst-at-stg-in-trace '(LSU RS1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-LSU-RS1-MT-step-if-dispatch-to-LSU-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(DQ 0) trace)
		  (not (b1p (LSU-RS-valid? (LSU-RS1 (MA-LSU MA)))))
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-to-LSU? MA))
		  (b1p (select-LSU-RS1? (MA-LSU MA))))
	     (uniq-inst-at-stg-in-trace '(LSU RS1)
					(step-trace trace MT MA sigs
						    ISA spc smc)))
  :hints (("goal" :in-theory (enable SELECT-LSU-RS1? SELECT-LSU-RS0?
				     lift-b-ops)))))

(defthm uniq-inst-at-LSU-RS1-MT-step-if-dispatch-to-LSU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (LSU-RS-valid? (LSU-RS1 (MA-LSU MA)))))
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (dispatch-to-LSU? MA))
		  (b1p (select-LSU-RS1? (MA-LSU MA))))
	     (uniq-inst-at-stg '(LSU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :use (:instance UNIQ-INST-AT-STG-IF-DQ-DE0-VALID)
		  :in-theory (enable dispatch-to-LSU? lift-b-ops
				     uniq-inst-at-stg DQ-ready-to-LSU?))))
)

(defthm uniq-inst-at-LSU-RS1-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (LSU-RS-valid? (LSU-RS1 (step-LSU MA sigs)))))
	     (uniq-inst-at-stg '(LSU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-LSU step-LSU-RS1 lift-b-ops))))

;; Proofs of no-inst-at-LSU-RS1-MT-step
(defthm not-INST-stg-step-INST-LSU-RS1-if-issue-LSU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (LSU-RS-valid? (LSU-RS1 (MA-LSU MA))))
		  (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs)))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU RS1))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-execute-inst
				     step-INST-dq-inst dispatch-inst?
				     dispatch-to-LSU? LSU-READY?
				     lift-b-ops SELECT-LSU-RS1?
				     select-LSU-RS0?
				     step-inst-low-level-functions)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-LSU-RS1-MT-step-if-issue-LSU-RS1-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (LSU-RS-valid? (LSU-RS1 (MA-LSU MA))))
		  (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs)))
	     (no-inst-at-stg-in-trace '(LSU RS1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-LSU-RS1-MT-step-if-issue-LSU-RS1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (LSU-RS-valid? (LSU-RS1 (MA-LSU MA))))
		  (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs)))
	     (no-inst-at-stg '(LSU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg))))
)

(defthm not-INST-stg-step-INST-LSU-RS1-if-not-dispatch
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(LSU RS1)))
		  (or (not (b1p (select-LSU-RS1? (MA-LSU MA))))
		      (not (b1p (dispatch-to-LSU? MA)))))
	     (not (equal (INST-stg (step-inst i MT MA sigs))
			 '(LSU RS1))))
  :hints (("goal" :in-theory (e/d (step-INST-execute-inst
				     step-INST-dq-inst
				     step-INST-low-level-functions
				     DISPATCH-INST? lift-b-ops
				     select-LSU-RS1? select-LSU-RS0?
				     DQ-stg-p)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))

(encapsulate nil
(local
(defthm no-inst-at-LSU-RS1-MT-step-if-not-LSU-RS-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(LSU RS1) trace)
		  (or (not (b1p (select-LSU-RS1? (MA-LSU MA))))
		      (not (b1p (dispatch-to-LSU? MA)))))
	     (no-inst-at-stg-in-trace '(LSU RS1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-LSU-RS1-MT-step-if-not-LSU-RS-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (LSU-RS-valid? (LSU-RS1 (MA-LSU MA)))))
		  (or (not (b1p (select-LSU-RS1? (MA-LSU MA))))
		      (not (b1p (dispatch-to-LSU? MA)))))
	     (no-inst-at-stg '(LSU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg)
		  :use (:instance no-inst-at-LSU-RS1))))
)

(defthm no-inst-at-LSU-RS1-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (LSU-RS-valid? (LSU-RS1 (step-LSU MA sigs))))))
	     (no-inst-at-stg '(LSU RS1) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-LSU step-LSU-RS1 lift-b-ops))))

;; Proof of uniq-inst-at-LSU-rbuf-MT-step
(defthm not-INST-stg-step-inst-LSU-rbuf-if-not-LSU-rbuf
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(LSU rbuf)))
		  (b1p (rbuf-valid? (LSU-rbuf (MA-LSU MA))))
		  (not (b1p (release-rbuf? (MA-LSU MA) MA sigs))))
	     (not (equal (INST-stg (step-inst i MT MA sigs))
			 '(LSU rbuf))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-execute-inst
				     ISSUE-LSU-RS0? lift-b-ops
				     ISSUE-LSU-RS1?
				     step-inst-low-level-functions)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-LSU-rbuf-MT-step-if-rbuf-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(LSU rbuf) trace)
		  (b1p (rbuf-valid? (LSU-rbuf (MA-LSU MA))))
		  (not (b1p (release-rbuf? (MA-LSU MA) MA sigs)))
		  (not (b1p (flush-all? MA sigs))))
	     (no-inst-at-stg-in-trace '(LSU rbuf)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-LSU-rbuf-MT-step-if-rbuf-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(LSU rbuf) trace)
		  (b1p (rbuf-valid? (LSU-rbuf (MA-LSU MA))))
		  (not (b1p (release-rbuf? (MA-LSU MA) MA sigs)))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg-in-trace '(LSU rbuf)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-LSU-rbuf-MT-step-if-rbuf-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (rbuf-valid? (LSU-rbuf (MA-LSU MA))))
		  (not (b1p (release-rbuf? (MA-LSU MA) MA sigs)))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg '(LSU rbuf)
			       (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stg)
		  :use (:instance uniq-inst-at-LSU-rbuf-if-valid))))
)

(defthm not-INST-stg-step-INST-LSU-rbuf-if-not-LSU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(LSU RS0)))
		  (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
		  (not (b1p (LSU-RS-ld-st? (LSU-RS0 (MA-LSU MA))))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-execute-inst
				     step-inst-low-level-functions
				     ISSUE-LSU-RS0? ISSUE-LSU-RS1?
				     LSU-RS0-ISSUE-READY?
				     LSU-RS1-ISSUE-READY?
				     lift-b-ops)
				  (inst-is-at-one-of-the-stages)))))
(encapsulate nil
(local
(defthm uniq-inst-at-LSU-rbuf-MT-step-if-issue-RS0-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(LSU RS0) trace)
		  (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
		  (not (b1p (LSU-RS-ld-st? (LSU-RS0 (MA-LSU MA)))))
		  (not (b1p (flush-all? MA sigs))))
	     (no-inst-at-stg-in-trace '(LSU rbuf)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-LSU-rbuf-MT-step-if-issue-RS0-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(LSU RS0) trace)
		  (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
		  (not (b1p (LSU-RS-ld-st? (LSU-RS0 (MA-LSU MA)))))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg-in-trace '(LSU rbuf)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-LSU-rbuf-MT-step-if-issue-RS0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
		  (not (b1p (LSU-RS-ld-st? (LSU-RS0 (MA-LSU MA)))))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg '(LSU rbuf) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stg lift-b-ops
				     issue-LSU-RS0? LSU-RS0-ISSUE-READY?)
		  :use (:instance uniq-inst-at-LSU-RS0-if-valid))))
)
(defthm not-inst-stg-step-inst-LSU-rbuf-if-not-LSU-rs1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(LSU RS1)))
		  (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
		  (not (b1p (LSU-RS-ld-st? (LSU-RS1 (MA-LSU MA)))))
		  (not (b1p (flush-all? MA sigs))))
	     (not (equal (INST-stg (step-inst i MT MA sigs))
			 '(LSU rbuf))))
  :hints (("goal" :in-theory (e/d (step-inst-execute-inst
				     step-inst-low-level-functions
				     ISSUE-LSU-RS0? ISSUE-LSU-RS1?
				     LSU-RS0-ISSUE-READY?
				     LSU-RS1-ISSUE-READY?
				     lift-b-ops)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))

(encapsulate nil
(local
(defthm uniq-inst-at-LSU-rbuf-MT-step-if-issue-RS1-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(LSU RS1) trace)
		  (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
		  (not (b1p (LSU-RS-ld-st? (LSU-RS1 (MA-LSU MA)))))
		  (not (b1p (flush-all? MA sigs))))
	     (no-inst-at-stg-in-trace '(LSU rbuf)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm uniq-inst-at-LSU-rbuf-MT-step-if-issue-RS1-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(LSU RS1) trace)
		  (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
		  (not (b1p (LSU-RS-ld-st? (LSU-RS1 (MA-LSU MA)))))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg-in-trace '(LSU rbuf)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm uniq-inst-at-LSU-rbuf-MT-step-if-issue-RS1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
		  (not (b1p (LSU-RS-ld-st? (LSU-RS1 (MA-LSU MA)))))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stg '(LSU rbuf) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stg lift-b-ops
				     issue-LSU-RS1? LSU-RS1-ISSUE-READY?)
		  :use (:instance uniq-inst-at-LSU-RS1-if-valid))))
)

(defthm uniq-inst-at-LSU-rbuf-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (rbuf-valid? (LSU-rbuf (step-LSU MA sigs)))))
	     (uniq-inst-at-stg '(LSU rbuf) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-LSU step-rbuf lift-b-ops))))

;; Proof of no-inst-at-LSU-rbuf-MT-step
(defthm not-INST-stg-step-INST-LSU-rbuf
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(LSU rbuf)))
		  (or (not (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs)))
		      (b1p (LSU-RS-ld-st? (LSU-RS0 (MA-LSU MA)))))
		  (or (not (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs)))
		      (b1p (LSU-RS-ld-st? (LSU-RS1 (MA-LSU MA))))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))))
  :hints (("goal" :in-theory (e/d (step-inst-execute-inst
				     lift-b-ops
				     step-inst-low-level-functions)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))

	         
(encapsulate nil
(local
(defthm no-inst-at-LSU-rbuf-MT-step-if-rbuf-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(LSU rbuf) trace)
		  (or (not (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs)))
		      (b1p (LSU-RS-ld-st? (LSU-RS0 (MA-LSU MA)))))
		  (or (not (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs)))
		      (b1p (LSU-RS-ld-st? (LSU-RS1 (MA-LSU MA))))))
	     (no-inst-at-stg-in-trace '(LSU rbuf)
			     (step-trace trace MT MA sigs ISA spc smc)))))

(defthm no-inst-at-LSU-rbuf-MT-step-if-rbuf-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (rbuf-valid? (LSU-rbuf (MA-LSU MA)))))
		  (or (not (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs)))
		      (b1p (LSU-RS-ld-st? (LSU-RS0 (MA-LSU MA)))))
		  (or (not (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs)))
		      (b1p (LSU-RS-ld-st? (LSU-RS1 (MA-LSU MA))))))
	     (no-inst-at-stg '(LSU rbuf) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg)
		  :use (:instance no-inst-at-LSU-rbuf))))
)

(defthm not-inst-stg-step-inst-LSU-rbuf-if-release-rbuf
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (release-rbuf? (MA-LSU MA) MA sigs))
		  (or (not (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs)))
		      (b1p (LSU-RS-ld-st? (LSU-RS0 (MA-LSU MA)))))
		  (or (not (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs)))
		      (b1p (LSU-RS-ld-st? (LSU-RS1 (MA-LSU MA))))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))))
  :hints (("goal" :in-theory (e/d (step-inst-execute-inst
				     step-inst-low-level-functions)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))

(encapsulate nil
(local
(defthm no-inst-at-LSU-rbuf-MT-step-if-release-rbuf-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (release-rbuf? (MA-LSU MA) MA sigs))
		  (or (not (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs)))
		      (b1p (LSU-RS-ld-st? (LSU-RS0 (MA-LSU MA)))))
		  (or (not (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs)))
		      (b1p (LSU-RS-ld-st? (LSU-RS1 (MA-LSU MA))))))
	     (no-inst-at-stg-in-trace '(LSU rbuf)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))
  :hints (("goal" :in-theory (enable step-LSU step-rbuf lift-b-ops)))))

(defthm no-inst-at-LSU-rbuf-MT-step-if-release-rbuf
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (release-rbuf? (MA-LSU MA) MA sigs))
		  (or (not (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs)))
		      (b1p (LSU-RS-ld-st? (LSU-RS0 (MA-LSU MA)))))
		  (or (not (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs)))
		      (b1p (LSU-RS-ld-st? (LSU-RS1 (MA-LSU MA))))))
	     (no-inst-at-stg '(LSU rbuf) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg))))
)

(defthm no-inst-at-LSU-rbuf-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (rbuf-valid? (LSU-rbuf (step-LSU MA sigs))))))
	     (no-inst-at-stg '(LSU rbuf) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-LSU step-rbuf lift-b-ops))))

;; Proof of uniq-inst-at-LSU-wbuf0-MT-step
(encapsulate nil
(local
(defthm not-wbuf0-step-inst-if-not-LSU-RS0-help
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (execute-stg-p (INST-stg i))
		  (not (equal (INST-stg i) '(LSU RS0)))
		  (or (not (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
		      (and (b1p (release-wbuf0? (MA-LSU MA) sigs))
			   (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))))
		  (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
		  (b1p (LSU-RS-LD-st? (LSU-RS0 (MA-LSU MA)))))
	     (not (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU wbuf0)
				  (LSU wbuf0 lch)
				  (complete wbuf0) (commit wbuf0)))))
  :hints (("goal" :in-theory (enable step-inst-execute-inst
				     EXECUTE-STG-P LSU-stg-p
				     release-wbuf0? lift-b-ops
				     RELEASE-WBUF0-READY?
				     ISSUE-LSU-RS0? ISSUE-LSU-RS0?
				     LSU-RS0-ISSUE-READY?
				     LSU-RS1-ISSUE-READY?
				     ISSUE-LSU-RS1?
				     step-inst-low-level-functions)))))

(defthm not-wbuf0-step-inst-if-not-LSU-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(LSU RS0)))
		  (or (not (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
		      (and (b1p (release-wbuf0? (MA-LSU MA) sigs))
			   (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))))
		  (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
		  (b1p (LSU-RS-LD-st? (LSU-RS0 (MA-LSU MA)))))
	     (not (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU wbuf0)
				  (LSU wbuf0 lch)
				  (complete wbuf0) (commit wbuf0)))))
  :hints (("goal" :in-theory (e/d (commit-stg-p lift-b-ops
				     step-inst-commit-inst
				     release-wbuf0?
				     complete-stg-p
				     RELEASE-WBUF0-READY?
				     step-inst-complete-inst
				     step-inst-low-level-functions)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))
)

(encapsulate nil
(local
(defthm uniq-inst-at-LSU-wbuf0-MT-step-if-issue-RS0-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(LSU RS0) trace)
		  (or (not (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
		      (and (b1p (release-wbuf0? (MA-LSU MA) sigs))
			   (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))))
		  (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
		  (b1p (LSU-RS-LD-st? (LSU-RS0 (MA-LSU MA)))))
	     (no-inst-at-stgs-in-trace '((LSU wbuf0)
					 (LSU wbuf0 lch)
					 (complete wbuf0) (commit wbuf0))
				       (step-trace trace MT MA sigs
						   ISA spc smc)))
  :hints (("goal" :in-theory (e/d (INST-SELECT-WBUF0? lift-b-ops)
				  (member-equal))))))

(local
(defthm uniq-inst-at-LSU-wbuf0-MT-step-if-issue-RS0-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(LSU RS0) trace)
		  (or (not (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
		      (and (b1p (release-wbuf0? (MA-LSU MA) sigs))
			   (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))))
		  (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
		  (b1p (LSU-RS-LD-st? (LSU-RS0 (MA-LSU MA))))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stgs-in-trace '((LSU wbuf0)
					   (LSU wbuf0 lch)
					   (complete wbuf0) (commit wbuf0))
				(step-trace trace MT MA sigs
					    ISA spc smc)))
  :hints (("goal" :in-theory (e/d (INST-SELECT-WBUF0? lift-b-ops)
				  (member-equal))))))

(defthm uniq-inst-at-LSU-wbuf0-MT-step-if-issue-RS0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (not (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
		      (and (b1p (release-wbuf0? (MA-LSU MA) sigs))
			   (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))))
		  (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
		  (b1p (LSU-RS-LD-st? (LSU-RS0 (MA-LSU MA))))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stgs '((LSU wbuf0) (LSU wbuf0 lch)
				  (complete wbuf0) (commit wbuf0))
				(MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stgs uniq-inst-at-stg
				     ISSUE-LSU-RS0? LSU-RS0-ISSUE-READY?
				     lift-b-ops)
		  :use (:instance uniq-inst-at-LSU-RS0-if-valid))))
)

(encapsulate nil
(local
(defthm not-wbuf0-step-inst-if-not-LSU-RS1-help
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (execute-stg-p (INST-stg i))
		  (not (equal (INST-stg i) '(LSU RS1)))
		  (or (not (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
		      (and (b1p (release-wbuf0? (MA-LSU MA) sigs))
			   (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))))
		  (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
		  (b1p (LSU-RS-LD-st? (LSU-RS1 (MA-LSU MA)))))
	     (not (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU wbuf0)
				  (LSU wbuf0 lch)
				  (complete wbuf0) (commit wbuf0)))))
  :hints (("goal" :in-theory (enable step-inst-execute-inst
				     EXECUTE-STG-P LSU-stg-p
				     release-wbuf0? lift-b-ops
				     RELEASE-WBUF0-READY?
				     ISSUE-LSU-RS0? ISSUE-LSU-RS0?
				     LSU-RS0-ISSUE-READY?
				     LSU-RS1-ISSUE-READY?
				     ISSUE-LSU-RS1?
				     step-inst-low-level-functions)))))

(defthm not-wbuf0-step-inst-if-not-LSU-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(LSU RS1)))
		  (or (not (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
		      (and (b1p (release-wbuf0? (MA-LSU MA) sigs))
			   (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))))
		  (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
		  (b1p (LSU-RS-LD-st? (LSU-RS1 (MA-LSU MA)))))
	     (not (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU wbuf0)
				  (LSU wbuf0 lch)
				  (complete wbuf0) (commit wbuf0)))))
  :hints (("goal" :in-theory (e/d (commit-stg-p lift-b-ops
				     step-inst-commit-inst
				     release-wbuf0?
				     complete-stg-p
				     RELEASE-WBUF0-READY?
				     step-inst-complete-inst
				     step-inst-low-level-functions)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))
)

(encapsulate nil
(local
(defthm uniq-inst-at-LSU-wbuf0-MT-step-if-issue-RS1-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(LSU RS1) trace)
		  (or (not (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
		      (and (b1p (release-wbuf0? (MA-LSU MA) sigs))
			   (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))))
		  (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
		  (b1p (LSU-RS-LD-st? (LSU-RS1 (MA-LSU MA)))))
	     (no-inst-at-stgs-in-trace '((LSU wbuf0)
					 (LSU wbuf0 lch)
					 (complete wbuf0) (commit wbuf0))
				       (step-trace trace MT MA sigs
						   ISA spc smc)))
  :hints (("goal" :in-theory (e/d (INST-SELECT-WBUF0? lift-b-ops)
				  (member-equal))))))

(local
(defthm uniq-inst-at-LSU-wbuf0-MT-step-if-issue-RS1-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(LSU RS1) trace)
		  (or (not (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
		      (and (b1p (release-wbuf0? (MA-LSU MA) sigs))
			   (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))))
		  (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
		  (b1p (LSU-RS-LD-st? (LSU-RS1 (MA-LSU MA))))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stgs-in-trace '((LSU wbuf0)
					   (LSU wbuf0 lch)
					   (complete wbuf0) (commit wbuf0))
					 (step-trace trace MT MA sigs
						     ISA spc smc)))
  :hints (("goal" :in-theory (e/d (INST-SELECT-WBUF0? lift-b-ops)
				  (member-equal))))))

(defthm uniq-inst-at-LSU-wbuf0-MT-step-if-issue-RS1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (not (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
		      (and (b1p (release-wbuf0? (MA-LSU MA) sigs))
			   (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))))
		  (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
		  (b1p (LSU-RS-LD-st? (LSU-RS1 (MA-LSU MA))))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stgs '((LSU wbuf0) (LSU wbuf0 lch)
				  (complete wbuf0) (commit wbuf0))
				(MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stgs uniq-inst-at-stg
				     ISSUE-LSU-RS1? LSU-RS1-ISSUE-READY?
				     lift-b-ops)
		  :use (:instance uniq-inst-at-LSU-RS1-if-valid))))
)

(defthm member-equal-step-INST-wbuf0-if-release-wbuf0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (b1p (release-wbuf0? (MA-LSU MA) sigs)))
	     (iff (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU wbuf0)
				  (LSU wbuf0 lch)
				  (complete wbuf0) (commit wbuf0)))
		  (member-equal (INST-stg i) '((LSU wbuf1)
					       (LSU wbuf1 lch)
					       (complete wbuf1)
					       (commit wbuf1)))))
  :hints (("goal" :in-theory (e/d (lift-b-ops release-wbuf0?
				     check-wbuf1? flush-all?
				     commit-stg-p
				     step-inst-commit-inst
				     step-inst-complete-inst
				     complete-stg-p
				     execute-stg-p LSU-STG-P
				     step-inst-execute-inst
				     INST-SELECT-WBUF0?
				     RELEASE-WBUF0-READY?
				     step-inst-low-level-functions)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))

(encapsulate nil
(local
(defthm uniq-inst-at-LSU-wbuf0-MT-step-if-wbuf1-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (no-inst-at-stgs-in-trace '((LSU wbuf1)
					      (LSU wbuf1 lch)
					      (complete wbuf1)
					      (commit wbuf1))
					    trace)
		  (b1p (release-wbuf0? (MA-LSU MA) sigs)))
	     (no-inst-at-stgs-in-trace '((LSU wbuf0)
					 (LSU wbuf0 lch)
					 (complete wbuf0) (commit wbuf0))
				       (step-trace trace MT MA sigs
						   ISA spc smc)))))

(local
(defthm uniq-inst-at-LSU-wbuf0-MT-step-if-wbuf1-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stgs-in-trace '((LSU wbuf1)
						(LSU wbuf1 lch)
						(complete wbuf1)
						(commit wbuf1))
					      trace)
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (b1p (release-wbuf0? (MA-LSU MA) sigs))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stgs-in-trace '((LSU wbuf0)
					   (LSU wbuf0 lch)
					   (complete wbuf0) (commit wbuf0))
					 (step-trace trace MT MA sigs
						     ISA spc smc)))
  :hints (("goal" :in-theory (e/d () (member-equal))))))

(defthm uniq-inst-at-LSU-wbuf0-MT-step-if-wbuf1-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (b1p (release-wbuf0? (MA-LSU MA) sigs))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stgs '((LSU wbuf0) (LSU wbuf0 lch)
				  (complete wbuf0) (commit wbuf0))
				(MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stgs)
		  :use (:instance UNIQ-INST-AT-LSU-WBUF1-IF-VALID))))
)

(defthm not-step-INST-at-wbuf0-if-not-commit-wbuf1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(commit wbuf1)))
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (b1p (release-wbuf0? (MA-LSU MA) sigs))
		  (b1p (wbuf-commit? (LSU-wbuf1 (MA-LSU MA)))))
	     (not (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU wbuf0)
				  (LSU wbuf0 lch)
				  (complete wbuf0) (commit wbuf0)))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-low-level-functions
				     step-inst-commit-inst
				     step-inst-execute-inst
				     step-inst-complete-inst
				     INST-SELECT-WBUF0? lift-b-ops
				     RELEASE-WBUF0?
				     RELEASE-WBUF0-READY?
				     execute-stg-p LSU-stg-p
				     complete-stg-p
				     commit-stg-p)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm not-uniq-inst-at-commit-wbuf0-help
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (subtrace-p trace MT) (INST-listp trace)
		  (subtrace-after-p i trace MT)
		  (not (committed-p i))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (uniq-inst-at-stg-in-trace '(commit wbuf0) trace)))
  :hints ((when-found-multiple ((EQUAL (INST-STG (CAR TRACE)) '(COMMIT WBUF0))
				(COMMITTED-P I)
				(SUBTRACE-AFTER-P I TRACE MT))
	       (:use  (:instance INST-IN-ORDER-COMMIT-UNCOMMIT
				 (i (car trace)) (j i))))
	  ("goal" :in-theory (disable INST-IN-ORDER-COMMIT-UNCOMMIT)))))

(defthm not-uniq-inst-at-commit-wbuf0-in-trace-cdr-if-car-is-not-commit
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (not (committed-p (car trace)))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (uniq-inst-at-stg-in-trace '(commit wbuf0) (cdr trace))))
  :hints (("goal" :use (:instance not-uniq-inst-at-commit-wbuf0-help
				  (i (car trace)) (trace (cdr trace))))))
)

(encapsulate nil
(local
(defthm not-uniq-inst-at-commit-wbuf1-help
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (subtrace-p trace MT) (INST-listp trace)
		  (subtrace-after-p i trace MT)
		  (not (committed-p i))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (uniq-inst-at-stg-in-trace '(commit wbuf1) trace)))
  :hints ((when-found-multiple ((EQUAL (INST-STG (CAR TRACE)) '(COMMIT WBUF1))
				(COMMITTED-P I)
				(SUBTRACE-AFTER-P I TRACE MT))
	       (:use  (:instance INST-IN-ORDER-COMMIT-UNCOMMIT
				 (i (car trace)) (j i))))
	  ("goal" :in-theory (disable INST-IN-ORDER-COMMIT-UNCOMMIT)))))

(defthm not-uniq-inst-at-commit-wbuf1-in-trace-cdr-if-car-is-not-commit
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (not (committed-p (car trace)))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (uniq-inst-at-stg-in-trace '(commit wbuf1) (cdr trace))))
  :hints (("goal" :use (:instance not-uniq-inst-at-commit-wbuf1-help
				  (i (car trace)) (trace (cdr trace))))))
)

(defthm not-inst-exint-now-car-if-not-uniq-inst-at-commit-wbuf10
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(commit wbuf0) (cdr trace)))
	     (equal (INST-exintr-now? (car trace) MA sigs) 0))
  :hints (("goal" :in-theory (enable INST-exintr-now?))))

(defthm not-inst-cause-jmp-car-if-not-uniq-inst-at-commit-wbuf0
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(commit wbuf0) (cdr trace)))
	     (equal (INST-cause-jmp? (car trace) MT MA sigs) 0))
  :hints (("goal" :in-theory (enable INST-cause-jmp?))))

(defthm not-inst-exint-now-car-if-not-uniq-inst-at-commit-wbuf1
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(commit wbuf1) (cdr trace)))
	     (equal  (INST-exintr-now? (car trace) MA sigs) 0))
  :hints (("goal" :in-theory (enable INST-exintr-now?))))

(defthm not-inst-cause-jmp-car-if-not-uniq-inst-at-commit-wbuf1
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(commit wbuf1) (cdr trace)))
	     (equal (INST-cause-jmp? (car trace) MT MA sigs) 0))
  :hints (("goal" :in-theory (enable INST-cause-jmp?))))

(encapsulate nil
(local
(defthm uniq-inst-at-LSU-wbuf0-MT-step-if-wbuf1-commit-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(commit wbuf1) trace)
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (b1p (release-wbuf0? (MA-LSU MA) sigs))
		  (b1p (wbuf-commit? (LSU-wbuf1 (MA-LSU MA)))))
	     (no-inst-at-stgs-in-trace '((LSU wbuf0)
					 (LSU wbuf0 lch)
					 (complete wbuf0) (commit wbuf0))
				       (step-trace trace MT MA sigs
						   ISA spc smc)))
  :hints (("goal" :in-theory (disable member-equal)))))

(local
(defthm uniq-inst-at-LSU-wbuf0-MT-step-if-wbuf1-commit-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(commit wbuf1) trace)
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (b1p (release-wbuf0? (MA-LSU MA) sigs))
		  (b1p (wbuf-commit? (LSU-wbuf1 (MA-LSU MA)))))
	     (uniq-inst-at-stgs-in-trace '((LSU wbuf0)
					   (LSU wbuf0 lch)
					   (complete wbuf0) (commit wbuf0))
					 (step-trace trace MT MA sigs
						     ISA spc smc)))
  :hints (("goal" :in-theory (disable member-equal)))))

(defthm uniq-inst-at-LSU-wbuf0-MT-step-if-wbuf1-commit
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (b1p (release-wbuf0? (MA-LSU MA) sigs))
		  (b1p (wbuf-commit? (LSU-wbuf1 (MA-LSU MA)))))
	     (uniq-inst-at-stgs '((LSU wbuf0) (LSU wbuf0 lch)
				  (complete wbuf0) (commit wbuf0))
				(MT-step MT MA sigs)))
  :hints (("goal" :use (:instance UNIQ-INST-AT-STG-COMMIT-WBUF1)
		  :in-theory (enable uniq-inst-at-stg
				     uniq-inst-at-stgs))))
)

(defthm member-equal-step-inst-wbuf0-if-not-release-wbuf0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (not (b1p (flush-all? MA sigs))))
	     (iff (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU wbuf0)
				  (LSU wbuf0 lch)
				  (complete wbuf0)
				  (commit wbuf0)))
		  (member-equal (INST-stg i)
				'((LSU wbuf0)
				  (LSU wbuf0 lch)
				  (complete wbuf0)
				  (commit wbuf0)))))
  :hints (("goal" :in-theory (e/d (lift-b-ops release-wbuf0?
				     check-wbuf1? flush-all?
				     commit-stg-p
				     step-inst-commit-inst
				     step-inst-complete-inst
				     complete-stg-p
				     execute-stg-p LSU-STG-P
				     step-inst-execute-inst
				     INST-SELECT-WBUF0?
				     RELEASE-WBUF0-READY?
				     step-inst-low-level-functions)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))

(encapsulate nil
(local
(defthm uniq-inst-at-LSU-wbuf0-MT-step-if-wbuf0-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stgs-in-trace '((LSU wbuf0)
					      (LSU wbuf0 lch)
					      (complete wbuf0)
					      (commit wbuf0))
					      trace)
		  (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (not (b1p (flush-all? MA sigs))))
	     (no-inst-at-stgs-in-trace '((LSU wbuf0)
					 (LSU wbuf0 lch)
					 (complete wbuf0) (commit wbuf0))
				       (step-trace trace MT MA sigs
						   ISA spc smc)))
  :hints (("goal" :in-theory (disable member-equal)))))

(local
(defthm uniq-inst-at-LSU-wbuf0-MT-step-if-wbuf0-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stgs-in-trace '((LSU wbuf0)
						(LSU wbuf0 lch)
						(complete wbuf0)
						(commit wbuf0))
					      trace)
		  (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stgs-in-trace '((LSU wbuf0)
					   (LSU wbuf0 lch)
					   (complete wbuf0) (commit wbuf0))
					 (step-trace trace MT MA sigs
						     ISA spc smc)))
  :hints (("goal" :in-theory (disable member-equal)))))

(defthm uniq-inst-at-LSU-wbuf0-MT-step-if-wbuf0-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stgs '((LSU wbuf0) (LSU wbuf0 lch)
				  (complete wbuf0) (commit wbuf0))
				(MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stgs)
		  :use (:instance UNIQ-INST-AT-LSU-WBUF0-IF-VALID))))
)

(defthm not-member-equal-step-inst-wbuf0-if-release
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(commit wbuf0)))
		  (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (b1p (wbuf-commit? (LSU-wbuf0 (MA-LSU MA)))))
	     (not (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU wbuf0)
				  (LSU wbuf0 lch)
				  (complete wbuf0) (commit wbuf0)))))
  :hints (("goal" :use (inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-low-level-functions
				     commit-stg-p execute-stg-p
				     complete-stg-p
				     LSU-stg-p lift-b-ops
				     INST-SELECT-WBUF0?
				     step-inst-execute-inst
				     step-inst-complete-inst
				     step-inst-commit-inst)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm uniq-inst-at-LSU-wbuf0-MT-step-if-wbuf0-commit-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(commit wbuf0) trace)
		  (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (b1p (wbuf-commit? (LSU-wbuf0 (MA-LSU MA)))))
	     (no-inst-at-stgs-in-trace '((LSU wbuf0)
					 (LSU wbuf0 lch)
					 (complete wbuf0) (commit wbuf0))
				       (step-trace trace MT MA sigs
						   ISA spc smc)))
  :hints (("goal" :in-theory (disable member-equal)))))

(local
(defthm uniq-inst-at-LSU-wbuf0-MT-step-if-wbuf0-commit-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(commit wbuf0) trace)
		  (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (b1p (wbuf-commit? (LSU-wbuf0 (MA-LSU MA)))))
	     (uniq-inst-at-stgs-in-trace '((LSU wbuf0)
					   (LSU wbuf0 lch)
					   (complete wbuf0) (commit wbuf0))
					 (step-trace trace MT MA sigs
						     ISA spc smc)))
  :hints (("goal" :in-theory (disable member-equal)))))

(defthm uniq-inst-at-LSU-wbuf0-MT-step-if-wbuf0-commit
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (b1p (wbuf-commit? (LSU-wbuf0 (MA-LSU MA)))))
	     (uniq-inst-at-stgs '((LSU wbuf0) (LSU wbuf0 lch)
				  (complete wbuf0) (commit wbuf0))
				(MT-step MT MA sigs)))
  :hints (("goal" :use (:instance UNIQ-INST-AT-STG-COMMIT-WBUF0)
		  :in-theory (enable uniq-inst-at-stg uniq-inst-at-stgs))))
)

(defthm uniq-inst-at-LSU-wbuf0-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (wbuf-valid? (LSU-wbuf0 (step-LSU MA sigs)))))
	     (uniq-inst-at-stgs '((LSU wbuf0) (LSU wbuf0 lch)
				  (complete wbuf0) (commit wbuf0))
				(MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-LSU step-wbuf0
				     WBUF1-OUTPUT UPDATE-WBUF0
				     ISSUED-WRITE
				     lift-b-ops))))

;; Proof of no-inst-at-LSU-wbuf0-MT-step
(encapsulate nil
(local
(defthm no-inst-at-stgs-nil-help
    (no-inst-at-stgs-in-trace nil trace)))

(defthm no-inst-at-stgs-nil
    (no-inst-at-stgs nil MT)
  :hints (("goal" :in-theory (enable no-inst-at-stgs))))
)

(encapsulate nil
(local
(defthm uniq-inst-at-stgs-nil-help
    (not (uniq-inst-at-stgs-in-trace nil trace))))

(defthm uniq-inst-at-stgs-nil
    (not (uniq-inst-at-stgs nil MT))
  :hints (("goal" :in-theory (enable uniq-inst-at-stgs))))
)

(encapsulate nil
(local
(defthm no-inst-at-stgs-singleton-help
    (iff (no-inst-at-stgs-in-trace (list stg1) trace)
	 (no-inst-at-stg-in-trace stg1 trace))))

(defthm no-inst-at-stgs-singleton
    (iff (no-inst-at-stgs (list stg1) MT)
	 (no-inst-at-stg stg1 MT))
  :hints (("goal" :in-theory (enable no-inst-at-stgs no-inst-at-stg))))
)

(encapsulate nil
(local
(defthm no-inst-at-stgs-if-no-inst-at-stg-help
    (implies (no-inst-at-stg-in-trace stg1 trace)
	     (iff (no-inst-at-stgs-in-trace (cons stg1 stgs) trace)
		  (no-inst-at-stgs-in-trace stgs trace)))))

(defthm no-inst-at-stgs-if-no-inst-at-stg
    (implies (no-inst-at-stg stg1 MT)
	     (iff (no-inst-at-stgs (cons stg1 stgs) MT)
		  (no-inst-at-stgs stgs MT)))
  :hints (("goal" :in-theory (enable no-inst-at-stgs no-inst-at-stg))))

(local
(defthm uniq-inst-at-stgs-if-no-inst-at-stg-help
    (implies (no-inst-at-stg-in-trace stg1 trace)
	     (iff (uniq-inst-at-stgs-in-trace (cons stg1 stgs) trace)
		  (uniq-inst-at-stgs-in-trace stgs trace)))))

(defthm uniq-inst-at-stgs-if-no-inst-at-stg
    (implies (no-inst-at-stg stg1 MT)
	     (iff (uniq-inst-at-stgs (cons stg1 stgs) MT)
		  (uniq-inst-at-stgs stgs MT)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stgs
				     no-inst-at-stg))))

)  

(defthm  not-member-equal-step-inst-wbuf0-if-no-issue
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
		  (implies (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS0 (MA-LSU MA))))))
		  (implies (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS1 (MA-LSU MA)))))))
	     (not (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU wbuf0)
				  (LSU wbuf0 lch)
				  (complete wbuf0) (commit wbuf0)))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-low-level-functions
				     step-inst-execute-inst
				     step-inst-complete-inst
				     step-inst-commit-inst
				     complete-stg-p
				     execute-stg-p LSU-stg-p
				     commit-stg-p)
				  (inst-is-at-one-of-the-stages)))))
				  
(encapsulate nil
(local
(defthm no-inst-at-LSU-wbuf0-MT-step-if-not-issue-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
		  (implies (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS0 (MA-LSU MA))))))
		  (implies (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS1 (MA-LSU MA)))))))
	     (no-inst-at-stgs-in-trace '((LSU wbuf0)
					 (LSU wbuf0 lch)
					 (complete wbuf0) (commit wbuf0))
				       (step-trace trace MT MA sigs
						   ISA spc smc)))
  :hints (("goal" :in-theory (disable member-equal)))))

(defthm no-inst-at-LSU-wbuf0-MT-step-if-not-issue
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
		  (implies (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS0 (MA-LSU MA))))))
		  (implies (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS1 (MA-LSU MA)))))))
	     (no-inst-at-stgs '((LSU wbuf0) (LSU wbuf0 lch)
				(complete wbuf0) (commit wbuf0))
			      (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stgs))))
)

(defthm  not-member-equal-step-inst-wbuf0-if-not-wbuf1-valid
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (release-wbuf0? (MA-LSU MA) sigs))
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
		  (implies (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS0 (MA-LSU MA))))))
		  (implies (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS1 (MA-LSU MA)))))))
	     (not (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU wbuf0)
				  (LSU wbuf0 lch)
				  (complete wbuf0) (commit wbuf0)))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-low-level-functions
				     step-inst-execute-inst
				     step-inst-complete-inst
				     step-inst-commit-inst
				     release-wbuf0?
				     RELEASE-WBUF0-READY?
				     complete-stg-p lift-b-ops
				     execute-stg-p LSU-stg-p
				     commit-stg-p)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-LSU-wbuf0-MT-step-if-not-wbuf1-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (release-wbuf0? (MA-LSU MA) sigs))
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
		  (implies (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS0 (MA-LSU MA))))))
		  (implies (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS1 (MA-LSU MA)))))))
	     (no-inst-at-stgs-in-trace '((LSU wbuf0)
					 (LSU wbuf0 lch)
					 (complete wbuf0) (commit wbuf0))
				       (step-trace trace MT MA sigs
						   ISA spc smc)))
  :hints (("goal" :in-theory (disable member-equal)))))

(defthm no-inst-at-LSU-wbuf0-MT-step-if-not-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (release-wbuf0? (MA-LSU MA) sigs))
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
		  (implies (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS0 (MA-LSU MA))))))
		  (implies (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS1 (MA-LSU MA)))))))
	     (no-inst-at-stgs '((LSU wbuf0) (LSU wbuf0 lch)
				(complete wbuf0) (commit wbuf0))
			      (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stgs))))
)

(defthm not-INST-stg-step-inst-commit-wbuf0-if-not-wbuf-valid
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(commit wbuf0))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-low-level-functions
				     step-inst-complete-inst complete-stg-p
				     commit-stg-p step-inst-commit-inst)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-commit-wbuf0-MT-step-if-not-wbuf-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))))
	     (no-inst-at-stg-in-trace '(commit wbuf0)
				       (step-trace trace MT MA sigs
						   ISA spc smc)))))    

(defthm no-inst-at-commit-wbuf0-MT-step-if-not-wbuf-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))))
	     (no-inst-at-stg  '(commit wbuf0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg))))
)

(defthm not-equal-commit-wbuf0-if-release-wbuf0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
		  (b1p (release-wbuf0? (MA-LSU MA) sigs)))
	     (not (equal (INST-stg (step-inst i MT MA sigs)) '(commit wbuf0))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-low-level-functions
				     step-inst-commit-inst
				     step-inst-complete-inst
				     complete-stg-p lift-b-ops
				     release-wbuf0? RELEASE-WBUF0-READY?
				     commit-stg-p)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-commit-wbuf0-MT-step-if-release-wbuf0-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
		  (b1p (release-wbuf0? (MA-LSU MA) sigs)))
	     (no-inst-at-stg-in-trace  '(commit wbuf0)
				       (step-trace trace MT MA sigs
						   ISA spc smc)))))

(defthm no-inst-at-commit-wbuf0-MT-step-if-release-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
		  (b1p (release-wbuf0? (MA-LSU MA) sigs)))
	     (no-inst-at-stg  '(commit wbuf0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg))))
)

(defthm not-INST-commit-if-commit-jmp
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (or (equal (INST-stg i) '(complete wbuf0))
		      (equal (INST-stg i) '(complete wbuf1)))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (b1p (commit-jmp? MA))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-commit? i MA) 0))
  :hints (("goal" :in-theory (enable INST-commit? lift-b-ops
				     commit-jmp? equal-b1p-converter)
		  :cases ((b1p (INST-specultv? i))
			  (b1p (INST-modified? i))))))

(defthm not-INST-commit-if-leave-excpt
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (or (equal (INST-stg i) '(complete wbuf0))
		      (equal (INST-stg i) '(complete wbuf1)))
		  (b1p (leave-excpt? MA))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-commit? i MA) 0))
  :hints (("goal" :in-theory (enable INST-commit? lift-b-ops
				     commit-jmp? equal-b1p-converter)
		  :cases ((b1p (INST-specultv? i))
			  (b1p (INST-modified? i))))))

(defthm not-INST-stg-step-INST-commit-wbuf0-if-flush-all
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
		  (not (b1p (wbuf-commit? (LSU-wbuf0 (MA-LSU MA)))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (b1p (flush-all? MA sigs)))
	     (not (equal (INST-stg (step-INST i MT MA sigs)) '(commit wbuf0))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :restrict ((NOT-ROB-EMPTY-IF-INST-IS-EXECUTED ((i i))))
		  :in-theory (e/d (step-inst-low-level-functions
				     step-inst-complete-inst complete-stg-p
				     lift-b-ops flush-all?
				     step-inst-commit-inst commit-stg-p)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm no-inst-at-commit-wbuf0-MT-step-if-not-wbuf0-commit-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
		  (not (b1p (wbuf-commit? (LSU-wbuf0 (MA-LSU MA)))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (b1p (flush-all? MA sigs)))
	     (no-inst-at-stg-in-trace  '(commit wbuf0)
				       (step-trace trace MT MA sigs
						   ISA spc smc)))))

(defthm no-inst-at-commit-wbuf0-MT-step-if-not-wbuf0-commit
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
		  (not (b1p (wbuf-commit? (LSU-wbuf0 (MA-LSU MA)))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (b1p (flush-all? MA sigs)))
	     (no-inst-at-stg  '(commit wbuf0) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stg))))
)

(defthm no-equal-INST-stg-step-inst-commit-wbuf0-if-not-wbuf1-commit
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (not (b1p (wbuf-commit? (LSU-wbuf1 (MA-LSU MA)))))
		  (b1p (release-wbuf0? (MA-LSU MA) sigs))
		  (b1p (flush-all? MA sigs)))
	     (not (equal (INST-stg (step-inst i MT MA sigs))
			 '(commit wbuf0))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :restrict ((NOT-ROB-EMPTY-IF-INST-IS-EXECUTED ((i i))))
		  :in-theory (e/d (step-inst-low-level-functions
				     step-inst-complete-inst complete-stg-p
				     lift-b-ops flush-all?
				     step-inst-commit-inst commit-stg-p)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
 (defthm no-inst-at-commit-wbuf0-MT-step-if-not-wbuf1-commit-help
     (implies (and (inv MT MA)
		   (subtrace-p trace MT) (INST-listp trace)
		   (MAETT-p MT) (MA-state-p MA)
		   (not (MT-CMI-p (MT-step MT MA sigs)))
		   (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		   (not (b1p (wbuf-commit? (LSU-wbuf1 (MA-LSU MA)))))
		   (b1p (release-wbuf0? (MA-LSU MA) sigs))
		   (b1p (flush-all? MA sigs)))
	      (no-inst-at-stg-in-trace  '(commit wbuf0)
					(step-trace trace MT MA sigs
						    ISA spc smc)))))

(defthm no-inst-at-commit-wbuf0-MT-step-if-not-wbuf1-commit
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (not (b1p (wbuf-commit? (LSU-wbuf1 (MA-LSU MA)))))
		  (b1p (release-wbuf0? (MA-LSU MA) sigs))
		  (b1p (flush-all? MA sigs)))
	     (no-inst-at-stg  '(commit wbuf0) (MT-step MT MA sigs)))
  :Hints (("goal" :in-theory (enable no-inst-at-stg))))
)

(defthm no-inst-at-LSU-wbuf0-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (not (b1p (wbuf-valid? (LSU-wbuf0 (step-LSU MA sigs))))))
	     (no-inst-at-stgs '((LSU wbuf0) (LSU wbuf0 lch)
				(complete wbuf0) (commit wbuf0))
			      (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-LSU step-wbuf0
				     WBUF1-OUTPUT UPDATE-WBUF0
				     ISSUED-WRITE
				     lift-b-ops))))

;; Proof of uniq-inst-at-LSU-wbuf1-MT-step
(encapsulate nil
(local
(defthm not-member-equal-step-INST-wbuf1-if-issue-RS0-help
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(LSU RS0)))
		  (execute-stg-p (INST-stg i))
		  (or (and (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
			   (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
			   (not (b1p (release-wbuf0? (MA-LSU MA) sigs))))
		      (and (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
			   (b1p (release-wbuf0? (MA-LSU MA) sigs))))
		  (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
		  (b1p (LSU-RS-LD-ST? (LSU-RS0 (MA-LSU MA)))))
	     (not (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU wbuf1) (LSU wbuf1 lch)
				  (complete wbuf1) (commit wbuf1)))))
  :hints (("goal" :in-theory (e/d (step-inst-low-level-functions
				     step-inst-execute-inst
				     lift-b-ops RELEASE-WBUF0?
				     RELEASE-WBUF0-READY? CHECK-WBUF1?
				     ISSUE-LSU-RS0? ISSUE-LSU-RS1?
				     LSU-RS0-ISSUE-READY?
				     LSU-RS1-ISSUE-READY?
				     INST-SELECT-WBUF0?
				     LSU-stg-p execute-stg-p)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages)))))

(defthm not-member-equal-step-INST-wbuf1-if-issue-RS0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(LSU RS0)))
		  (or (and (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
			   (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
			   (not (b1p (release-wbuf0? (MA-LSU MA) sigs))))
		      (and (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
			   (b1p (release-wbuf0? (MA-LSU MA) sigs))))
		  (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
		  (b1p (LSU-RS-LD-ST? (LSU-RS0 (MA-LSU MA)))))
	     (not (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU wbuf1) (LSU wbuf1 lch)
				  (complete wbuf1) (commit wbuf1)))))
  :hints (("goal" :in-theory (e/d (step-inst-low-level-functions
				     step-inst-commit-inst
				     step-inst-complete-inst
				     lift-b-ops RELEASE-WBUF0?
				     complete-stg-p
				     commit-stg-p)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))
)

(encapsulate nil
(local
(defthm uniq-inst-at-wbuf1-MT-step-if-issue-RS0-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(LSU RS0) trace)
		  (or (and (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
			   (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
			   (not (b1p (release-wbuf0? (MA-LSU MA) sigs))))
		      (and (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
			   (b1p (release-wbuf0? (MA-LSU MA) sigs))))
		  (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
		  (b1p (LSU-RS-LD-ST? (LSU-RS0 (MA-LSU MA)))))
	     (no-inst-at-stgs-in-trace '((LSU wbuf1)
					 (LSU wbuf1 lch)
					 (complete wbuf1) (commit wbuf1))
				       (step-trace trace MT MA sigs
						   ISA spc smc)))
  :hints (("goal" :in-theory (e/d (INST-SELECT-WBUF0? lift-b-ops)
				  (member-equal))))))

(local
(defthm uniq-inst-at-wbuf1-MT-step-if-issue-RS0-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(LSU RS0) trace)
		  (or (and (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
			   (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
			   (not (b1p (release-wbuf0? (MA-LSU MA) sigs))))
		      (and (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
			   (b1p (release-wbuf0? (MA-LSU MA) sigs))))
		  (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
		  (b1p (LSU-RS-LD-ST? (LSU-RS0 (MA-LSU MA))))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stgs-in-trace '((LSU wbuf1)
					   (LSU wbuf1 lch)
					   (complete wbuf1) (commit wbuf1))
					 (step-trace trace MT MA sigs
						     ISA spc smc)))
  :hints (("goal" :in-theory (e/d (INST-SELECT-WBUF0? lift-b-ops)
				  (member-equal))))))

(defthm uniq-inst-at-wbuf1-MT-step-if-issue-RS0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (and (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
			   (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
			   (not (b1p (release-wbuf0? (MA-LSU MA) sigs))))
		      (and (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
			   (b1p (release-wbuf0? (MA-LSU MA) sigs))))
		  (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
		  (b1p (LSU-RS-LD-ST? (LSU-RS0 (MA-LSU MA))))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stgs '((LSU wbuf1) (LSU wbuf1 lch)
				  (complete wbuf1) (commit wbuf1))
				(MT-step MT MA sigs)))
  :hints (("goal" :in-theory (e/d (uniq-inst-at-stgs uniq-inst-at-stg
				     issue-LSU-RS0? LSU-RS0-ISSUE-READY?
				     lift-b-ops)
				  (member-equal))
		  :use (:instance UNIQ-INST-AT-LSU-RS0-IF-VALID))))
)

(encapsulate nil
(local
(defthm not-member-equal-step-INST-wbuf1-if-issue-RS1-help
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(LSU RS1)))
		  (execute-stg-p (INST-stg i))
		  (or (and (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
			   (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
			   (not (b1p (release-wbuf0? (MA-LSU MA) sigs))))
		      (and (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
			   (b1p (release-wbuf0? (MA-LSU MA) sigs))))
		  (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
		  (b1p (LSU-RS-LD-ST? (LSU-RS1 (MA-LSU MA)))))
	     (not (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU wbuf1) (LSU wbuf1 lch)
				  (complete wbuf1) (commit wbuf1)))))
  :hints (("goal" :in-theory (e/d (step-inst-low-level-functions
				     step-inst-execute-inst
				     lift-b-ops RELEASE-WBUF0?
				     RELEASE-WBUF0-READY? CHECK-WBUF1?
				     ISSUE-LSU-RS0? ISSUE-LSU-RS1?
				     LSU-RS0-ISSUE-READY?
				     LSU-RS1-ISSUE-READY?
				     INST-SELECT-WBUF0?
				     LSU-stg-p execute-stg-p)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages)))))

(defthm not-member-equal-step-INST-wbuf1-if-issue-RS1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(LSU RS1)))
		  (or (and (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
			   (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
			   (not (b1p (release-wbuf0? (MA-LSU MA) sigs))))
		      (and (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
			   (b1p (release-wbuf0? (MA-LSU MA) sigs))))
		  (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
		  (b1p (LSU-RS-LD-ST? (LSU-RS1 (MA-LSU MA)))))
	     (not (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU wbuf1) (LSU wbuf1 lch)
				  (complete wbuf1) (commit wbuf1)))))
  :hints (("goal" :in-theory (e/d (step-inst-low-level-functions
				     step-inst-commit-inst
				     step-inst-complete-inst
				     lift-b-ops RELEASE-WBUF0?
				     complete-stg-p
				     commit-stg-p)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))
)

(encapsulate nil
(local
(defthm uniq-inst-at-wbuf1-MT-step-if-issue-RS1-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(LSU RS1) trace)
		  (or (and (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
			   (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
			   (not (b1p (release-wbuf0? (MA-LSU MA) sigs))))
		      (and (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
			   (b1p (release-wbuf0? (MA-LSU MA) sigs))))
		  (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
		  (b1p (LSU-RS-LD-ST? (LSU-RS1 (MA-LSU MA)))))
	     (no-inst-at-stgs-in-trace '((LSU wbuf1)
					 (LSU wbuf1 lch)
					 (complete wbuf1) (commit wbuf1))
				       (step-trace trace MT MA sigs
						   ISA spc smc)))
  :hints (("goal" :in-theory (e/d (INST-SELECT-WBUF0? lift-b-ops)
				  (member-equal))))))

(local
(defthm uniq-inst-at-wbuf1-MT-step-if-issue-RS1-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(LSU RS1) trace)
		  (or (and (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
			   (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
			   (not (b1p (release-wbuf0? (MA-LSU MA) sigs))))
		      (and (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
			   (b1p (release-wbuf0? (MA-LSU MA) sigs))))
		  (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
		  (b1p (LSU-RS-LD-ST? (LSU-RS1 (MA-LSU MA))))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stgs-in-trace '((LSU wbuf1)
					   (LSU wbuf1 lch)
					   (complete wbuf1) (commit wbuf1))
					 (step-trace trace MT MA sigs
						     ISA spc smc)))
  :hints (("goal" :in-theory (e/d (INST-SELECT-WBUF0? lift-b-ops)
				  (member-equal))))))

(defthm uniq-inst-at-wbuf1-MT-step-if-issue-RS1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (and (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
			   (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
			   (not (b1p (release-wbuf0? (MA-LSU MA) sigs))))
		      (and (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
			   (b1p (release-wbuf0? (MA-LSU MA) sigs))))
		  (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
		  (b1p (LSU-RS-LD-ST? (LSU-RS1 (MA-LSU MA))))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stgs '((LSU wbuf1) (LSU wbuf1 lch)
				  (complete wbuf1) (commit wbuf1))
				(MT-step MT MA sigs)))
  :hints (("goal" :in-theory (e/d (uniq-inst-at-stgs uniq-inst-at-stg
				     issue-LSU-RS1? LSU-RS1-ISSUE-READY?
				     lift-b-ops)
				  (member-equal))
		  :use (:instance UNIQ-INST-AT-LSU-RS1-IF-VALID))))
)

(defthm not-member-equal-step-INST-wbuf1-if-not-at-wbuf1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (not (b1p (flush-all? MA sigs))))
	     (iff (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU wbuf1)
				  (LSU wbuf1 lch)
				  (complete wbuf1) (commit wbuf1)))
		  (member-equal (INST-stg i)
				'((LSU wbuf1)
				  (LSU wbuf1 lch)
				  (complete wbuf1)
				  (commit wbuf1)))))
  :hints (("goal" :in-theory (e/d (step-inst-low-level-functions
				     step-inst-commit-inst commit-stg-p
				     complete-stg-p step-inst-complete-inst
				     lift-b-ops flush-all?
				     INST-SELECT-WBUF0? LSU-stg-p
				     ISSUE-LSU-RS0? ISSUE-LSU-RS1?
				     step-inst-execute-inst execute-stg-p)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))
				

(encapsulate nil
(local
(defthm uniq-inst-at-wbuf1-MT-step-if-wbuf1-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stgs-in-trace '((LSU wbuf1)
					      (LSU wbuf1 lch)
					      (complete wbuf1)
					      (commit wbuf1))
					    trace)
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (not (b1p (flush-all? MA sigs))))
	     (no-inst-at-stgs-in-trace '((LSU wbuf1)
					 (LSU wbuf1 lch)
					 (complete wbuf1) (commit wbuf1))
				       (step-trace trace MT MA sigs
						   ISA spc smc)))
  :hints (("goal" :in-theory (disable member-equal)))))

(local
(defthm uniq-inst-at-wbuf1-MT-step-if-wbuf1-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stgs-in-trace '((LSU wbuf1)
						(LSU wbuf1 lch)
						(complete wbuf1)
						(commit wbuf1))
					      trace)
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stgs-in-trace '((LSU wbuf1)
					   (LSU wbuf1 lch)
					   (complete wbuf1) (commit wbuf1))
					 (step-trace trace MT MA sigs
						     ISA spc smc)))
  :hints (("goal" :in-theory (disable member-equal)))))

(defthm uniq-inst-at-wbuf1-MT-step-if-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (not (b1p (flush-all? MA sigs))))
	     (uniq-inst-at-stgs '((LSU wbuf1) (LSU wbuf1 lch)
				  (complete wbuf1) (commit wbuf1))
				(MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stgs)
		  :use (:instance UNIQ-INST-AT-LSU-WBUF1-IF-VALID))))
)

(defthm not-INST-stg-step-inst-wbuf1-if-wbuf1-valid
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)N
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(commit wbuf1)))
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (b1p (wbuf-commit? (LSU-wbuf1 (MA-LSU MA)))))
	     (not (member-equal (INST-stg (step-inst i MT MA sigs))
				'((LSU wbuf1)
				  (LSU wbuf1 lch)
				  (complete wbuf1) (commit wbuf1)))))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (e/d (step-inst-low-level-functions
				     step-inst-commit-inst
				     step-inst-execute-inst
				     step-inst-complete-inst
				     complete-stg-p execute-stg-p
				     LSU-stg-p issue-LSU-RS1?
				     issue-LSU-RS0? lift-b-ops
				     commit-stg-p)
				  (inst-is-at-one-of-the-stages)))))
				  
(encapsulate nil
(local
(defthm uniq-inst-at-wbuf1-MT-step-if-wbuf1-commit-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(commit wbuf1) trace)
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (b1p (wbuf-commit? (LSU-wbuf1 (MA-LSU MA)))))
	     (no-inst-at-stgs-in-trace '((LSU wbuf1)
					 (LSU wbuf1 lch)
					 (complete wbuf1) (commit wbuf1))
				       (step-trace trace MT MA sigs
						   ISA spc smc)))
  :hints (("goal" :in-theory (disable member-equal)))))

(local
(defthm uniq-inst-at-wbuf1-MT-step-if-wbuf1-commit-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(commit wbuf1) trace)
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (b1p (wbuf-commit? (LSU-wbuf1 (MA-LSU MA)))))
	     (uniq-inst-at-stgs-in-trace '((LSU wbuf1)
					   (LSU wbuf1 lch)
					   (complete wbuf1) (commit wbuf1))
					 (step-trace trace MT MA sigs
						     ISA spc smc)))
  :hints (("goal" :in-theory (disable member-equal)))))

(defthm uniq-inst-at-wbuf1-MT-step-if-wbuf1-commit
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (b1p (wbuf-commit? (LSU-wbuf1 (MA-LSU MA)))))
	     (uniq-inst-at-stgs '((LSU wbuf1) (LSU wbuf1 lch)
				  (complete wbuf1) (commit wbuf1))
				(MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stgs
				     uniq-inst-at-stg)
		  :use (:instance UNIQ-INST-AT-STG-COMMIT-WBUF1))))
)

(defthm uniq-inst-at-LSU-wbuf1-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (wbuf-valid? (LSU-wbuf1 (step-LSU MA sigs)))))
	     (uniq-inst-at-stgs '((LSU wbuf1) (LSU wbuf1 lch)
				  (complete wbuf1) (commit wbuf1))
				(MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-LSU step-wbuf1 lift-b-ops
				     update-wbuf1 ISSUED-WRITE))))

;; Proof of no-inst-at-LSU-wbuf1-MT-step
(defthm not-member-equal-step-inst-wbuf1-if-wbuf-empty
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))))
	     (not (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU wbuf1) (LSU wbuf1 lch)
				  (complete wbuf1) (commit wbuf1)))))
  :hints (("goal" :in-theory (e/d (step-inst-low-level-functions
				     commit-stg-p step-inst-commit-inst
				     step-inst-execute-inst execute-stg-p
				     LSU-stg-p lift-b-ops
				     INST-SELECT-WBUF0?
				     complete-stg-p step-inst-complete-inst)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))

(encapsulate nil
(local
(defthm no-inst-at-LSU-wbuf1-MT-step-if-not-wbuf-empty-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))))
	     (no-inst-at-stgs-in-trace '((LSU wbuf1)
					 (LSU wbuf1 lch)
					 (complete wbuf1) (commit wbuf1))
				       (step-trace trace MT MA sigs
						   ISA spc smc)))
  :hints (("goal" :in-theory (disable member-equal)))))

(defthm no-inst-at-LSU-wbuf1-MT-step-if-not-wbuf-empty
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))))
	     (no-inst-at-stgs '((LSU wbuf1) (LSU wbuf1 lch)
				(complete wbuf1) (commit wbuf1))
			      (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable no-inst-at-stgs))))
)

(defthm not-member-equal-step-inst-wbuf1-if-not-issue
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (member-equal (INST-stg i)
				     '((LSU wbuf1)
				       (LSU wbuf1 lch)
				       (complete wbuf1) (commit wbuf1))))
		  (implies (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS0 (MA-LSU MA))))))
		  (implies (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS1 (MA-LSU MA)))))))
	     (not (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU wbuf1)
				  (LSU wbuf1 lch)
				  (complete wbuf1) (commit wbuf1)))))
  :hints (("Goal" :in-theory (e/d (step-inst-low-level-functions
				     step-inst-commit-inst
				     step-inst-execute-inst
				     step-inst-complete-inst
				     complete-stg-p
				     execute-stg-p LSU-stg-p
				     commit-stg-p)
				  (inst-is-at-one-of-the-stages))
		  :use (inst-is-at-one-of-the-stages)))) 

(encapsulate nil
(local
(defthm no-inst-at-LSU-wbuf1-MT-step-if-no-issue-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stgs-in-trace '((LSU wbuf1)
					      (LSU wbuf1 lch)
					      (complete wbuf1)
					      (commit wbuf1))
					    trace)
		  (implies (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS0 (MA-LSU MA))))))
		  (implies (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS1 (MA-LSU MA)))))))
	     (no-inst-at-stgs-in-trace '((LSU wbuf1)
					 (LSU wbuf1 lch)
					 (complete wbuf1) (commit wbuf1))
				       (step-trace trace MT MA sigs
						   ISA spc smc)))
  :hints (("Goal" :in-theory (disable member-equal)))))

(defthm no-inst-at-LSU-wbuf1-MT-step-if-no-issue
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
		  (implies (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS0 (MA-LSU MA))))))
		  (implies (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS1 (MA-LSU MA)))))))
	     (no-inst-at-stgs '((LSU wbuf1) (LSU wbuf1 lch)
				(complete wbuf1) (commit wbuf1))
			      (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable no-inst-at-stgs)
		  :use (:instance no-inst-at-LSU-wbuf1))))
)

(defthm not-member-equal-step-inst-wbuf1-if-release-wbuf0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
		  (b1p (release-wbuf0? (MA-LSU MA) sigs)))
	     (not (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU wbuf1)
				  (LSU wbuf1 lch)
				  (complete wbuf1)
				  (commit wbuf1)))))
  :hints (("Goal" :in-theory (e/d (step-inst-low-level-functions
				     step-inst-commit-inst
				     step-inst-complete-inst
				     step-inst-execute-inst
				     execute-stg-p LSU-stg-p
				     INST-SELECT-WBUF0? lift-b-ops
				     commit-stg-p complete-stg-p)
				  (inst-is-at-one-of-the-stages))
		  :use (inst-is-at-one-of-the-stages))))

(encapsulate nil
(local
(defthm no-inst-at-LSU-wbuf1-MT-step-if-not-wbuf1-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
		  (b1p (release-wbuf0? (MA-LSU MA) sigs)))
	     (no-inst-at-stgs-in-trace '((LSU wbuf1)
					 (LSU wbuf1 lch)
					 (complete wbuf1)
					 (commit wbuf1))
				       (step-trace trace MT MA sigs ISA
						   spc smc)))
  :hints (("Goal" :in-theory (disable member-equal)))))

(defthm no-inst-at-LSU-wbuf1-MT-step-if-not-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
		  (b1p (release-wbuf0? (MA-LSU MA) sigs)))
	     (no-inst-at-stgs '((LSU wbuf1) (LSU wbuf1 lch)
				(complete wbuf1) (commit wbuf1))
			      (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable no-inst-at-stgs)))) 
)

(defthm not-member-equal-step-inst-wbuf1-if-not-issue-release-wbuf0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA)
		  (implies (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS0 (MA-LSU MA))))))
		  (implies (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS1 (MA-LSU MA))))))
		  (b1p (release-wbuf0? (MA-LSU MA) sigs)))
	     (not (member-equal  (INST-stg (step-INST i MT MA sigs))
				 '((LSU wbuf1)
				   (LSU wbuf1 lch)
				   (complete wbuf1) (commit wbuf1)))))
    :hints (("Goal" :in-theory (e/d (step-inst-low-level-functions
				     step-inst-commit-inst
				     step-inst-complete-inst
				     step-inst-execute-inst
				     execute-stg-p LSU-stg-p
				     RELEASE-WBUF0?
				     INST-SELECT-WBUF0? lift-b-ops
				     commit-stg-p complete-stg-p)
				    (inst-is-at-one-of-the-stages))
		  :use (inst-is-at-one-of-the-stages))))

(encapsulate nil
(local
(defthm no-inst-at-LSU-wbuf1-MT-step-if-release-wbuf0-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA)
		  (implies (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS0 (MA-LSU MA))))))
		  (implies (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS1 (MA-LSU MA))))))
		  (b1p (release-wbuf0? (MA-LSU MA) sigs)))
	     (no-inst-at-stgs-in-trace '((LSU wbuf1)
					 (LSU wbuf1 lch)
					 (complete wbuf1) (commit wbuf1))
				       (step-trace trace MT MA sigs
						   ISA spc smc)))
  :hints (("Goal" :in-theory (disable member-equal)))))

(defthm no-inst-at-LSU-wbuf1-MT-step-if-release-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (implies (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS0 (MA-LSU MA))))))
		  (implies (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
			   (not (b1p (LSU-RS-LD-st? (LSU-RS1 (MA-LSU MA))))))
		  (b1p (release-wbuf0? (MA-LSU MA) sigs)))
	     (no-inst-at-stgs '((LSU wbuf1) (LSU wbuf1 lch)
				(complete wbuf1) (commit wbuf1))
			      (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable no-inst-at-stgs))))
)

(defthm not-INST-stg-step-inst-commit-wbuf-if-release-wbuf0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (release-wbuf0? (MA-LSU MA) sigs)))
	     (not (equal (INST-stg (step-INST i MT MA sigs)) '(commit wbuf1))))
  :hints (("Goal" :in-theory (e/d (step-inst-low-level-functions
				   step-inst-commit-inst commit-stg-p
				   lift-b-ops
				   step-inst-complete-inst complete-stg-p)
				  (inst-is-at-one-of-the-stages))
		  :use (inst-is-at-one-of-the-stages))))

(encapsulate nil
(local
(defthm no-inst-at-commit-wbuf1-MT-step-if-release-wbuf0-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (release-wbuf0? (MA-LSU MA) sigs)))
	     (no-inst-at-stg-in-trace '(commit wbuf1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-commit-wbuf1-MT-step-if-release-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (release-wbuf0? (MA-LSU MA) sigs)))
	     (no-inst-at-stg '(commit wbuf1) (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable no-inst-at-stg))))
)

(defthm not-equal-INST-stg-step-inst-commit-wbuf1-if-not-wbuf1-valid
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))))
	     (not (equal (INST-stg (step-INST i MT MA sigs)) '(commit wbuf1))))
  :hints (("Goal" :in-theory (e/d (step-inst-low-level-functions
				     step-inst-commit-inst
				     step-inst-complete-inst
				     commit-stg-p complete-stg-p)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))

(encapsulate nil
(local
(defthm no-inst-at-commit-wbuf1-MT-step-if-not-wbuf1-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))))
	     (no-inst-at-stg-in-trace '(commit wbuf1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-commit-wbuf1-MT-step-if-not-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))))
	     (no-inst-at-stg '(commit wbuf1) (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable no-inst-at-stg))))
)

(defthm not-INST-stg-step-inst-commit-wbuf1-if-flush-all
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (not (b1p (wbuf-commit? (LSU-wbuf1 (MA-LSU MA)))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (b1p (flush-all? MA sigs)))
	     (not (equal (INST-stg (step-INST i MT MA sigs)) '(commit wbuf1))))
  :hints (("Goal" :in-theory (e/d (step-inst-low-level-functions
				     step-inst-commit-inst commit-stg-p
				     step-inst-complete-inst complete-stg-p
				     lift-b-ops FLUSH-ALL?)
				  (inst-is-at-one-of-the-stages))
		  :restrict ((NOT-ROB-EMPTY-IF-INST-IS-EXECUTED ((i i))))
		  :use (inst-is-at-one-of-the-stages))))

(encapsulate nil
(local
(defthm no-inst-at-commit-wbuf1-MT-step-if-not-wbuf1-commit-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (not (b1p (wbuf-commit? (LSU-wbuf1 (MA-LSU MA)))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (b1p (flush-all? MA sigs)))
	     (no-inst-at-stg-in-trace '(commit wbuf1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(defthm no-inst-at-commit-wbuf1-MT-step-if-not-wbuf1-commit
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (not (b1p (release-wbuf0? (MA-LSU MA) sigs)))
		  (not (b1p (wbuf-commit? (LSU-wbuf1 (MA-LSU MA)))))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (b1p (flush-all? MA sigs)))
	     (no-inst-at-stg '(commit wbuf1) (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable no-inst-at-stg))))
)

(defthm no-inst-at-LSU-wbuf1-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (step-LSU MA sigs))))))
	     (no-inst-at-stgs '((LSU wbuf1) (LSU wbuf1 lch)
				(complete wbuf1) (commit wbuf1))
			      (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable step-LSU step-wbuf1 lift-b-ops
				     issued-write UPDATE-WBUF1))))

;; Proof of uniq-inst-at-LSU-lch-MT-step
(defthm not-member-equal-step-INST-LSU-lch-if-check-wbuf0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(LSU wbuf0)))
		  (b1p (check-wbuf0? (MA-LSU MA))))
	     (not (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU lch) (LSU wbuf0 lch)
				  (LSU wbuf1 lch)))))
  :hints (("Goal" :in-theory (e/d (step-inst-low-level-functions
				     step-inst-execute-inst
				     CHECK-WBUF1? lift-b-ops
				     RELEASE-RBUF?
				     execute-stg-p LSU-stg-p)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages)))) 

(encapsulate nil
(local
(defthm uniq-inst-at-LSU-lch-MT-step-if-check-wbuf0-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(LSU wbuf0) trace)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (check-wbuf0? (MA-LSU MA))))
	     (no-inst-at-stgs-in-trace '((LSU lch)
					 (LSU wbuf0 lch)
					 (LSU wbuf1 lch))
				       (step-trace trace MT MA sigs
						   ISA spc smc)))
  :hints (("Goal" :in-theory (disable member-equal)))))

(local
(defthm uniq-inst-at-LSU-lch-MT-step-if-check-wbuf0-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(LSU wbuf0) trace)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (check-wbuf0? (MA-LSU MA))))
	     (uniq-inst-at-stgs-in-trace '((LSU lch)
					   (LSU wbuf0 lch)
					   (LSU wbuf1 lch))
					 (step-trace trace MT MA sigs
						     ISA spc smc)))
  :hints (("Goal" :in-theory (disable member-equal))))) 

(defthm uniq-inst-at-LSU-lch-MT-step-if-check-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (check-wbuf0? (MA-LSU MA))))
	     (uniq-inst-at-stgs '((LSU lch) (LSU wbuf0 lch)
				  (LSU wbuf1 lch))
				(MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable uniq-inst-at-stgs uniq-inst-at-stg
				     check-wbuf0? lift-b-ops)
		  :use (:instance uniq-inst-at-stg-LSU-wbuf0))))
)

(defthm not-member-equal-step-INST-if-check-wbuf1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(LSU wbuf1)))
		  (b1p (check-wbuf1? (MA-LSU MA))))
	     (not (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU lch)
				  (LSU wbuf0 lch)
				  (LSU wbuf1 lch)))))
  :hints (("Goal" :in-theory (e/d (step-inst-low-level-functions
				     step-inst-execute-inst
				     CHECK-WBUF1? lift-b-ops
				     RELEASE-RBUF?
				     execute-stg-p LSU-stg-p)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))

(encapsulate nil
(local
(defthm uniq-inst-at-LSU-lch-MT-step-if-check-wbuf1-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(LSU wbuf1) trace)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (check-wbuf1? (MA-LSU MA))))
	     (no-inst-at-stgs-in-trace '((LSU lch)
					 (LSU wbuf0 lch)
					 (LSU wbuf1 lch))
				       (step-trace trace MT MA sigs
						   ISA spc smc)))
  :hints (("Goal" :in-theory (disable member-equal)))))

(local
(defthm uniq-inst-at-LSU-lch-MT-step-if-check-wbuf1-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(LSU wbuf1) trace)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (check-wbuf1? (MA-LSU MA))))
	     (uniq-inst-at-stgs-in-trace '((LSU lch)
					   (LSU wbuf0 lch)
					   (LSU wbuf1 lch))
					 (step-trace trace MT MA sigs
						     ISA spc smc)))
  :hints (("Goal" :in-theory (disable member-equal))))) 

(defthm uniq-inst-at-LSU-lch-MT-step-if-check-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (check-wbuf1? (MA-LSU MA))))
	     (uniq-inst-at-stgs '((LSU lch) (LSU wbuf0 lch)
				  (LSU wbuf1 lch))
				(MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable uniq-inst-at-stgs uniq-inst-at-stg
				     check-wbuf1? lift-b-ops)
		  :use (:instance uniq-inst-at-stg-LSU-wbuf1))))
)

(defthm not-member-equal-step-inst-LSU-lch-if-release-rbuf
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (INST-stg i) '(LSU rbuf)))
		  (b1p (release-rbuf? (MA-LSU MA) MA sigs)))
	     (not (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU lch)
				  (LSU wbuf0 lch)
				  (LSU wbuf1 lch)))))
  :hints (("Goal" :in-theory (e/d (step-inst-execute-inst
				     step-inst-low-level-functions
				     execute-stg-p LSU-stg-p
				     RELEASE-RBUF? lift-b-ops)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))

(encapsulate nil
(local
(defthm uniq-inst-at-LSU-lch-MT-step-if-release-rbuf-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA)
		  (no-inst-at-stg-in-trace '(LSU rbuf) trace)
		  (b1p (release-rbuf? (MA-LSU MA) MA sigs)))
	     (no-inst-at-stgs-in-trace '((LSU lch)
					 (LSU wbuf0 lch)
					 (LSU wbuf1 lch))
				       (step-trace trace MT MA sigs
						   ISA spc smc)))
  :hints (("Goal" :in-theory (disable member-equal)))))

(local
(defthm uniq-inst-at-LSU-lch-MT-step-if-release-rbuf-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg-in-trace '(LSU rbuf) trace)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (release-rbuf? (MA-LSU MA) MA sigs)))
	     (uniq-inst-at-stgs-in-trace '((LSU lch)
					   (LSU wbuf0 lch)
					   (LSU wbuf1 lch))
					 (step-trace trace MT MA sigs
						     ISA spc smc)))
  :hints (("Goal" :in-theory (disable member-equal)))))

(defthm uniq-inst-at-LSU-lch-MT-step-if-release-rbuf
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (release-rbuf? (MA-LSU MA) MA sigs)))
	     (uniq-inst-at-stgs '((LSU lch) (LSU wbuf0 lch)
				  (LSU wbuf1 lch))
				(MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable uniq-inst-at-stgs uniq-inst-at-stg
				     release-rbuf? lift-b-ops)
		  :use (:instance uniq-inst-at-LSU-rbuf-if-valid))))
)

(defthm uniq-inst-at-LSU-lch-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (LSU-latch-valid? (LSU-lch (step-LSU MA sigs)))))
	     (uniq-inst-at-stgs '((LSU lch) (LSU wbuf0 lch)
				  (LSU wbuf1 lch))
				(MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable step-LSU step-LSU-lch lift-b-ops))))

;; Proof of no-inst-at-LSU-lch-MT-step
(defthm not-member-equal-step-INST-LSU-lch-if-no-check-release
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (check-wbuf0? (MA-LSU MA))))
		  (not (b1p (check-wbuf1? (MA-LSU MA))))
		  (not (b1p (release-rbuf? (MA-LSU MA) MA sigs))))
	     (not (member-equal (INST-stg (step-INST i MT MA sigs))
				'((LSU lch)
				  (LSU wbuf0 lch)
				  (LSU wbuf1 lch)))))
  :hints (("Goal" :in-theory (e/d (step-inst-low-level-functions
				     step-inst-execute-inst)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages)))) 

(encapsulate nil
(local
(defthm no-inst-at-LSU-lch-MT-step-not-check-release-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (check-wbuf0? (MA-LSU MA))))
		  (not (b1p (check-wbuf1? (MA-LSU MA))))
		  (not (b1p (release-rbuf? (MA-LSU MA) MA sigs))))
	     (no-inst-at-stgs-in-trace '((LSU lch)
					 (LSU wbuf0 lch)
					 (LSU wbuf1 lch))
				       (step-trace trace MT MA sigs
						   ISA spc smc)))
  :hints (("Goal" :in-theory (disable member-equal)))))

(defthm no-inst-at-LSU-lch-MT-step-not-check-release
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (check-wbuf0? (MA-LSU MA))))
		  (not (b1p (check-wbuf1? (MA-LSU MA))))
		  (not (b1p (release-rbuf? (MA-LSU MA) MA sigs))))
	     (no-inst-at-stgs '((LSU lch) (LSU wbuf0 lch)
				(LSU wbuf1 lch))
			      (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable no-inst-at-stgs))))
)

(defthm no-inst-at-LSU-lch-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (LSU-latch-valid? (LSU-lch (step-LSU MA sigs))))))
	     (no-inst-at-stgs '((LSU lch) (LSU wbuf0 lch)
				(LSU wbuf1 lch))
			      (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable step-LSU step-LSU-lch lift-b-ops))))

(defthm no-LSU-stg-conflict-preserved
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (not (MT-CMI-p (MT-step MT MA sigs))))
	     (no-LSU-stg-conflict (MT-step MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable no-LSU-stg-conflict))))

(defthm no-stage-conflict-preserved
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (not (MT-CMI-p (MT-step MT MA sigs))))
	     (no-stage-conflict (MT-step MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable no-stage-conflict))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof about no-tag-conflict
;;  Prove that each dispatched instruction has a unique Tomasulo's tag.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof of no-tag-conflict for initial states

(encapsulate nil
(local
(defthm not-robe-valid-if-MA-flushed-help
    (implies (and (b1p (robe-empty-under? idx2 ROB))
		  (integerp idx) (integerp idx2) (< idx idx2) (<= 0 idx))
	     (not (b1p (robe-valid? (nth-robe idx ROB)))))
  :hints (("goal" :in-theory (enable lift-b-ops robe-empty-under?
				     robe-empty?)))))

(defthm not-robe-valid-if-MA-flushed
    (implies (and (b1p (MA-flushed? MA)) (rob-index-p idx))
	     (not (b1p (robe-valid? (nth-robe idx (MA-rob MA))))))
  :hints (("goal" :in-theory (enable MA-flushed? ROB-entries-empty? lift-b-ops
				     rob-index-p unsigned-byte-p))))
)

(defthm no-tag-conflict-at-init-MT
    (implies (and (MA-state-p MA) (rob-index-p idx)
		  (b1p (MA-flushed? MA)))
	     (no-tag-conflict-at idx (init-MT MA) MA))
  :hints (("goal" :in-theory (enable no-tag-conflict-at init-MT
				     NO-inst-of-tag))))

(encapsulate nil
(local
(defthm no-tag-conflict-init-MT-help
    (implies (and (MA-state-p MA) (b1p (MA-flushed? MA))
		  (integerp index) (<= 0 index) (<= index *rob-size*))
	     (no-tag-conflict-under index (init-MT MA) MA))
  :hints (("goal" :in-theory (enable rob-index-p UNSIGNED-BYTE-P)))))

(defthm no-tag-conflict-init-MT
    (implies (and (MA-state-p MA) (b1p (MA-flushed? MA)))
	     (no-tag-conflict (init-MT MA) MA))
  :hints (("goal" :in-theory(enable no-tag-conflict))))
)

; Proof of no-tag-conflict-preserved
(defthm not-execute-stg-p-step-inst-if-not-DE0
    (implies (and (INST-p i)
		  (not (equal (INST-stg i) '(DQ 0)))
		  (not (execute-stg-p (INST-stg i))))
	     (not (execute-stg-p (INST-stg (step-inst i MT MA sigs)))))
  :hints (("Goal" :in-theory (e/d (step-inst-low-level-functions
				     dq-stg-p step-inst-dq-inst)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))

(defthm not-execute-stg-p-step-inst-if-not-dispatch-inst
    (implies (and (INST-p i)
		  (not (b1p (dispatch-inst? MA)))
		  (not (execute-stg-p (INST-stg i))))
	     (not (execute-stg-p (INST-stg (step-inst i MT MA sigs)))))
  :hints (("Goal" :in-theory (e/d (step-inst-low-level-functions
				     dq-stg-p step-inst-dq-inst)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))

(defthm not-complete-stg-p-step-inst-if-not-DE0
    (implies (and (INST-p i)
		  (not (equal (INST-stg i) '(DQ 0)))
		  (not (execute-stg-p (INST-stg i)))
		  (not (complete-stg-p (INST-stg i))))
	     (not (complete-stg-p (INST-stg (step-inst i MT MA sigs)))))
  :hints (("Goal" :in-theory (e/d (step-inst-low-level-functions
				     dq-stg-p step-inst-dq-inst)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))

(defthm not-complete-stg-p-step-inst-if-not-dispatch-inst
    (implies (and (INST-p i)
		  (not (b1p (dispatch-inst? MA)))
		  (not (execute-stg-p (INST-stg i)))
		  (not (complete-stg-p (INST-stg i))))
	     (not (complete-stg-p (INST-stg (step-inst i MT MA sigs)))))
  :hints (("Goal" :in-theory (e/d (step-inst-low-level-functions
				     dq-stg-p step-inst-dq-inst)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))

(defthm complete-stg-p-step-inst-if-not-commit
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (or (not (equal (MT-ROB-head MT) (INST-tag i)))
		      (not (b1p (commit-inst? MA))))
		  (complete-stg-p (INST-stg i))
		  (INST-p i) (MAETT-p MT) (MA-state-p MA))
	     (complete-stg-p (INST-stg (step-inst i MT MA sigs))))
  :hints (("Goal" :in-theory (enable step-inst-low-level-functions
				     INST-commit? lift-b-ops
				     step-inst-complete-inst))))

(defthm INST-tag-step-inst-opener
    (implies (and (INST-p i) (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (INST-tag (step-INST i MT MA sigs))
		    (if (and (equal (INST-stg i) '(DQ 0))
			     (b1p (DISPATCH-INST? MA)))
			(ROB-tail (MA-ROB MA))
			(INST-tag i))))
  :hints (("goal" :in-theory (e/d (step-inst-low-level-functions
				     step-inst-dq-inst dq-stg-p)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))
				  
(defthm robe-valid-MT-ROB-tail-if-dispatch-inst
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (b1p (dispatch-inst? MA)))
	     (equal (robe-valid? (nth-robe (MT-ROB-tail MT) (MA-rob MA)))
		    0))
  :hints (("Goal" :in-theory (enable dispatch-inst? lift-b-ops
				     equal-b1p-converter
				     dispatch-to-IU? 
				     dispatch-to-MU?
				     dispatch-to-BU?
				     dispatch-to-LSU?
				     DQ-ready-no-unit?
				     dispatch-no-unit?))))
		   
(defthm equal-MT-ROB-head-MT-ROB-tail
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (iff (equal (MT-ROB-head MT) (MT-ROB-tail MT))
		  (or (b1p (ROB-full? (MA-ROB MA)))
		      (b1p (ROB-empty? (MA-ROB MA))))))
     :hints (("Goal" :in-theory (enable ROB-full? ROB-empty? lift-b-ops
					lift-b-ops))))

(encapsulate nil
(local
(defthm uniq-inst-of-tag-MT-step-if-robe-valid-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rob-index-p idx)
		  (no-inst-of-tag-in-trace idx trace)
		  (or (not (equal (MT-ROB-head MT) idx))
		      (not (b1p (commit-inst? MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (robe-valid? (nth-robe idx (MA-rob MA)))))
	     (no-inst-of-tag-in-trace idx (step-trace trace MT MA sigs
						      ISA spc smc)))
  :hints (("goal" :induct t
		  :in-theory (enable committed-p dispatched-p)))))

(local
(defthm uniq-inst-of-tag-MT-step-if-robe-valid-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rob-index-p idx)
		  (uniq-inst-of-tag-in-trace idx trace)
		  (or (not (equal (MT-ROB-head MT) idx))
		      (not (b1p (commit-inst? MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (robe-valid? (nth-robe idx (MA-rob MA)))))
	     (uniq-inst-of-tag-in-trace idx (step-trace trace MT MA sigs
							ISA spc smc)))
  :hints (("goal" :induct t
		  :in-theory (enable committed-p dispatched-p)))))

(defthm uniq-inst-of-tag-MT-step-if-robe-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rob-index-p idx)
		  (or (not (equal (MT-ROB-head MT) idx))
		      (not (b1p (commit-inst? MA))))
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (robe-valid? (nth-robe idx (MA-rob MA)))))
	     (uniq-inst-of-tag idx (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable uniq-inst-of-tag)
		  :use (:instance UNIQ-INST-OF-TAG-IF-ROBE-VALID))))

)

(defthm INST-at-DE0-be-dispatched-if-dispatch-inst
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(DQ 0))
		  (b1p (dispatch-inst? MA))
		  (MAETT-p MT) (MA-state-p MA)
		  (not (execute-stg-p (INST-stg (step-inst i MT MA sigs)))))
	     (complete-stg-p (INST-stg (step-inst i MT MA sigs))))
  :hints (("Goal" :in-theory (enable dispatch-inst? lift-b-ops))))

(encapsulate nil
(local
(defthm not-execute-stg-p-step-inst-if-robe-receive-inst
    (implies (and (inv MT MA)
		  (not (equal (INST-stg i) '(DQ 0)))
		  (b1p (robe-receive-inst? (MA-rob MA) (INST-tag i) MA))
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA))
	     (not (execute-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("Goal" :in-theory (e/d (robe-receive-inst? lift-b-ops
				     dispatch-inst? dispatch-no-unit?
				     dispatch-to-IU? dispatch-to-MU?
				     dispatch-to-BU? dispatch-to-LSU?)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages)))))

(local
(defthm not-complete-stg-p-step-inst-if-robe-receive-inst
    (implies (and (inv MT MA)  
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA) 
		  (not (equal (INST-stg i) '(DQ 0)))
		  (b1p (robe-receive-inst? (MA-rob MA) (INST-tag i) MA)))
	      (not (complete-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("Goal" :in-theory (e/d (robe-receive-inst? lift-b-ops
				     dispatch-inst? dispatch-no-unit?
				     dispatch-to-IU? dispatch-to-MU?
				     dispatch-to-BU? dispatch-to-LSU?)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages)))))

(local
(defthm uniq-inst-of-tag-MT-step-if-robe-receive-inst-help-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (rob-index-p idx)
		  (no-inst-at-stg-in-trace '(DQ 0) trace)
		  (b1p (robe-receive-inst? (MA-ROB MA) idx MA)))
	     (no-inst-of-tag-in-trace idx
				       (step-trace trace MT MA sigs
						   ISA spc smc)))
  :hints (("Goal" :in-theory (enable robe-receive-inst? lift-b-ops
				     committed-p dispatched-p)))))

(local
(defthm uniq-inst-of-tag-MT-step-if-robe-receive-inst-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (rob-index-p idx)
		  (not (b1p (flush-all? MA sigs)))
		  (uniq-inst-at-stg-in-trace '(DQ 0) trace)
		  (b1p (robe-receive-inst? (MA-ROB MA) idx MA)))
	     (uniq-inst-of-tag-in-trace idx
					 (step-trace trace MT MA sigs
						     ISA spc smc)))
  :hints (("Goal" :in-theory (enable robe-receive-inst? lift-b-ops
				     committed-p dispatched-p)))))

(defthm uniq-inst-of-tag-MT-step-if-robe-receive-inst
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (rob-index-p idx)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (robe-receive-inst? (MA-ROB MA) idx MA)))
	     (uniq-inst-of-tag idx (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable uniq-inst-of-tag uniq-inst-at-stg
				     robe-receive-inst?
				     lift-b-ops)
		  :use (:instance UNIQ-INST-AT-STG-IF-DQ-DE0-VALID))))
)

(defthm uniq-inst-of-tag-MT-step
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rob-index-p idx)
		  (b1p (robe-valid? (nth-robe idx (step-ROB MA sigs)))))
	     (uniq-inst-of-tag idx (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable step-robe lift-b-ops))))

(defthm not-execute-stg-p-step-inst-if-INST-cause-jmp
    (implies (and (inv MT MA)
		  (INST-p i) (MAETT-p MT) (MA-state-p MA)
		  (b1p (INST-cause-jmp? i MT MA sigs)))
	     (not (execute-stg-p (INST-stg (step-inst i MT MA sigs)))))
  :hints (("Goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (disable inst-is-at-one-of-the-stages))))

(defthm not-complete-stg-p-step-inst-if-INST-cause-jmp
    (implies (and (inv MT MA)
		  (INST-p i) (MAETT-p MT) (MA-state-p MA)
		  (b1p (INST-cause-jmp? i MT MA sigs)))
	     (not (complete-stg-p (INST-stg (step-inst i MT MA sigs)))))
  :hints (("Goal" :use (committed-p-step-inst-if-INST-cause-jmp)
		  :in-theory
		  (disable committed-p-step-inst-if-INST-cause-jmp))))

(encapsulate nil
(local
(defthm no-inst-of-tag-MT-step-if-flush-all-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MT-all-commit-before-trace trace MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (rob-index-p idx)
		  (b1p (flush-all? MA sigs)))
	     (no-inst-of-tag-in-trace idx
				      (step-trace trace MT MA sigs ISA
						  spc smc)))
  :hints (("goal" :in-theory (enable COMMITTED-P dispatched-p))
	  (when-found (MT-ALL-COMMIT-BEFORE-TRACE (CDR TRACE)
                                               MT)
		      (:cases ((committed-p (car trace)))))
	  (when-found (execute-stg-p (INST-stg (step-inst (car trace)
							  MT MA sigs)))
		      (:cases ((committed-p (car trace)))))
	  (when-found (complete-stg-p (INST-stg (step-inst (car trace)
							   MT MA sigs)))
		      (:cases ((committed-p (car trace))))))))

(defthm no-inst-of-tag-MT-step-if-flush-all
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (rob-index-p idx)
		  (b1p (flush-all? MA sigs)))
	     (no-inst-of-tag idx (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable no-inst-of-tag))))
)

(encapsulate nil
(local
(defthm no-inst-of-tag-MT-step-if-not-robe-receive-inst-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rob-index-p idx)
		  (not (b1p (robe-receive-inst? (MA-rob MA) idx MA)))
		  (not (b1p (robe-valid? (nth-robe idx (MA-rob MA))))))
	     (no-inst-of-tag-in-trace idx
				      (step-trace trace MT MA sigs
						  ISA spc smc)))
  :hints (("goal" :in-theory (enable ROBE-RECEIVE-INST? lift-b-ops
				     committed-p dispatched-p))
	  (when-found (EXECUTE-STG-P (INST-STG (STEP-INST (CAR TRACE)
							  MT MA SIGS)))
		      (:cases ((execute-stg-p (INST-stg (car trace))))))
	  (when-found (complete-STG-P (INST-STG (STEP-INST (CAR TRACE)
							  MT MA SIGS)))
		      (:cases ((execute-stg-p (INST-stg (car trace)))
			       (complete-stg-p (INST-stg (car trace)))))))))

(defthm no-inst-of-tag-MT-step-if-not-robe-receive-inst
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rob-index-p idx)
		  (not (b1p (robe-receive-inst? (MA-rob MA) idx MA)))
		  (not (b1p (robe-valid? (nth-robe idx (MA-rob MA))))))
	     (no-inst-of-tag idx (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable no-inst-of-tag))))
)

(defthm not-complete-stg-p-step-inst-if-commit-inst
    (implies (and (inv MT MA)
		  (INST-p i)
		  (b1p (commit-inst? MA))
		  (equal (INST-tag i) (MT-ROB-head MT))
		  (complete-stg-p (INST-stg i))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (complete-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("Goal" :in-theory (enable step-inst-complete-inst
				     inst-commit? lift-b-ops
				     step-inst-low-level-functions))))

(encapsulate nil
(local
(defthm no-inst-at-MT-rob-head-MT-step-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (b1p (commit-inst? MA)))
	     (no-inst-of-tag-in-trace (MT-rob-head MT)
				       (step-trace trace MT MA sigs
						   ISA spc smc)))
    :hints (("goal" :in-theory (enable  lift-b-ops
					committed-p dispatched-p))
	  (when-found (EXECUTE-STG-P (INST-STG (STEP-INST (CAR TRACE)
							  MT MA SIGS)))
		      (:cases ((execute-stg-p (INST-stg (car trace))))))
	  (when-found (complete-STG-P (INST-STG (STEP-INST (CAR TRACE)
							  MT MA SIGS)))
		      (:cases ((execute-stg-p (INST-stg (car trace)))
			       (complete-stg-p (INST-stg (car trace)))))))))

(defthm no-inst-at-MT-rob-head-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (b1p (commit-inst? MA)))
	     (no-inst-of-tag (MT-rob-head MT) (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable no-inst-of-tag))))
)

(defthm no-inst-of-tag-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rob-index-p idx)
		  (not (b1p (robe-valid? (nth-robe idx (step-ROB MA sigs))))))
	     (no-inst-of-tag idx (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable step-robe lift-b-ops))))

; This is the individual case.  The rest is done by induction.
(defthm no-tag-conflict-at-MT-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (rob-index-p idx))
	     (no-tag-conflict-at idx (MT-step MT MA sigs) (MA-step MA sigs)))
  :hints (("Goal" :in-theory (enable no-tag-conflict-at))))

(encapsulate nil 
(local
(defthm no-tag-conflict-preserved-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (integerp n) (<= 0 n)
		  (<= n 8))
	     (no-tag-conflict-under n (MT-step MT MA sigs)
				     (MA-step MA sigs)))
  :hints (("Goal" :in-theory (enable rob-index-p UNSIGNED-BYTE-P)))))

(defthm no-tag-conflict-preserved
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (no-tag-conflict (MT-step MT MA sigs) (MA-step MA sigs)))
  :hints (("Goal" :in-theory (enable NO-TAG-CONFLICT))))
)
