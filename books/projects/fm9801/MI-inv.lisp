;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; MI-inv.lisp
; Author  Jun Sawada, University of Texas at Austin
;
;  This book contains the proof of the invariant property MT-inst-inv.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "ACL2")

(include-book "MA2-lemmas")
(include-book "MAETT-lemmas")
(include-book "modifier")
(include-book "memory-inv")
(deflabel begin-MI-inv)
; This file proves instruction invariants.
; Index
;  Misc Lemmas
;  Proof of MI-INST-inv for initial states 
;  Proof of MI-INST-inv for induction step
;     Proof of INST-inv-fetched-inst
;     Proof of INST-inv-step-INST
;        Proof of IFU-inst-inv
;        Proof of DQ-inst-inv
;        Proof of execute-inst-inv-step-INST
;          Lemmas about the stage of dispatched instructions.
;          Lemmas about dispatch logic
;          Lemmas about register modifiers
;          Lemmas about CDB output
;          Proof of IU-inst-inv-step-INST
;          Proof of MU-inst-inv-step-INST
;          Proof of BU-inst-inv-step-INST
;          Proof of LSU-inst-inv-step-INST
;             LSU-RS0-inst-inv-step-INST
;             LSU-RS1-inst-inv-step-INST
;             LSU-RS1-inst-inv-step-INST
;             LSU-wbuf0-inst-inv-step-INST
;             LSU-rbuf-inst-inv-step-INST
;             LSU-wbuf0-lch-inst-inv-step-INST
;             LSU-wbuf1-lch-inst-inv-step-INST
;               LSU-forward-wbuf-INST-dest-val
;               read-mem-INST-load-addr-INST-dest-val
;             LSU-lch-inst-inv-step-INST
;          Proof of execute-inst-robe-inv-step-INST
;        Proof of complete-inst-inv
;        Proof of commit-inst-inv
;     Proof of INST-inv-exintr-INST
;   MT-INST-inv-lemma
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Misc Lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Several lemmas given below are for the proof of lemmas in this book.
;; They are not intended to be universal lemmas, because the left-hand
;; side terms are not definitely more complex than right-hand side.
;; However, these rewriting rules are useful in the proof of lemmas in
;; this book. 

(in-theory (enable MT-specultv-at-dispatch-off-if-non-specultv-inst-in
		   INST-modified-at-dispatch-off-if-undispatched-inst-in))

(local
(defthm MT-mem-=-MA-mem
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA))
	     (equal (MT-mem MT) (MA-mem MA)))
  :hints (("goal" :in-theory (enable weak-inv inv
				     mem-match-p)))))

(local
(defthm MT-RF-=-MA-RF
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA))
	     (equal (MT-RF MT) (MA-RF MA)))
  :hints (("goal" :in-theory (enable weak-inv inv
				     RF-match-p)))))

(local
(defthm MT-SRF-=-MA-SRF
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA))
	     (equal (MT-SRF MT) (MA-SRF MA)))
  :hints (("goal" :in-theory (enable weak-inv inv
				     SRF-match-p)))))

(in-theory (enable ISA-before-MT-non-nil-trace))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Proof of MI-INST-inv for initial states
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm Mt-INST-inv-init-MT
    (MT-INST-inv (init-MT MA) MA)
  :hints (("goal" :in-theory (enable MT-INST-inv init-MT))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Proof of MI-INST-inv for induction step
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  Proof of Invariants on each instruction
;   Most of the effort in this book is directed for the proof of
;   following lemmas:
;     INST-inv-fetched-inst
;     INST-inv-step-INST
;     INST-inv-exintr-INST
;   And the proof of INST-inv-step-INST takes by far the
;   largest number of lemmas..
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Begin of INST-inv-fetched-inst
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate nil
(local
(defthm ISA-pc-MT-final-ISA-help-help
    (implies (and (equal (trace-pc trace (ISA-pc pre)) (MA-pc MA))
		  (MAETT-p MT)
		  (MA-state-p MA))
	     (equal (ISA-pc (trace-final-ISA trace pre)) (MA-PC MA)))))

(local
(defthm ISA-pc-MT-final-ISA-help
    (implies (and (equal (MT-pc MT) (MA-pc MA))
		  (MAETT-p MT)
		  (MA-state-p MA))
	     (equal (ISA-pc (MT-final-ISA MT)) (MA-PC MA)))
  :hints (("goal" :in-theory (enable MT-final-ISA MT-pc)))))

;; The program counter in a current MA is the same as the final ISA state.
(defthm ISA-pc-MT-final-ISA
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (not (b1p (MT-specultv? MT)))
		  (not (b1p (MT-self-modify? MT))))
	     (equal (ISA-pc (MT-final-ISA MT)) (MA-PC MA)))
  :hints (("goal" :in-theory (enable weak-inv inv
				     MT-specultv-p MT-self-modify-p
				     pc-match-p lift-b-ops)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (MAETT-p MT)
			   (MA-state-p MA)
			   (not (b1p (MT-specultv? MT)))
			   (not (b1p (MT-self-modify? MT))))
		      (equal (MA-PC MA) (ISA-pc (MT-final-ISA MT)))))))
)

(in-theory (disable (:rewrite ISA-pc-MT-final-ISA . 2)))
; Matt K. mod: Modernize theory-invariant call below.
#|
(theory-invariant (not (and (member-equal '(:rewrite ISA-pc-MT-final-ISA . 1)
					  theory)
                            (member-equal '(:rewrite ISA-pc-MT-final-ISA . 2)
                                          theory))))
|#
(theory-invariant (not (and (active-runep '(:rewrite ISA-pc-MT-final-ISA . 1))
                            (active-runep '(:rewrite ISA-pc-MT-final-ISA . 2)))))

;; A landmark lemma.
;; A newly fetched instruction satisfies INST-inv.
(defthm INST-inv-fetched-inst
    (implies (and (MAETT-p MT)
		  (MA-state-p MA)
		  (inv MT MA)
		  (MA-input-p sigs)
		  (b1p (fetch-inst? ma sigs)))
	     (INST-inv (fetched-inst MT (MT-final-ISA MT)
				     (MT-specultv? MT)
				     (MT-self-modify? MT))
		       (MA-step MA sigs)))
  :hints (("Goal" :in-theory (e/d (fetched-inst lift-b-ops MA-step-functions
						inst-inv-def
						MT-def
						bv-eqv-iff-equal
						INST-function-def)
				  (exception-relations
				   incompatible-with-excpt-in-MAETT-lemmas
				   INST-WB-IF-INST-DATA-ACCS-ERROR-DETECTED
				   INST-STORE-INST-SYNC-EXCLUSIVE
				   INST-LSU-IF-INST-STORE
				   INST-IS-AT-ONE-OF-THE-STAGES)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  Proof of INST-inv-step-INST
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; INST-inv-step-INST proves that instruction i preserves instruction
; invariants during the current cycle. 
;
; Proof of INST-inv-step-INST contains a number of landmark lemmas.
;   IFU-inst-inv-step-INST
;   DQ-inst-inv-step-INST
;   execute-inst-inv-step-INST
;   complete-inst-inv-step-INST
;   commit-inst-inv-step-INST
; Each lemma confirms that all instruction invariants are preserved
; for i, depending on the stage of i in the next cycle. 
;  
; Before proceeding on to the proof of each stage dependent lemmas,
; we first prove lemmas about the jump and exceptions.

(in-theory (enable inst-stg-step-inst))

;; We prove MT-jmp-exintr-before-IFU-DQ-INST-if-flush-all.
;; This lemma suggests that flush-all? is asserted only if
;; there is an instruction which flushes the following instructions.
;; Such instructions are either branch instruction or exception related
;; instructions.

;; The following lemmas are for proving the lemma 
;; MT-jmp-exintr-before-IFU-DQ-INST-if-flush-all.
;; The proof sketch is this.  If commit-jmp? is true, there is an
;; instruction stored in ROB at index MT-rob-head.  This instruction at
;; complete stage appears earlier than i in MT, and is an mis-predicted 
;; branch instruction which commits this cycle.  The existence of this
;; instruction negates MT-no-jmp-exintr-before.
(local
(defthm uniq-inst-of-tag-if-context-sync
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (b1p (commit-jmp? MA))
		      (b1p (leave-excpt? MA))
		      (b1p (enter-excpt? MA))))
	     (uniq-inst-of-tag (MT-rob-head MT) MT))
  :hints (("goal" :in-theory (enable commit-jmp? lift-b-ops
				     enter-excpt? leave-excpt?)))))

(local
(defthm complete-inst-of-tag-if-context-sync
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (b1p (commit-jmp? MA))
		      (b1p (leave-excpt? MA))
		      (b1p (enter-excpt? MA))))
	     (complete-stg-p (INST-stg (inst-of-tag (MT-rob-head MT) MT))))
  :hints (("goal" :in-theory (e/d (commit-jmp? lift-b-ops
					       leave-excpt? enter-excpt?
					       committed-p dispatched-p)
				  (inst-of-tag-is-dispatched
				   inst-of-tag-is-not-committed))
		  :use ((:instance inst-of-tag-is-not-committed
				   (rix (MT-rob-head MT)))
			(:instance inst-of-tag-is-dispatched
				   (rix (MT-rob-head MT))))))))

(local
(defthm inst-cause-jmp-inst-of-tag-head
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (or (b1p (commit-jmp? MA))
		      (b1p (leave-excpt? MA))
		      (b1p (enter-excpt? MA))))
	     (b1p (inst-cause-jmp? (inst-of-tag (MT-rob-head MT) MT)
				   MT MA sigs)))
  :hints (("Goal" :in-theory (enable inst-cause-jmp? lift-b-ops)))))

(local
(encapsulate  nil
(local
 (defthm MT-jmp-exintr-before-if-inst-cause-jmp-help
     (implies (and (distinct-member-p trace)
		   (MAETT-p MT) (MA-state-p MA)
		   (member-in-order i j trace)
		   (member-equal i trace)
		   (member-equal j trace)
		   (b1p (inst-cause-jmp? i MT MA sigs)))
	      (not (trace-no-jmp-exintr-before j trace MT MA sigs)))
   :hints (("Goal" :in-theory (enable member-in-order*)))))

; If j follows i in program order, and i causes a jump, 
; (MT-no-jmp-exintr-before j MT..) is false. 
(defthm MT-jmp-exintr-before-if-inst-cause-jmp
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in-order-p i j MT)
		  (INST-in i MT)
		  (INST-in j MT)
		  (b1p (inst-cause-jmp? i MT MA sigs)))
	     (not (MT-no-jmp-exintr-before j MT MA sigs)))
  :hints (("Goal" :in-theory (enable MT-no-jmp-exintr-before
				     inv MT-distinct-inst-p
				     weak-inv
				     INST-in INST-in-order-p)))
  :rule-classes nil) 
))

(local
(defthm MT-jmp-exintr-before-IFU-if-context-sync
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (IFU-stg-p (INST-stg i))
		  (or (b1p (commit-jmp? MA))
		      (b1p (leave-excpt? MA))
		      (b1p (enter-excpt? MA))))
	     (not (MT-no-jmp-exintr-before i MT MA sigs)))
  :hints (("goal" :use (:instance MT-jmp-exintr-before-if-inst-cause-jmp
				  (j i)
				  (i (inst-of-tag (MT-rob-head MT) MT)))))))

(local
(defthm MT-jmp-exintr-before-DQ-if-context-sync
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (DQ-stg-p (INST-stg i))
		  (or (b1p (commit-jmp? MA))
		      (b1p (leave-excpt? MA))
		      (b1p (enter-excpt? MA))))
	     (not (MT-no-jmp-exintr-before i MT MA sigs)))
  :hints (("goal" :use (:instance MT-jmp-exintr-before-if-inst-cause-jmp
				  (j i)
				  (i (inst-of-tag (MT-rob-head MT) MT)))))))

;; If instruction i is in execute-stg, and a context synchronization occurs
;; in the MA,  (MT-no-jmp-exintr-before i MT ..) is false.
(defthm MT-no-jmp-exintr-before-execute-if-context-sync
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (execute-stg-p (INST-stg i))
		  (or (b1p (commit-jmp? MA))
		      (b1p (leave-excpt? MA))
		      (b1p (enter-excpt? MA)))
		  (MAETT-p MT) (MA-state-p MA) (INST-p i))
	     (not (MT-no-jmp-exintr-before i MT MA sigs)))
  :hints (("goal" :use (:instance MT-jmp-exintr-before-if-inst-cause-jmp
				  (j i)
				  (i (inst-of-tag (MT-rob-head MT) MT))))
	  (use-hint-always
	   (:cases ((equal i (INST-OF-TAG (MT-ROB-HEAD MT) MT)))))))

;; This lemma shows that there should be an instruction in MT
;; which causes following instructions to be abandoned, if
;; the MA control line flush-all? is asserted.  
;; Suppose i is an instruction at the IFU stage or in the dispatch queue.  
;; Flush-all? can be asserted if i is externally interrupted.
;; Otherwise, there should be an instruction in MT which precedes i in 
;; program order, and it discards the following instructions including i.
(defthm MT-jmp-exintr-before-IFU-DQ-INST-if-flush-all
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (INST-in i MT)
		  (or (IFU-stg-p (INST-stg i))
		      (DQ-stg-p (INST-stg i)))
		  (b1p (flush-all? MA sigs))
		  (not (b1p (INST-exintr-now? i  MA sigs))))
	     (not (MT-no-jmp-exintr-before i MT MA sigs)))
  :hints (("goal" :in-theory (enable flush-all? INST-exintr-now?
				     ex-intr?
				     lift-b-ops))))

; Suppose i is an instruction in an execution unit. If flush-all? is
; asserted in the MA, branching or other kind of context synchronization is
; caused by a committing instruction which precedes i.
(defthm MT-JMP-EXINTR-BEFORE-execute-INST-IF-FLUSH-ALL
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (execute-stg-p (INST-stg i))
		  (b1p (flush-all? MA sigs))
		  (MAETT-p MT) (MA-state-p MA) (INST-p i) (MA-input-p sigs))
	     (not (MT-no-jmp-exintr-before i MT MA sigs)))
  :hints (("goal" :in-theory (enable flush-all? lift-b-ops))))

(encapsulate nil
(local
(defthm leave-excpt-only-if-commit-inst?
    (implies (and (inv MT MA)
		  (not (b1p (commit-inst? MA)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (leave-excpt? MA) 0))
  :hints (("goal" :in-theory (enable leave-excpt? commit-inst? lift-b-ops
				     equal-b1p-converter)))))

(local
(defthm enter-excpt-only-if-commit-inst?
    (implies (and (inv MT MA)
		  (not (b1p (commit-inst? MA)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (enter-excpt? MA) 0))
  :hints (("goal" :in-theory (enable enter-excpt? commit-inst? lift-b-ops
				     equal-b1p-converter)))))

; The Instruction i at the head of the ROB retires if i is completed, and
; one of lines commit-jmp?, leave-excpt? and enter-excpt? is asserted.
(defthm not-complete-step-inst-INST-at-rob-head
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT)
		  (complete-stg-p (INST-stg (inst-of-tag (MT-rob-head MT) MT)))
		  (or (b1p (commit-jmp? MA))
		      (b1p (leave-excpt? MA))
		      (b1p (enter-excpt? MA))))
	     (not (complete-stg-p
		   (INST-stg (step-INST (inst-of-tag (MT-rob-head MT) MT)
					MT MA sigs)))))
  :hints (("goal" :in-theory (enable step-INST-opener
				     step-INST-low-level-functions
				     INST-commit?
				     lift-b-ops bv-eqv-iff-equal))))
) ;encapsulate							     

(encapsulate nil
(local
(defthm consp-MT-non-commit-trace-help-help
    (implies (uniq-inst-of-tag-in-trace rix trace)
	     (consp (non-commit-trace trace)))))

(local
(defthm consp-MT-non-commit-trace-help
    (implies (uniq-inst-of-tag (MT-rob-head MT) MT)
	     (consp (MT-non-commit-trace MT)))
  :hints (("goal" :in-theory (enable MT-non-commit-trace uniq-inst-of-tag)))))

; If an instruction commits in this cycle, MT-non-commit-trace
; returns non empty list of instructions.
(defthm consp-MT-non-commit-trace
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT)
		  (b1p (commit-inst? MA)))
	     (consp (MT-non-commit-trace MT))))
)

; The first instruction in MT-non-commit-trace has the tag
; (MT-ROB-head MT).
(defthm car-MT-non-commit-trace
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT)
		  (b1p (commit-inst? MA)))
	     (equal (car (MT-non-commit-trace MT))
		    (inst-of-tag (MT-rob-head MT) MT)))
  :hints (("goal" :in-theory
		  (enable (:rewrite car-trace-INST-at-rob-head . 1))
		  :restrict
		  (((:rewrite car-trace-INST-at-rob-head . 1)
		    ((trace (MT-non-commit-trace MT))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; From here we prove the invariants at each stage. 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; The proof of IFU-inst-inv
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; IFU-inst-inv is preserved for instruction i, if i is in IFU-stg in 
; the current cycle, and will be in IFU-stg in the next cycle.
(defthm IFU-inst-inv-step-INST-IFU 
    (implies (and (IFU-INST-inv I MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (IFU-stg-p (INST-stg i))
		  (IFU-stg-p (INST-stg (step-INST I MT MA sigs))))
	     (IFU-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable IFU-inst-inv
				     step-INST-low-level-functions
				     MA-step-functions
				     lift-b-ops
				     INST-function-def
				     step-INST-opener))))

; A landmark lemma
; IFU-inst-inv will hold for instruction i, if it is in IFU-stg in the
; next cycle, given that i is not externally interrupted during this cycle,
; and i is not abandoned by a jump or interrupts by a preceding instruction.
(defthm IFU-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (not (b1p (INST-exintr-now? i MA sigs)))
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (IFU-stg-p (INST-stg (step-INST I MT MA sigs))))
	     (IFU-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("Goal" :use ((:instance INST-is-at-one-of-the-stages))
		  :in-theory (e/d (INST-inv)
				  (INST-INV-IF-INST-IN)))
	  ("Goal'" :cases ((b1p (flush-all? MA sigs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;   Proof of DQ-inst-inv
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Lemmas to case split depending on the value of MT-DQ-len.
(defthm MT-DQ-len-0-to-4
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (or (equal (MT-DQ-len MT) 0) (equal (MT-DQ-len MT) 1)
		 (equal (MT-DQ-len MT) 2) (equal (MT-DQ-len MT) 3)
		 (equal (MT-DQ-len MT) 4)))
  :hints (("Goal" :in-theory (enable inv misc-inv)))
  :rule-classes nil)

; New-dq-stage returns the dispatch queue stage where a decoded instruction
; is pushed.  It is one of the four stages in the dispatch queue.
(defthm NEW-DQ-stage-one-of-them
    (or (equal (NEW-dq-stage MT MA) '(DQ 0))
	(equal (NEW-dq-stage MT MA) '(DQ 1))
	(equal (NEW-dq-stage MT MA) '(DQ 2))
	(equal (NEW-dq-stage MT MA) '(DQ 3)))
  :hints (("goal" :in-theory (enable NEW-dq-stage)))
  :rule-classes nil)

;;; Following lemmas determines the value of DE-valid? field of each entry
;;; in the dispatching queue.
(defthm DE-valid-DQ-DE0-by-MT-DQ-len
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (DE-valid? (DQ-DE0 (MA-DQ MA)))
		    (if (<= (MT-DQ-len MT) 0) 0 1)))
  :hints (("goal" :in-theory (enable inv misc-inv
				     equal-b1p-converter
				     correct-entries-in-DQ-p)))
  :rule-classes
  ((:rewrite :corollary
	     (implies (and (inv MT MA)
			   (MAETT-p MT) (MA-state-p MA)
			   (<= (MT-DQ-len MT) 0))
		      (equal (DE-valid? (DQ-DE0 (MA-DQ MA))) 0)))
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (MAETT-p MT) (MA-state-p MA)
			   (> (MT-DQ-len MT) 0))
		      (equal (DE-valid? (DQ-DE0 (MA-DQ MA))) 1)))))

(defthm DE-valid-DQ-DE1-by-MT-DQ-len
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (DE-valid? (DQ-DE1 (MA-DQ MA)))
		    (if (<= (MT-DQ-len MT) 1) 0 1)))
  :hints (("goal" :in-theory (enable inv misc-inv
				     equal-b1p-converter
				     correct-entries-in-DQ-p)))
  :rule-classes
  ((:rewrite :corollary
	     (implies (and (inv MT MA)
			   (MAETT-p MT) (MA-state-p MA)
			   (<= (MT-DQ-len MT) 1))
		      (equal (DE-valid? (DQ-DE1 (MA-DQ MA))) 0)))
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (MAETT-p MT) (MA-state-p MA)
			   (> (MT-DQ-len MT) 1))
		      (equal (DE-valid? (DQ-DE1 (MA-DQ MA))) 1)))))

(defthm DE-valid-DQ-DE2-by-MT-DQ-len
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (DE-valid? (DQ-DE2 (MA-DQ MA)))
		    (if (<= (MT-DQ-len MT) 2) 0 1)))
  :hints (("goal" :in-theory (enable inv misc-inv
				     equal-b1p-converter
				     correct-entries-in-DQ-p)))
  :rule-classes
  ((:rewrite :corollary
	     (implies (and (inv MT MA)
			   (MAETT-p MT) (MA-state-p MA)
			   (<= (MT-DQ-len MT) 2))
		      (equal (DE-valid? (DQ-DE2 (MA-DQ MA))) 0)))
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (MAETT-p MT) (MA-state-p MA)
			   (> (MT-DQ-len MT) 2))
		      (equal (DE-valid? (DQ-DE2 (MA-DQ MA))) 1)))))

(defthm DE-valid-DQ-DE3-by-MT-DQ-len
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (DE-valid? (DQ-DE3 (MA-DQ MA)))
		    (if (<= (MT-DQ-len MT) 3) 0 1)))
  :hints (("goal" :in-theory (enable inv misc-inv
				     equal-b1p-converter
				     correct-entries-in-DQ-p)))
  :rule-classes
  ((:rewrite :corollary
	     (implies (and (inv MT MA)
			   (MAETT-p MT) (MA-state-p MA)
			   (<= (MT-DQ-len MT) 3))
		      (equal (DE-valid? (DQ-DE3 (MA-DQ MA))) 0)))
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (MAETT-p MT) (MA-state-p MA)
			   (> (MT-DQ-len MT) 3))
		      (equal (DE-valid? (DQ-DE3 (MA-DQ MA))) 1)))))

; DQ-full? is true if the dispatch queue length is larger than 3.
(defthm DQ-full-by-MT-DQ-len
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (DQ-full? (MA-DQ MA))
		    (if (<= (MT-DQ-len MT) 3) 0 1)))
  :hints (("goal" :in-theory (enable inv misc-inv
				     DQ-full?
				     equal-b1p-converter
				     correct-entries-in-DQ-p)))
  :rule-classes
  ((:rewrite :corollary
	     (implies (and (inv MT MA)
			   (MAETT-p MT) (MA-state-p MA)
			   (<= (MT-DQ-len MT) 3))
		      (equal (DQ-full? (MA-DQ MA)) 0)))
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (MAETT-p MT) (MA-state-p MA)
			   (> (MT-DQ-len MT) 3))
		      (equal (DQ-full? (MA-DQ MA)) 1)))))

; decode-illegal-inst-0 shows that Opcode 0 is not an illegal instruction.
; This is an ad-hoc lemma for the proofs in this book.
(local
(defthm decode-illegal-inst-0
    (equal (decode-illegal-inst? 0 su ra) 0)
  :hints (("goal" :in-theory  (enable decode-illegal-inst?)))))

; IFU-branch-target calculates the branching destination for
; instruction at IFU. INST-br-target calculates the branching
; destination for instruction i.  If an instruction i is at IFU-stg,
; these two functions return the same value.
(defthm IFU-branch-target=INST-br-target
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (INST-in i MT)
		  (IFU-stg-p (INST-stg i))
		  (not (INST-fetch-error-detected-p I))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (equal (IFU-branch-target (MA-IFU MA))
		    (INST-br-target i)))
  :hints (("goal" :in-theory (enable IFU-branch-target INST-br-target
				     INST-pc))))
 
;; MA-SRF-su-=-INST-su shows the Supervisor/User mode is correct.
;; Imagine a non-retired instruction i.  Suppose i is not a speculatively
;; executed instruction, and not retired.  The mode in which i should be
;; executed is represented by (INST-su i).  The current mode in MA is
;; determined by  (SRF-su (MA-SRF MA)).  These two values should
;; be identical.

;; A sketch of the proof of MA-SRF-su-=-INST-su is as follows.
;; If i is an instruction which is not retired, and whose specultv? flag
;; is not on, then i appears in MT-non-retire-trace and
;; no partially executed instruction changes the su bit.
;; So the su bits are the same in the pre-ISA states of both i and the first
;; instruction in MT-non-retire-trace.
;; 

(local
(encapsulate nil
(local
(defthm MA-su-car-MT-non-retire-trace-=-INST-su-help-induction
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-listp trace)
		  (subtrace-p trace MT)
		  (trace-correct-speculation-p trace)
		  (no-commit-inst-p trace)
		  (member-equal i trace)
		  (not (b1p (inst-specultv? i))))
	     (equal (INST-su (car trace)) (INST-su i)))
  :hints (("Goal" :in-theory
		  (enable
		   ISA-before INST-su
		   INST-start-specultv?
		   committed-p
		   lift-b-ops
		   flushed-p
		   INST-exintr-INST-in-if-not-retired
		   inst-specultv-is-not-member-equal-to-trace-all-specultv)
		  :induct t)
	  (when-found (SRF-SU (ISA-SRF (INST-PRE-ISA (CAR (CDR TRACE)))))
		      (:cases ((consp (cdr trace))))))
  :rule-classes nil))

(local
(defthm MA-su-car-MT-non-retire-trace-=-INST-su-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-listp trace)
		  (subtrace-p trace MT)
		  (no-commit-inst-p trace)
		  (trace-correct-speculation-p trace)
		  (member-equal i trace)
		  (not (b1p (inst-specultv? i))))
	     (equal (SRF-su (ISA-SRF (ISA-before trace MT)))
		    (INST-su i)))
  :hints (("goal" :cases ((endp trace))
		  :in-theory (enable INST-su)
		  :do-not-induct t)
	  ("subgoal 2"
	   :use (:instance
		 MA-su-car-MT-non-retire-trace-=-INST-su-help-induction)))
  :rule-classes nil))

;  Supervisor/User mode of the ISA state before the first non-committed
;  instruction in MT is equal to that of i, which is an non-speculative
;  instruction in MT. 
(defthm MA-su-car-MT-non-retire-trace-=-INST-su
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (inst-in i MT) (INST-p i)
		  (not (retire-stg-p (INST-stg i)))
		  (not (commit-stg-p (INST-stg i)))
		  (not (b1p (inst-specultv? i))))
	     (equal (SRF-su (ISA-SRF (ISA-before (MT-non-commit-trace MT) MT)))
		    (INST-su i)))
  :hints (("goal" :use (:instance MA-su-car-MT-non-retire-trace-=-INST-su-help
				  (trace (MT-non-commit-trace MT)))))
  :rule-classes nil)
))

;; Supervisor/User mode in the current MA state and the pre-ISA of i
;; are the same.
(defthm MA-SRF-su-=-INST-su
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (inst-in i MT) (INST-p i)
		  (not (retire-stg-p (INST-stg i)))
		  (not (commit-stg-p (INST-stg i)))
		  (not (b1p (inst-specultv? i))))
	     (equal (SRF-su (MA-SRF MA))
		    (INST-su i)))
  :hints (("goal" :use (:instance MA-su-car-MT-non-retire-trace-=-INST-su)
		  :in-theory (enable INST-su))))

; DQ0-inst-inv is true for i in the next cycle, if i is in IFU-stg and
; advances to (DQ 0) in this cycle.  Similar lemmas follow.
(defthm DQ0-inst-inv-step-INST-IFU 
    (implies (and (inv MT MA)
		  (IFU-INST-inv I MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (INST-in i MT)
		  (not (b1p (flush-all? MA sigs)))
		  (IFU-stg-p (INST-stg i))
		  (equal (INST-stg (step-INST I MT MA sigs)) '(DQ 0)))
	     (DQ0-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory
		  (e/d (lift-b-ops step-DE0 DE1-out DE2-out DE3-out
			   IFU-INST-inv INST-opcode decode-output INST-su
			   INST-pc INST-ra INST-decode-error?
			   INST-fetch-error-detected-p-iff-INST-fetch-error?
			   INST-decode-error-detected-p-iff-INST-decode-error?
			   exception-relations NEW-dq-stage INST-excpt-flags
			   DQ0-inst-inv)
		       (MT-DQ-len-lemmas))
		  :cases ((b1p (DISPATCH-INST? MA))))
	  (use-hint-always (:cases ((b1p (INST-fetch-error? i)))))
	  (use-hint-always (:use (:instance MT-DQ-len-0-to-4)))))

(defthm DQ1-inst-inv-step-INST-IFU 
    (implies (and (inv MT MA)
		  (IFU-INST-inv I MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (INST-in i MT)
		  (not (b1p (flush-all? MA sigs)))
		  (IFU-stg-p (INST-stg i))
		  (equal (INST-stg (step-INST I MT MA sigs)) '(DQ 1)))
	     (DQ1-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory
		  (e/d (lift-b-ops step-DE1
			   DE1-out DE2-out DE3-out IFU-INST-inv
			   INST-opcode decode-output INST-su
			   INST-pc INST-ra exception-relations
			   NEW-dq-stage INST-decode-error?
			   INST-fetch-error-detected-p-iff-INST-fetch-error?
			   INST-decode-error-detected-p-iff-INST-decode-error?
			   INST-excpt-flags DQ1-inst-inv)
		       (MT-DQ-len-lemmas))
		  :cases ((b1p (DISPATCH-INST? MA))))
	  (use-hint-always (:cases ((b1p (INST-fetch-error? i)))))
	  (use-hint-always (:use (:instance MT-DQ-len-0-to-4)))))

(defthm DQ2-inst-inv-step-INST-IFU 
    (implies (and (inv MT MA)
		  (IFU-INST-inv I MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (INST-in i MT)
		  (not (b1p (flush-all? MA sigs)))
		  (IFU-stg-p (INST-stg i))
		  (equal (INST-stg (step-INST I MT MA sigs)) '(DQ 2)))
	     (DQ2-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory
		  (e/d (lift-b-ops step-DE2 DE1-out DE2-out DE3-out
			   IFU-INST-inv INST-opcode decode-output
			   INST-decode-error? INST-su INST-ra INST-pc
			   INST-fetch-error-detected-p-iff-INST-fetch-error?
			   INST-decode-error-detected-p-iff-INST-decode-error?
			   exception-relations NEW-dq-stage INST-excpt-flags
			   DQ2-inst-inv)
		       (MT-DQ-len-lemmas))
		  :cases ((b1p (DISPATCH-INST? MA))))
	  (use-hint-always (:cases ((b1p (INST-fetch-error? i)))))
	  (use-hint-always (:use (:instance MT-DQ-len-0-to-4)))))

(defthm DQ3-inst-inv-step-INST-IFU 
    (implies (and (inv MT MA)
		  (IFU-INST-inv I MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (INST-in i MT)
		  (not (b1p (flush-all? MA sigs)))
		  (IFU-stg-p (INST-stg i))
		  (equal (INST-stg (step-INST I MT MA sigs)) '(DQ 3)))
	     (DQ3-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory
		  (e/d (lift-b-ops step-DE3 DE1-out DE2-out DE3-out
			   IFU-INST-inv INST-opcode INST-ra decode-output
			   INST-fetch-error-detected-p-iff-INST-fetch-error?
			   INST-decode-error-detected-p-iff-INST-decode-error?
			   INST-decode-error? INST-su INST-pc
			   exception-relations NEW-dq-stage INST-excpt-flags
			   DQ3-inst-inv)
		       (MT-DQ-len-lemmas))
		  :cases ((b1p (DISPATCH-INST? MA))))
	  (use-hint-always (:cases ((b1p (INST-fetch-error? i)))))
	  (use-hint-always (:use (:instance MT-DQ-len-0-to-4)))))

; DQ-inst-inv is true for i, if i's current stage is IFU-stg and
; it advances to DQ-stg.
(defthm DQ-inst-inv-step-INST-IFU 
    (implies (and (inv MT MA)
		  (IFU-INST-inv I MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (INST-in i MT)
		  (not (b1p (flush-all? MA sigs)))
		  (IFU-stg-p (INST-stg i))
		  (DQ-stg-p (INST-stg (step-INST I MT MA sigs))))
	     (DQ-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (e/d (DQ-inst-inv lift-b-ops)
				  (MT-DQ-len-lemmas))
		  :use (:instance  NEW-DQ-STAGE-ONE-OF-THEM))))

; DQ-inst-inv is true for i if i's current stage if DQ-stg.
(defthm DQ-inst-inv-step-INST-DQ 
    (implies (and (inv MT MA)
		  (DQ-INST-inv I MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (INST-in i MT)
		  (not (b1p (flush-all? MA sigs)))
		  (DQ-stg-p (INST-stg i))
		  (DQ-stg-p (INST-stg (step-INST I MT MA sigs))))
	     (DQ-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory
		  (e/d (DQ-stg-p inst-inv-def step-DE0 step-DE1 step-DE2
				 step-de3 DE1-out DE2-out DE3-out 
				 lift-b-ops)
		       (MT-DQ-len-lemmas))
		  :cases ((b1p (dispatch-inst? MA))))
	  (use-hint-always (:cases ((b1p (INST-fetch-error? i)))))
	  (use-hint-always (:use (:instance MT-DQ-len-0-to-4)))))

; A landmark lemma 
; DQ-inst-inv is preserved.
(defthm DQ-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (not (b1p (INST-exintr-now? i MA sigs)))
		  (DQ-stg-p (INST-stg (step-INST I MT MA sigs))))
	     (DQ-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("Goal" :use ((:instance INST-is-at-one-of-the-stages))
		  :in-theory (e/d (INST-inv)
				  (INST-INV-IF-INST-IN)))
	  ("Goal'" :cases ((b1p (flush-all? MA sigs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Begin of Proof of execute-inst-inv
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Execute-inst-inv defines the invariant conditions that instructions
; hold in the multi-issue pipelined execution core. 
; The proof is organized as follows.
;
;   Lemmas about the stage of dispatched instructions.
;   Lemmas about dispatch logic
;   Lemmas about register modifiers
;   Lemmas about CDB output
;   Proof of IU-inst-inv-step-INST
;   Proof of MU-inst-inv-step-INST
;   Proof of BU-inst-inv-step-INST
;   Proof of LSU-inst-inv-step-INST
;   Proof of execute-inst-robe-inv-step-INST
; The theorem execute-inst-robe-inv-step-INST guarantees that
; the ROB is recording correct values for instructions.
;;;;;;;;Begin of stage inference lemmas for instructions in DQ ;;;;;;
(deflabel begin-minor-stage-inference-rules)
; A dispatched instruction does not go to stage MU-lch1 directly.
(defthm not-MU-lch1-step-inst-if-DQ-stg
    (implies (DQ-stg-p (INST-stg i))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU lch1))))
  :hints (("goal" :in-theory (enable step-INST
				     STEP-INST-DQ
				     dispatch-inst))))

; A dispatched instruction does not go to stage MU-lch2 directly.
(defthm not-MU-lch2-step-inst-if-DQ-stg
    (implies (DQ-stg-p (INST-stg i))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(MU lch2))))
  :hints (("goal" :in-theory (enable step-INST
				     STEP-INST-DQ
				     dispatch-inst))))

; A dispatched instruction does not go to stage LSU-rbuf directly.
(defthm not-LSU-rbuf-step-inst-if-DQ-stg
    (implies (DQ-stg-p (INST-stg i))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))))
  :hints (("goal" :in-theory (enable step-INST
				     STEP-INST-DQ
				     dispatch-inst))))

; A dispatched instruction does not go to stage LSU-lch directly.
(defthm not-LSU-lch-step-inst-if-DQ-stg
    (implies (DQ-stg-p (INST-stg i))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU lch))))
  :hints (("goal" :in-theory (enable step-INST
				     STEP-INST-DQ
				     dispatch-inst))))

; A dispatched instruction does not go to stage LSU-wbuf0 directly.
(defthm not-LSU-wbuf0-step-inst-if-DQ-stg
    (implies (DQ-stg-p (INST-stg i))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU wbuf0))))
  :hints (("goal" :in-theory (enable step-INST
				     STEP-INST-DQ
				     dispatch-inst))))

; A dispatched instruction does not go to stage LSU-wbuf1 directly.
(defthm not-LSU-wbuf1-step-inst-if-DQ-stg
    (implies (DQ-stg-p (INST-stg i))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU wbuf1))))
  :hints (("goal" :in-theory (enable step-INST
				     STEP-INST-DQ
				     dispatch-inst))))

; A dispatched instruction does not go to stage LSU-wbuf0-lch directly.
(defthm not-LSU-wbuf0-lch-step-inst-if-DQ-stg
    (implies (DQ-stg-p (INST-stg i))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU wbuf0 lch))))
  :hints (("goal" :in-theory (enable step-INST
				     STEP-INST-DQ
				     dispatch-inst))))

; A dispatched instruction does not go to stage LSU-wbuf1-lch directly.
(defthm not-LSU-wbuf1-lch-step-inst-if-DQ-stg
    (implies (DQ-stg-p (INST-stg i))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU wbuf1 lch))))
  :hints (("goal" :in-theory (enable step-INST
				     STEP-INST-DQ
				     dispatch-inst))))

(deflabel end-minor-stage-inference-rules)
(deftheory minor-stage-inference-rules
    (set-difference-theories
     (universal-theory 'end-minor-stage-inference-rules)
     (universal-theory 'begin-minor-stage-inference-rules)))
(in-theory (disable minor-stage-inference-rules))

;;;;;;;;;;;;;;End of stage inference lemmas for instructions in DQ ;;;;;;

;;;;;;;;;Lemmas about the dispatch logic.;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Reservation station IU-RS0 is selected for the entry of a new dispatched
; instruction iff IU-RS0 is empty.
(defthm not-select-IU-RS0-if-RS0-valid?
    (equal (select-IU-RS0? (MA-IU MA))
	   (b-not (RS-valid? (IU-RS0 (MA-IU MA)))))
  :hints (("goal" :in-theory (enable select-IU-RS0? lift-b-ops
				     equal-b1p-converter))))

; Reservation station IU-RS1 is not chosen if IU-RS1 is busy.
(defthm not-select-IU-RS1-if-RS1-valid?
    (implies (b1p (RS-valid? (IU-RS1 (MA-IU MA))))
	     (equal (select-IU-RS1? (MA-IU MA)) 0))
  :hints (("goal" :in-theory (enable select-IU-RS1? lift-b-ops
				     dispatch-to-IU?
				     IU-ready?
				     equal-b1p-converter))))

; If both IU reservation stations are busy, instructions are not dispatched
; to the IU.
(defthm not-dispatch-to-IU-if-RS-full
    (implies (and (b1p (RS-valid? (IU-RS0 (MA-IU MA))))
		  (b1p (RS-valid? (IU-RS1 (MA-IU MA)))))
	     (equal (dispatch-to-IU? MA) 0))
  :hints (("goal" :in-theory (enable lift-b-ops dispatch-to-IU?
				     DQ-ready-to-IU?
				     IU-READY?
				     equal-b1p-converter))))

; A dispatched instruction goes into IU-RS1 if RS1 is the only available
; station.
(defthm select-IU-RS1-if-not-RS1-valid?
    (implies (and (b1p (RS-valid? (IU-RS0 (MA-IU MA))))
		  (not (b1p (RS-valid? (IU-RS1 (MA-IU MA))))))
	     (equal (select-IU-RS1? (MA-IU MA)) 1))
  :hints (("goal" :in-theory (enable lift-b-ops select-IU-RS1?
				     equal-b1p-converter))))

; Reservation station MU-RS0 is selected over MU-RS1 iff MU-RS0 is empty.
(defthm not-select-MU-RS0-if-RS0-valid?
    (equal (select-MU-RS0? (MA-MU MA))
	   (b-not (RS-valid? (MU-RS0 (MA-MU MA)))))
  :hints (("goal" :in-theory (enable select-MU-RS0? lift-b-ops
				     equal-b1p-converter))))

; Reservation station MU-RS1 is not selected if MU-RS1 is busy.
(defthm not-select-MU-RS1-if-RS1-valid?
    (implies (b1p (RS-valid? (MU-RS1 (MA-MU MA))))
	     (equal (select-MU-RS1? (MA-MU MA)) 0))
  :hints (("goal" :in-theory (enable select-MU-RS1? lift-b-ops
				     dispatch-to-MU?
				     MU-ready?
				     equal-b1p-converter))))

; If both MU reservation stations are busy, instructions are not dispatched
; to the MU.
(defthm not-dispatch-to-MU-if-RS-full
    (implies (and (b1p (RS-valid? (MU-RS0 (MA-MU MA))))
		  (b1p (RS-valid? (MU-RS1 (MA-MU MA)))))
	     (equal (dispatch-to-MU? MA) 0))
  :hints (("goal" :in-theory (enable lift-b-ops dispatch-to-MU?
				     DQ-ready-to-MU?
				     MU-READY?
				     equal-b1p-converter))))

; A dispatched instruction goes into MU-RS1 if RS1 is the only available
; station.
(defthm select-MU-RS1-if-not-RS1-valid?
    (implies (and (b1p (RS-valid? (MU-RS0 (MA-MU MA))))
		  (not (b1p (RS-valid? (MU-RS1 (MA-MU MA))))))
	     (equal (select-MU-RS1? (MA-MU MA)) 1))
  :hints (("goal" :in-theory (enable lift-b-ops select-MU-RS1?
				     equal-b1p-converter))))

; Reservation station BU-RS0 is selected over BU-RS1 iff BU-RS0 is empty.
(defthm not-select-BU-RS0-if-RS0-valid?
    (equal (select-BU-RS0? (MA-BU MA))
	   (b-not (BU-RS-valid? (BU-RS0 (MA-BU MA)))))
  :hints (("goal" :in-theory (enable select-BU-RS0? lift-b-ops
				     equal-b1p-converter))))

; Reservation station BU-RS1 is not selected if MU-RS1 is busy.
(defthm not-select-BU-RS1-if-RS1-valid?
    (implies (b1p (BU-RS-valid? (BU-RS1 (MA-BU MA))))
	     (equal (select-BU-RS1? (MA-BU MA)) 0))
  :hints (("goal" :in-theory (enable select-BU-RS1? lift-b-ops
				     dispatch-to-BU?
				     BU-ready?
				     equal-b1p-converter))))

; If both BU reservation stations are busy, instructions are not dispatched
; to the BU.
(defthm not-dispatch-to-BU-if-RS-full
    (implies (and (b1p (BU-RS-valid? (BU-RS0 (MA-BU MA))))
		  (b1p (BU-RS-valid? (BU-RS1 (MA-BU MA)))))
	     (equal (dispatch-to-BU? MA) 0))
  :hints (("goal" :in-theory (enable lift-b-ops dispatch-to-BU?
				     DQ-ready-to-BU?
				     BU-READY?
				     equal-b1p-converter))))

; A dispatched instruction goes into BU-RS1 if RS1 is the only available
; station.
(defthm select-BU-RS1-if-not-RS1-valid?
    (implies (and (b1p (BU-RS-valid? (BU-RS0 (MA-BU MA))))
		  (not (b1p (BU-RS-valid? (BU-RS1 (MA-BU MA))))))
	     (equal (select-BU-RS1? (MA-BU MA)) 1))
  :hints (("goal" :in-theory (enable lift-b-ops select-BU-RS1?
				     equal-b1p-converter))))

; If both LSU reservation stations are busy, instructions are not dispatched
; to the LSU.
(defthm not-dispatch-to-LSU-if-RS-full
    (implies (and (b1p (LSU-RS-valid? (LSU-RS0 (MA-LSU MA))))
		  (b1p (LSU-RS-valid? (LSU-RS1 (MA-LSU MA)))))
	     (equal (dispatch-to-LSU? MA) 0))
  :hints (("goal" :in-theory (enable lift-b-ops dispatch-to-LSU?
				     DQ-ready-to-LSU?
				     LSU-READY?
				     equal-b1p-converter))))

; If LSU-RS0 is the only available reservation station, a dispatched
; instruction goes into LSU-RS0.
(defthm select-LSU-RS0-if-not-RS0-valid?
    (implies (and (MA-state-p MA)
		  (b1p (LSU-RS-valid? (LSU-RS1 (MA-LSU MA))))
		  (not (b1p (LSU-RS-valid? (LSU-RS0 (MA-LSU MA))))))
	     (equal (select-LSU-RS0? (MA-LSU MA)) 1))
  :hints (("goal" :in-theory (enable lift-b-ops select-LSU-RS0?
				     equal-b1p-converter))))

; If LSU-RS1 is the only available reservation station, a dispatched
; instruction goes into LSU-RS1.
(defthm select-LSU-RS1-if-not-RS1-valid?
    (implies (and (MA-state-p MA)
		  (b1p (LSU-RS-valid? (LSU-RS0 (MA-LSU MA))))
		  (not (b1p (LSU-RS-valid? (LSU-RS1 (MA-LSU MA))))))
	     (equal (select-LSU-RS1? (MA-LSU MA)) 1))
  :hints (("goal" :in-theory (enable lift-b-ops select-LSU-RS1?
				     equal-b1p-converter))))

; Select-LSU-RS1 and select-LSU-RS0 are mutually exclusive.
(defthm select-LSU-RS1-select-LSU-RS0
    (implies (MA-state-p MA)
	     (equal (select-LSU-RS1? (MA-LSU MA))
		    (b-not (select-LSU-RS0? (MA-LSU MA)))))
  :hints (("goal" :in-theory (enable issue-logic-def LSU-output-def
				     lift-b-ops))))

; If LSU-RS0 is selected and RS0 is busy, no LSU instruction is dispatched.
(defthm not-dispatch-to-LSU-if-select-LSU-RS0
    (implies (and (MA-state-p MA)
		  (b1p (LSU-RS-valid? (LSU-RS0 (MA-LSU MA))))
		  (b1p (select-LSU-RS0? (MA-LSU MA))))
	     (equal (dispatch-to-LSU? MA) 0))
  :hints (("goal" :in-theory (enable issue-logic-def LSU-output-def
				     lift-b-ops
				     equal-b1p-converter dispatch-to-LSU?))))

; If LSU-RS1 is selected and RS1 is busy, no LSU instruction is dispatched.
(defthm not-dispatch-to-LSU-if-select-LSU-RS1
    (implies (and (MA-state-p MA)
		  (b1p (LSU-RS-valid? (LSU-RS1 (MA-LSU MA))))
		  (not (b1p (select-LSU-RS0? (MA-LSU MA)))))
	     (equal (dispatch-to-LSU? MA) 0))
  :hints (("goal" :in-theory (enable issue-logic-def LSU-output-def
				     lift-b-ops
				     equal-b1p-converter dispatch-to-LSU?))))

; If (INST-no-unit? i) is 0 for instruction i at (DQ 0),
; dispatch-no-unit? is not asserted.
;
; Note: These rules have very simple left-hand sides.  It is recommended
; that these rules are kept local.
(defthm INST-no-unit-if-dispatch-no-unit
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(DQ 0))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (not (b1p (INST-no-unit? i))))
	     (equal (dispatch-no-unit? MA) 0))
  :hints (("goal" :in-theory (enable dispatch-no-unit?
				     equal-b1p-converter
				     INST-no-unit?
				     lift-b-ops
				     exception-relations
				     inst-excpt-detected-p
				     DQ-ready-no-unit?)
		  :cases ((INST-fetch-error-detected-p i)))))

; If instruction i at (DQ 0) has caused an exception, dispatch-to-IU? is not
; asserted.  Following three lemmas are similar lemmas for other execution
; units.
(defthm not-dispatch-to-IU-if-excpt-detected
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(DQ 0))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (INST-excpt-detected-p i))
	     (equal (dispatch-to-IU? MA) 0))
  :hints (("goal" :in-theory (enable dispatch-to-IU? dispatch-to-LSU?
				     dispatch-to-BU? dispatch-to-MU?
				     lift-b-ops
				     DQ-READY-TO-IU? DQ-READY-TO-BU?
				     DQ-READY-TO-MU? DQ-READY-TO-LSU?
				     INST-EXCPT-DETECTED-P))))

(defthm not-dispatch-to-MU-if-excpt-detected
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(DQ 0))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (INST-excpt-detected-p i))
	     (equal (dispatch-to-MU? MA) 0))
  :hints (("goal" :in-theory (enable dispatch-to-IU? dispatch-to-LSU?
				     dispatch-to-BU? dispatch-to-MU?
				     lift-b-ops
				     DQ-READY-TO-IU? DQ-READY-TO-BU?
				     DQ-READY-TO-MU? DQ-READY-TO-LSU?
				     INST-EXCPT-DETECTED-P))))

(defthm not-dispatch-to-LSU-if-excpt-detected
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(DQ 0))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (INST-excpt-detected-p i))
	     (equal (dispatch-to-LSU? MA) 0))
  :hints (("goal" :in-theory (enable dispatch-to-IU? dispatch-to-LSU?
				     dispatch-to-BU? dispatch-to-MU?
				     lift-b-ops
				     DQ-READY-TO-IU? DQ-READY-TO-BU?
				     DQ-READY-TO-MU? DQ-READY-TO-LSU?
				     INST-EXCPT-DETECTED-P))))

(defthm not-dispatch-to-BU-if-excpt-detected
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(DQ 0))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (INST-excpt-detected-p i))
	     (equal (dispatch-to-BU? MA) 0))
  :hints (("goal" :in-theory (enable dispatch-to-IU? dispatch-to-LSU?
				     dispatch-to-BU? dispatch-to-MU?
				     lift-b-ops
				     DQ-READY-TO-IU? DQ-READY-TO-BU?
				     DQ-READY-TO-MU? DQ-READY-TO-LSU?
				     INST-EXCPT-DETECTED-P))))

; If dispatch-to-IU? is asserted, (INST-IU? i) is true for the instruction
; i at (DQ 0).  The lemma is written as a contrapositive.
; Following three lemmas are similar lemmas for other execution units.
(defthm INST-IU-if-dispatch-to-IU
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(DQ 0))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-IU? i))))
	     (equal (dispatch-to-IU? MA) 0))
  :hints (("goal" :in-theory (enable dispatch-to-IU?
				     equal-b1p-converter
				     INST-IU?
				     lift-b-ops
				     exception-relations
				     DQ-ready-to-IU?)
		  :cases ((INST-fetch-error-detected-p i)))))

(defthm INST-MU-if-dispatch-to-MU
    (implies (and (inv MT MA)
		  (INST-in i MT) (equal (INST-stg i) '(DQ 0))
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-MU? i))))
	     (equal (dispatch-to-MU? MA) 0))
  :hints (("goal" :in-theory (enable dispatch-to-MU?
				     equal-b1p-converter
				     INST-MU?
				     lift-b-ops
				     INST-EXCPT-FLAGS
				     exception-relations
				     DQ-ready-to-MU?)
		  :cases ((INST-fetch-error-detected-p i)))))

(defthm INST-BU-if-dispatch-to-BU
    (implies (and (inv MT MA)
		  (INST-in i MT) (equal (INST-stg i) '(DQ 0))
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-BU? i))))
	     (equal (dispatch-to-BU? MA) 0))
  :hints (("goal" :in-theory (enable dispatch-to-BU?
				     equal-b1p-converter
				     INST-BU?
				     lift-b-ops
				     INST-EXCPT-FLAGS
				     exception-relations
				     DQ-ready-to-BU?)
		  :cases ((INST-fetch-error-detected-p i)))))

(defthm INST-LSU-if-dispatch-to-LSU
    (implies (and (inv MT MA)
		  (INST-in i MT) (equal (INST-stg i) '(DQ 0))
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-LSU? i))))
	     (equal (dispatch-to-LSU? MA) 0))
  :hints (("goal" :in-theory (enable dispatch-to-LSU?
				     equal-b1p-converter
				     INST-LSU?
				     lift-b-ops
				     INST-EXCPT-FLAGS
				     exception-relations
				     DQ-ready-to-LSU?)
		  :cases ((INST-fetch-error-detected-p i)))))
;;;;;;;;;;;; End of Lemmas about dispatch logic. ;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;; Start of Lemmas about Register Modifiers;;;;;;;;;;;;;;;;
; If instruction i has raised an fetch error,  i does not go into the
; execution stage.   In fact, it advances to the complete stage directly.
(defthm INST-stg-step-INST-if-fetch-error-inst-dispatched
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(DQ 0))
		  (b1p (INST-fetch-error? i))
		  (b1p (dispatch-inst? MA))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (INST-stg (step-INST i MT MA sigs)) '(complete)))
  :hints (("goal" :in-theory (enable dispatch-inst? lift-b-ops
				     exception-relations))))

;; A load-store instruction i at DQ-stg should not complete in this
;; cycle, because it should advance to the LSU execution stage.
(defthm not-complete-stg-p-step-INST-if-INST-LSU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (DQ-stg-p (INST-stg i))
		  (b1p (INST-LSU? i))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i)))
	     (not (complete-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :in-theory (enable step-INST DQ-stg-p
				     step-inst-dq
				     dispatch-inst))))

; A data-access error does not occur before instruction dispatch. 
(defthm INST-data-accs-error-detected-p-step-INST-not-dispatched
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p I) (INST-in I MT)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))		  
		  (not (dispatched-p i)))
	     (not (INST-data-accs-error-detected-p (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (e/d (INST-data-accs-error-detected-p
				   INST-LOAD-ACCS-ERROR-DETECTED-P
				   minor-stage-inference-rules
				   opcode-inst-type
				   INST-exunit-relations
				   INST-DECODE-ERROR-DETECTED-P
				   INST-STORE-ACCS-ERROR-DETECTED-P)
				  (INST-STG-STEP-IFU-INST-IF-DQ-FULL
				   INST-is-at-one-of-the-stages))
		  :use (:instance (:instance INST-is-at-one-of-the-stages)))))

;; No exception occurs in the dispatch queue.
(defthm INST-excpt-detected-p-step-INST-DQ-0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))		  
		  (equal (INST-stg i) '(DQ 0)))
	     (equal (INST-excpt-detected-p (step-INST i MT MA sigs))
		    (INST-excpt-detected-p i)))
  :hints (("goal" :in-theory (enable INST-excpt-detected-p))))

; INST-excpt-flags remains unchanged in the dispatch queue.
(defthm INST-excpt-flags-step-INST-DQ
    (implies (and (inv MT MA)
		  (DQ-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (INST-excpt-flags (step-INST i MT MA sigs))
		    (INST-excpt-flags i)))
  :hints (("goal" :in-theory (enable INST-excpt-flags))))

; Dispatched instruction i is assigned to the tail entry of the ROB. 
(defthm INST-rob-step-inst-=-MT-rob-tail
    (implies (and (inv MT MA)
		  (MAETT-p MT)  (MA-state-p MA)
		  (equal (INST-stg i) '(DQ 0))
		  (b1p (dispatch-inst? MA)))
	     (equal (INST-tag (STEP-inst i MT MA sigs))
		    (MT-rob-tail MT)))
  :hints (("goal" :in-theory (enable step-INST step-INST-dq
				     dispatch-inst))))

  
(encapsulate nil
(local
(defthm read-reg-ISA-before-DQ-DE0-help-induct-2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (rname-p rname)
		  (consp trace)
		  (equal (INST-stg i) '(DQ 0))
		  (member-equal i trace) 
		  (no-commit-inst-p trace)
		  (not (trace-exist-LRM-in-ROB-p rname trace)))
	     (equal (read-reg rname (ISA-RF (INST-pre-ISA (car trace))))
		    (read-reg rname (ISA-RF (INST-pre-ISA i)))))
  :hints (("goal" :induct (member-equal i trace)
		  :in-theory (enable committed-p))
	  (when-found (ISA-RF (INST-PRE-ISA (CAR (CDR TRACE))))
		      (:cases ((consp (cdr trace))))))))

(local
(defthm read-reg-ISA-before-DQ-DE0-help-induct
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace) 
		  (rname-p rname)
		  (consp trace)
		  (equal (INST-stg i) '(DQ 0))
		  (member-equal i trace)
		  (not (trace-exist-LRM-in-ROB-p rname trace)))
	     (equal (read-reg rname
			      (trace-RF
			       trace (ISA-RF (INST-pre-ISA (car trace)))))
		    (read-reg rname (ISA-RF (INST-pre-ISA i)))))
  :hints ((when-found (ISA-RF (INST-PRE-ISA (CAR (CDR TRACE))))
		      (:cases ((consp (cdr trace)))))
	  ("goal" :in-theory (enable committed-p)))
  :rule-classes nil))

(local
(defthm read-reg-ISA-before-DQ-DE0-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (rname-p rname)
		  (equal (INST-stg i) '(DQ 0))
		  (not (exist-LRM-in-ROB-p rname MT)))
	     (equal (read-reg rname (MT-RF MT))
		    (read-reg rname (ISA-RF (INST-pre-ISA i)))))
  :rule-classes nil
; Matt K. mod: Apparently heuristics have somehow changed.  The proof goes
; through by replacing the original hints with corresponding proof-builder
; commands.
#|
  :hints (("goal" :in-theory (e/d (MT-RF exist-LRM-in-ROB-p
					 INST-in)
				  (MT-RF-=-MA-RF))
		  :use (:instance read-reg-ISA-before-DQ-DE0-help-induct
				  (trace (MT-trace MT)))))
|#
  :instructions ((:in-theory (e/d (MT-RF exist-LRM-in-ROB-p
					 INST-in)
				  (MT-RF-=-MA-RF)))
                 (:use (:instance read-reg-ISA-before-DQ-DE0-help-induct
				  (trace (MT-trace MT))))
                 :prove) ; or :bash
  ))

; An important lemma. 
; Suppose instruction i is at (DQ 0), and there is no register modifier
; in ROB, then the actual register contains the correct operand for i.
(defthm read-reg-ISA-before-DQ-DE0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (rname-p rname)
		  (equal (INST-stg i) '(DQ 0))
		  (not (exist-LRM-in-ROB-p rname MT)))
	     (equal (read-reg rname (ISA-RF (INST-pre-ISA i)))
		    (read-reg rname (MA-RF MA))))
  :hints (("goal" :use (:instance read-reg-ISA-before-DQ-DE0-help))))
)

(encapsulate nil
(local
(defthm read-sreg-ISA-before-DQ-DE0-help-induct-2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (srname-p rname)
		  (consp trace)
		  (equal (INST-stg i) '(DQ 0))
		  (member-equal i trace) 
		  (no-commit-inst-p trace)
		  (not (b1p (trace-specultv-at-dispatch? trace)))
		  (not (trace-exist-LSRM-in-ROB-p rname trace)))
	     (equal (read-sreg rname (ISA-SRF (INST-pre-ISA (car trace))))
		    (read-sreg rname (ISA-SRF (INST-pre-ISA i)))))
  :hints (("goal" :induct (member-equal i trace)
		  :in-theory (enable committed-p lift-b-ops
				     INST-exintr-INST-in-if-not-retired
				     INST-start-specultv?))
	  (when-found (ISA-SRF (INST-PRE-ISA (CAR (CDR TRACE))))
		      (:cases ((consp (cdr trace))))))))

(local
(defthm read-sreg-ISA-before-DQ-DE0-help-induct
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace) 
		  (srname-p rname)
		  (consp trace)
		  (equal (INST-stg i) '(DQ 0))
		  (member-equal i trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (trace-exist-LSRM-in-ROB-p rname trace))
		  (not (b1p (trace-specultv-at-dispatch? trace))))
	     (equal (read-sreg rname
			       (trace-SRF
				trace (ISA-SRF (INST-pre-ISA (car trace)))))
		    (read-sreg rname (ISA-SRF (INST-pre-ISA i)))))
  :hints ((when-found (ISA-SRF (INST-PRE-ISA (CAR (CDR TRACE))))
		      (:cases ((consp (cdr trace)))))
	  ("goal" :in-theory (enable committed-p)))
  :rule-classes nil))

(local
(defthm read-sreg-ISA-before-DQ-DE0-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (srname-p rname)
		  (equal (INST-stg i) '(DQ 0))
		  (not (exist-LSRM-in-ROB-p rname MT))
		  (not (b1p (MT-specultv-at-dispatch? MT))))
	     (equal (read-sreg rname (MT-SRF MT))
		    (read-sreg rname (ISA-SRF (INST-pre-ISA i)))))
  :rule-classes nil
; Matt K. mod: Apparently heuristics have somehow changed.  The proof goes
; through by replacing the original hints with corresponding proof-builder
; commands.
#|
  :hints (("goal" :in-theory (e/d (MT-SRF exist-LSRM-in-ROB-p
				   MT-specultv-at-dispatch? INST-in)
				  (MT-SRF-=-MA-SRF))
		  :use (:instance read-sreg-ISA-before-DQ-DE0-help-induct
				  (trace (MT-trace MT)))))
|#
  :instructions ((:in-theory (e/d (MT-SRF exist-LSRM-in-ROB-p
                                          MT-specultv-at-dispatch? INST-in)
				  (MT-SRF-=-MA-SRF)))
                 (:use (:instance read-sreg-ISA-before-DQ-DE0-help-induct
				  (trace (MT-trace MT))))
                 :prove) ; or :bash
  ))

; An important lemma. 
; Suppose instruction i is at (DQ 0).  If no register modifier of
; special register rname is in ROB, the actual special register rname
; contains the correct register value for i.
(defthm read-sreg-ISA-before-DQ-DE0
     (implies (and (inv MT MA)
		   (equal (INST-stg i) '(DQ 0))
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-in i MT)
		   (srname-p rname)
		   (not (exist-LSRM-in-ROB-p rname MT))
		   (not (b1p (MT-specultv-at-dispatch? MT))))
	      (equal (read-sreg rname (ISA-SRF (INST-pre-ISA i)))
		     (read-sreg rname (MA-SRF MA))))
  :hints (("goal" :use (:instance read-sreg-ISA-before-DQ-DE0-help))))
)

; Instruction i is MTSR or MFSR instruction, and RA does not 
; designate a legitimate special register, i is an illegal instruction.
(defthm INST-decode-error-if-INST-ra-not-srname-p
    (implies (and (or (equal (INST-opcode i) 9)
		      (equal (INST-opcode i) 10))
		  (not (srname-p (INST-RA I)))
		  (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (INST-decode-error? i) 1))
  :hints (("goal" :in-theory (enable INST-decode-error?
				     equal-b1p-converter
				     decode-illegal-inst?
				     srname-p rname-p
				     INST-opcode
				     lift-b-ops))))

; Instruction i is at (DQ 0), and output DQ-read-val1 from the dispatch
; logic is the first source operand value for instruction i.
(defthm DQ-read-val1-INST-src-val1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (DQ-out-ready1? (MA-DQ MA))))
	     (equal (DQ-read-val1 (MA-DQ MA) MA) (INST-src-val1 i)))
  :hints (("goal" :in-theory
		  (e/d (DQ-out-ready1?
			DQ-read-val1
			INST-SRC-val1
			INST-cntlv decode rdb logbit*
			INST-modified-at-dispatch-off-if-undispatched-inst-in
			equal-b1p-converter
			lift-b-ops)
		       (INST-decode-error-if-INST-ra-not-srname-p)))
	  (when-found (EQUAL '9 (INST-OPCODE I))
		      (:use
		       (:instance INST-decode-error-if-INST-ra-not-srname-p)))
	  (when-found (b1p (INST-decode-error? i))
		      (:cases ((b1p (INST-fetch-error? i)))))))

; Instruction i is at (DQ 0), and output DQ-read-val2 from a dispatch
; logic is the second source operand value of instruction i.
(defthm DQ-read-val2-INST-src-val2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (DQ-out-ready2? (MA-DQ MA))))
	     (equal (read-reg (DQ-out-reg2 (MA-DQ MA)) (MA-RF MA))
		    (INST-src-val2 i)))
  :hints (("goal" :in-theory
		  (e/d (DQ-out-ready2?
			DQ-out-reg2
			INST-SRC-val2
			INST-cntlv decode rdb logbit*
			equal-b1p-converter
			lift-b-ops)
		       (INST-decode-error-if-INST-ra-not-srname-p)))))

; Instruction i is at (DQ 0), and output DQ-read-val3 from a dispatch
; logic is the third source operand value of instruction i.
(defthm DQ-read-val3-INST-src-val3
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (DQ-out-ready3? (MA-DQ MA))))
	     (equal (read-reg (DQ-out-reg3 (MA-DQ MA)) (MA-RF MA))
		    (INST-src-val3 i)))
  :hints (("goal" :in-theory
		  (e/d (DQ-out-ready3?
			DQ-out-reg3
			INST-SRC-val3
			INST-cntlv decode rdb logbit*
			equal-b1p-converter
			lift-b-ops)
		       (INST-decode-error-if-INST-ra-not-srname-p)))))

(in-theory (enable IFU-is-last-inst DQ0-is-earlier-than-other-DQ)) 

(local
(defthm INST-dest-val-read-reg-INST-post-ISA
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-excpt? I)))
		  (not (b1p (INST-exintr? i)))
		  (reg-modifier-p rname i))
	     (equal (INST-dest-val i)
		    (read-reg rname (ISA-RF (INST-post-ISA i)))))
  :hints (("goal" :in-theory (enable INST-dest-val
				     reg-modifier-p
				     INST-function-def
				     DECODE-ILLEGAL-INST?
				     lift-b-ops
				     ISA-step ISA-step-functions)))))

(local
(defthm INST-dest-val-read-sreg-INST-post-ISA
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-excpt? I)))
		  (not (b1p (INST-exintr? i)))
		  (sreg-modifier-p rname i))
	     (equal (INST-dest-val i)
		    (read-sreg rname (ISA-SRF (INST-post-ISA i)))))
  :hints (("goal" :in-theory (enable INST-dest-val
				     sreg-modifier-p
				     INST-function-def
				     DECODE-ILLEGAL-INST?
				     lift-b-ops
				     ISA-step ISA-step-functions)))))

; A local lemma.
; Suppose instruction k precedes i in program order.
; Suppose s0 and s1 are the pre-ISA state of k and i, respectively.
; If there is no modifier of register rname between k and i,
; the value of register rname in s0 and s1 are the same.
; Note: This rule has a very bad form.  The LHS term pattern matches the
; RHS.  It is possible that this rule causes an infinite loop.  So
; we disable the rule.
(local
(defthm read-reg-unchanged-if-not-trace-exist-LRM-before-p
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (not (b1p (inst-specultv? I)))
		  (not (b1p (inst-modified? I)))
		  (not (trace-exist-LRM-before-p i rname trace))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-listp trace)
		  (INST-p i) (rname-p rname) 
		  (member-equal i trace))
	     (equal (read-reg rname (ISA-RF (INST-pre-ISA i)))
		    (read-reg rname (ISA-RF (INST-pre-ISA (car trace))))))
  :hints ((when-found (ISA-RF (INST-PRE-ISA (CAR (CDR TRACE))))
		      (:cases ((consp (cdr trace))))))))

(local
(defthm read-sreg-unchanged-if-not-trace-exist-LSRM-before-p
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (not (b1p (inst-specultv? I)))
		  (not (b1p (inst-modified? I)))
		  (not (trace-exist-LSRM-before-p i rname trace))
		  (no-commit-inst-p trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-listp trace)
		  (INST-p i) (srname-p rname) 
		  (member-equal i trace))
	     (equal (read-sreg rname (ISA-SRF (INST-pre-ISA i)))
		    (read-sreg rname (ISA-SRF (INST-pre-ISA (car trace))))))
  :hints ((when-found (ISA-SRF (INST-PRE-ISA (CAR (CDR TRACE))))
		      (:cases ((consp (cdr trace)))))
	  ("goal" :in-theory (enable INST-exintr-INST-in-if-not-retired
				     committed-p)))))

(local
(in-theory
 (disable read-reg-unchanged-if-not-trace-exist-LRM-before-p
	  read-sreg-unchanged-if-not-trace-exist-LSRM-before-p)))

(encapsulate nil
(local
 (defthm INST-dest-val-LRM-before-help-help
     (implies (and (consp trace)
		   (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (subtrace-p trace MT)
		   (rname-p rname)
		   (INST-listp trace)
		   (not (b1p (inst-specultv? I)))
		   (not (b1p (inst-modified? I)))
		   (member-equal i (cdr trace))
		   (reg-modifier-p rname (car trace))
		   (not (committed-p (car trace)))
		   (not (trace-exist-LRM-before-p i rname
						  (cdr trace))))
	      (equal (read-reg rname (ISA-RF (INST-pre-ISA i)))
		     (INST-dest-val (car trace))))
   :Hints (("goal" :cases ((consp (cdr trace)))
		   :in-theory (enable
	             INST-exintr-INST-in-if-not-retired
  	             read-reg-unchanged-if-not-trace-exist-LRM-before-p
		     committed-p)
		   :restrict
		   ((read-reg-unchanged-if-not-trace-exist-LRM-before-p
		     ((trace (cdr trace)))))))))

(local
 (defthm INST-dest-val-LRM-before-help
     (implies (and (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (subtrace-p trace MT)
		   (INST-listp trace)
		   (rname-p rname)
		   (not (b1p (inst-specultv? I)))
		   (not (b1p (inst-modified? I)))
		   (INST-p i) (member-equal i trace)
		   (trace-exist-uncommitted-LRM-before-p i rname trace))
     (equal (INST-dest-val (trace-LRM-before i rname trace))
	    (read-reg rname (ISA-RF (INST-pre-ISA i)))))
   :hints (("goal" :restrict
		   ((INST-dest-val-LRM-before-help-help
		     ((trace trace))))))))

; An important lemma. 
; Suppose j is a last modifier of register rname before i.  And s is
; the pre-ISA i.  Then the destination value of j is the same as the
; value of register rname in s.
(defthm INST-dest-val-LRM-before*
    (implies (and (inv MT MA)
		  (exist-uncommitted-LRM-before-p i rname MT)
		  (not (b1p (inst-specultv? I)))
		  (not (b1p (inst-modified? I)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (rname-p rname))
	     (equal (INST-dest-val (LRM-before i rname MT))
		    (read-reg rname (ISA-RF (INST-pre-ISA i)))))
  :hints (("goal" :in-theory (enable LRM-before
				     exist-uncommitted-LRM-before-p
				     INST-in))))
)

;; Another presentation of the same original theorem
(defthm INST-dest-val-LRM-before
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? I)))
		  (not (b1p (inst-modified? I)))
		  (rname-p rname)
		  (exist-LRM-before-p i rname MT)
		  (not (committed-p (LRM-before i rname MT))))
	     (equal (INST-dest-val (LRM-before i rname MT))
		    (read-reg rname (ISA-RF (INST-pre-ISA i)))))
  :hints (("goal" :in-theory
	  (enable exist-LRM-before-p-and-exist-uncommitted-LRM-before-p)))
  :rule-classes nil)

(encapsulate nil
(local
(defthm INST-dest-val-LSRM-before-help-help
    (implies (and (consp trace)
		  (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (srname-p rname)
		  (INST-listp trace)
		  (not (b1p (inst-specultv? I)))
		  (not (b1p (inst-modified? I)))
		  (member-equal i (cdr trace))
		  (sreg-modifier-p rname (car trace))
		  (not (committed-p (car trace)))
		  (not (trace-exist-uncommitted-LSRM-before-p i rname (cdr trace))))
	     (equal (read-sreg rname (ISA-SRF (INST-pre-ISA i)))
		    (INST-dest-val (car trace))))
  :hints (("goal"
	   :cases ((consp (cdr trace)))
	   :in-theory
	   (enable
	    read-sreg-unchanged-if-not-trace-exist-LSRM-before-p
	    INST-exintr-INST-in-if-not-retired
	    committed-p)
	   :restrict
	   ((read-sreg-unchanged-if-not-trace-exist-LSRM-before-p
	     ((trace (cdr trace)))))))))

(local
(defthm INST-dest-val-LSRM-before-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (srname-p rname)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (INST-p i) (member-equal i trace)
		  (trace-exist-uncommitted-LSRM-before-p i rname trace))
     (equal (INST-dest-val (trace-LSRM-before i rname trace))
	    (read-sreg rname (ISA-SRF (INST-pre-ISA i)))))
  :hints (("goal" :restrict
		  ((INST-dest-val-LSRM-before-help-help
		    ((trace trace))))))))

; Suppose j is a the last modifier of special register rname before i.
; The destination value of j is the value of the special register rname
; in the pre-ISA state of i.
(defthm INST-dest-val-LSRM-before*
    (implies (and (inv MT MA)
		  (exist-uncommitted-LSRM-before-p i rname MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (srname-p rname))
	     (equal (INST-dest-val (LSRM-before i rname MT))
		    (read-sreg rname (ISA-SRF (INST-pre-ISA i)))))
  :hints (("goal" :in-theory (enable LSRM-before
				     exist-uncommitted-LSRM-before-p
				     INST-in))))
)

; Another presentation of INST-dest-val-LSRM-before.
(defthm INST-dest-val-LSRM-before
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT) (srname-p rname)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (exist-LSRM-before-p i rname MT)
		  (not (committed-p (LSRM-before i rname MT))))
	     (equal (INST-dest-val (LSRM-before i rname MT))
		    (read-sreg rname (ISA-SRF (INST-pre-ISA i)))))
  :hints (("goal" :in-theory
	  (enable exist-LSRM-before-p-and-exist-uncommitted-LSRM-before-p)))
  :rule-classes nil)

; If j is the last register modifier before i, and i is not speculatively
; executed instruction, then j is not speculatively executed, either. 
(defthm inst-specultv-LRM-before
    (implies (and (inv MT MA)
		  (exist-LRM-before-p i rname MT)
		  (not (b1p (inst-specultv? I)))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)) 
	     (equal (inst-specultv? (LRM-before i rname MT))
		    0))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter)
				  (INST-in-order-p-inst-specultv))
		  :use (:instance INST-in-order-p-inst-specultv
				  (i (LRM-before i rname MT))
				  (j i)))))

; see inst-specultv-LRM-before
(defthm inst-specultv-LSRM-before
    (implies (and (inv MT MA)
		  (exist-LSRM-before-p i rname MT)
		  (not (b1p (inst-specultv? I)))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)) 
	     (equal (inst-specultv? (LSRM-before i rname MT))
		    0))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter)
				  (INST-in-order-p-inst-specultv))
		  :use (:instance INST-in-order-p-inst-specultv
				  (i (LSRM-before i rname MT))
				  (j i)))))

; If j is the last register modifier before i, and i's modified flag is not
; on, then j's modified flag is not on either.
(defthm INST-modified-LRM-before
    (implies (and (inv MT MA)
		  (exist-LRM-before-p i rname MT)
		  (not (b1p (INST-modified? I)))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)) 
	     (equal (INST-modified? (LRM-before i rname MT))
		    0))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter)
				  (INST-in-order-p-INST-modified))
		  :use (:instance INST-in-order-p-INST-modified
				  (i (LRM-before i rname MT))
				  (j i)))))

; See INST-modified-LRM-before.
(defthm INST-modified-LSRM-before
    (implies (and (inv MT MA)
		  (exist-LSRM-before-p i rname MT)
		  (not (b1p (INST-modified? I)))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)) 
	     (equal (INST-modified? (LSRM-before i rname MT))
		    0))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter)
				  (INST-in-order-p-INST-modified))
		  :use (:instance INST-in-order-p-INST-modified
				  (i (LSRM-before i rname MT))
				  (j i)))))

; If j is the last register modifier before i, and i is not speculatively
; executed, then no fetch error is detected for j.
(defthm INST-fetch-error-detected-p-LRM-before
    (implies (and (inv MT MA)
		  (exist-uncommitted-LRM-before-p i rname MT)
		  (not (b1p (inst-specultv? I)))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)) 
	     (not (INST-fetch-error-detected-p 
		   (LRM-before i rname MT))))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter
				   INST-start-specultv?
				   INST-excpt?
				   lift-b-ops)
				  (INST-in-order-p-INST-start-specultv))
		  :use (:instance INST-in-order-p-INST-start-specultv
				  (i (LRM-before i rname MT))
				  (j i)))))

; See INST-fetch-error-detected-p-LRM-before.
(defthm INST-fetch-error-detected-p-LSRM-before
    (implies (and (inv MT MA)
		  (exist-uncommitted-LSRM-before-p i rname MT)
		  (not (b1p (inst-specultv? I)))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)) 
	     (not (INST-fetch-error-detected-p 
		   (LSRM-before i rname MT))))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter
				     INST-start-specultv?
				     INST-excpt?
				     lift-b-ops)
				  (INST-in-order-p-INST-start-specultv))
		  :use (:instance INST-in-order-p-INST-start-specultv
				  (i (LSRM-before i rname MT))
				  (j i)))))

; If j is the last register modifier before i in program order, and 
; i is not speculatively executed, then j has not raised an exception.
(defthm INST-excpt-detected-p-LRM-before
    (implies (and (inv MT MA)
		  (exist-uncommitted-LRM-before-p i rname MT)
		  (not (b1p (inst-specultv? I)))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)) 
	     (not (INST-excpt-detected-p 
		   (LRM-before i rname MT))))
    :hints (("goal" :in-theory (e/d (equal-b1p-converter
				     INST-start-specultv?
				     INST-excpt?
				     lift-b-ops)
				  (INST-in-order-p-INST-start-specultv))
		  :use (:instance INST-in-order-p-INST-start-specultv
				  (i (LRM-before i rname MT))
				  (j i)))))

; See INST-excpt-detected-p-LRM-before
(defthm INST-excpt-detected-p-LSRM-before
    (implies (and (inv MT MA)
		  (exist-uncommitted-LSRM-before-p i rname MT)
		  (not (b1p (inst-specultv? I)))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)) 
	     (not (INST-excpt-detected-p 
		   (LSRM-before i rname MT))))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter
				     INST-start-specultv?
				     INST-excpt?
				     lift-b-ops)
				  (INST-in-order-p-INST-start-specultv))
		  :use (:instance INST-in-order-p-INST-start-specultv
				  (i (LSRM-before i rname MT))
				  (j i)))))
;;;;;;;;;;;;;;;End of last register modifier theory ;;;;;;;;;;;;;;;;;;;

;;;;;;;;Lemmas about CDB output;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  When IU-RS0-issue-ready? is on, there is an instruction at IU RS0.
(defthm uniq-inst-of-tag-if-IU-RS0-issue-ready
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (IU-RS0-issue-ready? (MA-IU MA))))
	     (uniq-inst-of-tag (RS-tag (IU-RS0 (MA-IU MA))) MT))
  :hints (("goal" :in-theory (enable lift-b-ops IU-RS0-issue-ready?
				     IU-RS-field-INST-at-lemmas))))

;  When IU-RS1-issue-ready? is on, there is an instruction at IU RS1.
(defthm uniq-inst-of-tag-if-IU-RS1-issue-ready
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (IU-RS1-issue-ready? (MA-IU MA))))
	     (uniq-inst-of-tag (RS-tag (IU-RS1 (MA-IU MA))) MT))
  :hints (("goal" :in-theory (enable lift-b-ops IU-RS1-issue-ready?
				     IU-RS-field-INST-at-lemmas))))

; When CDB-for-IU? is on, an instruction is assigned to the ROB entry
; designated by CDB-tag.
(defthm uniq-inst-of-tag-if-CDB-for-IU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (CDB-for-IU? MA)))
	     (uniq-inst-of-tag (CDB-tag MA) MT))
  :hints (("goal" :in-theory (enable CDB-tag lift-b-ops CDB-for-IU?
				     IU-output-tag)
		  :cases ((b1p (IU-RS0-ISSUE-READY? (MA-IU MA)))))))

; When CDB-for-MU? is on, an instruction is assigned to the ROB entry
; designated by CDB-tag.
(defthm uniq-inst-of-tag-if-CDB-for-MU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (CDB-for-MU? MA)))
	     (uniq-inst-of-tag (CDB-tag MA) MT))
  :hints (("goal" :in-theory (enable CDB-def lift-b-ops
				     MU-field-lemmas))))

; When CDB-for-BU? is on, an instruction is assigned to the ROB entry
; designated by CDB-tag. 
(defthm uniq-inst-of-tag-if-CDB-for-BU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (CDB-for-BU? MA)))
	     (uniq-inst-of-tag (CDB-tag MA) MT))
  :hints (("goal" :in-theory (enable CDB-def lift-b-ops BU-output-def))))

; When CDB-for-LSU? is on, an instruction is assigned to the ROB entry
; designated by CDB-tag. 
(defthm uniq-inst-of-tag-if-CDB-for-LSU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (CDB-for-LSU? MA)))
	     (uniq-inst-of-tag (CDB-tag MA) MT))
  :hints (("goal" :in-theory (enable CDB-def lift-b-ops LSU-output-def
				     LSU-field-INST-at-lemmas))))

; When CDB-ready-for? is 1 with the Tomasulo's tag rix, an instruction is
; assigned to the ROB entry designated by rix.
(defthm uniq-inst-of-tag-if-CDB-ready-for
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (rob-index-p rix)
		  (b1p (CDB-ready-for? rix MA)))
	     (uniq-inst-of-tag rix MT))
  :hints (("goal" :in-theory (enable lift-b-ops CDB-ready-for?
				     bv-eqv-iff-equal)
		  :use (:instance cases-of-CDB-ready))))

; If CDB-ready-for is 1 with Tomasulo's tag rix, and an IU instruction
; is assigned to the ROB entry designated by rix, CDB-for-IU? is 1.
(defthm CDB-for-IU-if-CDB-ready-for-INST-IU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (b1p (CDB-ready-for? rix MA))
		  (b1p (INST-IU? (inst-of-tag rix MT)))
		  (rob-index-p rix)
		  (not (b1p (inst-specultv? (inst-of-tag rix MT))))
		  (not (b1p (INST-modified? (inst-of-tag rix MT)))))
	     (b1p (CDB-for-IU? MA)))
  :hints (("goal" :in-theory (enable CDB-def
				     BU-output-def
				     bv-eqv-iff-equal
				     BU-RS-field-inst-at-lemmas
				     MU-field-inst-at-lemmas
				     LSU-field-inst-at-lemmas
				     CDB-ready?
				     lift-b-ops
				     equal-b1p-converter)))
  :rule-classes nil)

; If CDB-ready-for is 1 with Tomasulo's tag rix, and an BU instruction
; is assigned to the ROB entry designated by rix, CDB-for-BU? is 1.
(defthm CDB-for-BU-if-CDB-ready-for-INST-BU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (b1p (CDB-ready-for? rix MA))
		  (b1p (INST-BU? (inst-of-tag rix MT)))
		  (rob-index-p rix)
		  (not (b1p (inst-specultv? (inst-of-tag rix MT))))
		  (not (b1p (INST-modified? (inst-of-tag rix MT)))))
	     (b1p (CDB-for-BU? MA)))
  :hints (("goal" :in-theory (enable CDB-ready-for?
				     CDB-for-BU? CDB-tag
				     CDB-for-IU?
				     CDB-for-IU?
				     CDB-for-MU?
				     CDB-READY?
				     CDB-for-LSU?
				     IU-output-tag
				     BU-output-tag
				     BU-RS-field-inst-at-lemmas
				     MU-field-inst-at-lemmas
				     LSU-field-inst-at-lemmas
				     IU-RS0-ISSUE-READY?
				     IU-RS1-ISSUE-READY?
				     inst-type-exclusive-2
				     bv-eqv-iff-equal
				     lift-b-ops
				     equal-b1p-converter)))
  :rule-classes nil)

; If CDB-ready-for is 1 with Tomasulo's tag rix, and an LSU instruction
; is assigned to the ROB entry designated by rix, CDB-for-LSU? is 1.
(defthm CDB-for-LSU-if-CDB-ready-for-INST-LSU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (b1p (CDB-ready-for? rix MA))
		  (b1p (INST-LSU? (inst-of-tag rix MT)))
		  (rob-index-p rix)
		  (not (b1p (inst-specultv? (inst-of-tag rix MT))))
		  (not (b1p (INST-modified? (inst-of-tag rix MT)))))
	     (b1p (CDB-for-LSU? MA)))
  :hints (("goal" :in-theory (enable CDB-def
				     BU-output-def
				     IU-output-def
				     BU-RS-field-inst-at-lemmas
				     MU-field-lemmas
				     LSU-field-lemmas
				     LSU-output-def
				     bv-eqv-iff-equal
				     lift-b-ops
				     equal-b1p-converter)))
  :rule-classes nil)

; If CDB-ready-for is 1 with Tomasulo's tag rix, and an MU instruction
; is assigned to the ROB entry designated by rix, CDB-for-MU? is 1.
(defthm CDB-for-MU-if-CDB-ready-for-INST-MU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (b1p (CDB-ready-for? rix MA))
		  (b1p (INST-MU? (inst-of-tag rix MT)))
		  (rob-index-p rix)
		  (not (b1p (inst-specultv? (inst-of-tag rix MT))))
		  (not (b1p (INST-modified? (inst-of-tag rix MT)))))
	     (b1p (CDB-for-MU? MA)))
  :hints (("goal" :in-theory (enable CDB-def
				     BU-output-def
				     IU-output-def
				     LSU-output-def
				     BU-RS-field-inst-at-lemmas
				     MU-field-inst-at-lemmas
				     LSU-field-inst-at-lemmas
				     MU-output-def
				     bv-eqv-iff-equal
				     lift-b-ops
				     equal-b1p-converter)))
  :rule-classes nil)

; If the operand of the completing instruction is 0(ADD), signal
; IU-output-val has destination value for an add instruction. 
; A help lemma to prove CDB-val-inst-dest-val-inst-of-tag-opcode-0.
(local
(defthm IU-output-val-INST-add-dest-val
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-opcode
			  (inst-of-tag (IU-output-tag (MA-IU MA)) MT))
			 0)
		  (b1p (CDB-for-IU? MA))
		  (not (b1p (inst-specultv?
			     (inst-of-tag (IU-output-tag (MA-IU MA)) MT))))
		  (not (b1p (INST-modified?
			     (inst-of-tag (IU-output-tag (MA-IU MA)) MT)))))
	     (equal (IU-output-val (MA-IU MA))
		    (INST-add-dest-val (inst-of-tag
					(IU-output-tag (MA-IU MA)) MT))))
  :hints (("goal" :in-theory (enable CDB-for-IU? lift-b-ops
				     IU-output-tag IU-output-val
				     IU-RS0-ISSUE-READY?
				     IU-RS1-ISSUE-READY?
				     IU-RS-field-INST-at-lemmas
				     INST-IU-op?
				     INST-cntlv
				     INST-add-dest-val)))))

; If the opcode of the completing instruction is 9,
; the correct destination value is on the CDB.
(defthm CDB-val-inst-dest-val-inst-of-tag-opcode-0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (b1p (CDB-ready-for? rix MA))
		  (rob-index-p rix)
		  (equal (INST-opcode (inst-of-tag rix MT)) 0)
		  (not (b1p (inst-specultv? (inst-of-tag rix MT))))
		  (not (b1p (INST-modified? (inst-of-tag rix MT)))))
	     (equal (CDB-val MA)
		    (INST-dest-val (inst-of-tag rix MT))))
  :hints (("goal" :in-theory (enable CDB-val INST-dest-val 
				     CDB-tag
				     lift-b-ops
				     INST-opcode
				     CDB-ready-for?
				     opcode-inst-type)
		  :use (:instance CDB-for-IU-if-CDB-ready-for-INST-IU))))

(local
(defthm IU-output-val-INST-mfsr-dest-val
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-opcode
			  (inst-of-tag (IU-output-tag (MA-IU MA)) MT))
			 9)
		  (b1p (CDB-for-IU? MA))
		  (not (b1p (inst-specultv?
			     (inst-of-tag (IU-output-tag (MA-IU MA)) MT))))
		  (not (b1p (INST-modified?
			     (inst-of-tag (IU-output-tag (MA-IU MA)) MT)))))
	     (equal (IU-output-val (MA-IU MA))
		    (INST-mfsr-dest-val (inst-of-tag
					(IU-output-tag (MA-IU MA)) MT))))
  :hints (("goal" :in-theory (enable CDB-for-IU? lift-b-ops
				     IU-output-tag IU-output-val
				     IU-RS0-ISSUE-READY?
				     IU-RS1-ISSUE-READY?
				     IU-RS-field-INST-at-lemmas
				     INST-IU-op?
				     INST-cntlv
				     INST-mfsr-dest-val)))))

; If the opcode of the completing instruction is 9,
; the correct destination value is on the CDB.
(defthm CDB-val-inst-dest-val-inst-of-tag-opcode-9
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (rob-index-p rix)
		  (b1p (CDB-ready-for? rix MA))
		  (equal (INST-opcode (inst-of-tag rix MT)) 9)
		  (not (b1p (inst-specultv? (inst-of-tag rix MT))))
		  (not (b1p (INST-modified? (inst-of-tag rix MT)))))
	     (equal (CDB-val MA)
		    (INST-dest-val (inst-of-tag rix MT))))
    :hints (("goal" :in-theory (enable CDB-val INST-dest-val 
				     CDB-tag
				     lift-b-ops
				     INST-opcode
				     INST-IU? INST-cntlv
				     CDB-ready-for?
				     opcode-inst-type)
		    :use (:instance CDB-for-IU-if-CDB-ready-for-INST-IU))))

(local
(defthm IU-output-val-INST-mtsr-dest-val
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-opcode
			  (inst-of-tag (IU-output-tag (MA-IU MA)) MT))
			 10)
		  (b1p (CDB-for-IU? MA))
		  (not (b1p (inst-specultv?
			     (inst-of-tag (IU-output-tag (MA-IU MA)) MT))))
		  (not (b1p (INST-modified?
			     (inst-of-tag (IU-output-tag (MA-IU MA)) MT)))))
	     (equal (IU-output-val (MA-IU MA))
		    (INST-mtsr-dest-val (inst-of-tag
					(IU-output-tag (MA-IU MA)) MT))))
  :hints (("goal" :in-theory (enable CDB-for-IU? lift-b-ops
				     IU-output-tag IU-output-val
				     IU-RS0-ISSUE-READY?
				     IU-RS1-ISSUE-READY?
				     IU-RS-field-INST-at-lemmas
				     INST-IU-op?
				     INST-cntlv
				     INST-mtsr-dest-val)))))

; If the opcode of the completing instruction is 10, 
; the correct destination value is on the CDB.
(defthm CDB-val-inst-dest-val-inst-of-tag-opcode-10
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (rob-index-p rix)
		  (b1p (CDB-ready-for? rix MA))
		  (equal (INST-opcode (inst-of-tag rix MT)) 10)
		  (not (b1p (inst-specultv? (inst-of-tag rix MT))))
		  (not (b1p (INST-modified? (inst-of-tag rix MT)))))
	     (equal (CDB-val MA)
		    (INST-dest-val (inst-of-tag rix MT))))
  :hints (("goal" :in-theory (enable CDB-val INST-dest-val 
				     CDB-tag
				     lift-b-ops
				     INST-opcode
				     INST-IU? INST-cntlv
				     CDB-ready-for?
				     opcode-inst-type)
		    :use (:instance CDB-for-IU-if-CDB-ready-for-INST-IU))))

(encapsulate nil
(local
(defthm LSU-latch-val-INST-ld-dest-val-help
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg stg MT)
		  (or (equal stg '(LSU wbuf0 lch))
		      (equal stg '(LSU wbuf1 lch)))
		  (not (b1p (inst-specultv? (INST-at-stg stg MT))))
		  (not (b1p (INST-modified? (INST-at-stg stg MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (equal (opcode (INST-word (INST-at-stg stg MT))) 3)))
  :hints (("goal" :cases ((b1p (INST-store? (INST-at-stg stg MT))))
		  :in-theory (enable LSU-field-lemmas))
	  ("subgoal 1" :in-theory (e/d (opcode-inst-type INST-opcode)
		                    (LSU-STORE-IF-AT-LSU-WBUF))))))
(local
(defthm LSU-latch-val-INST-ld-dest-val
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (b1p (LSU-latch-valid? (LSU-lch (MA-LSU MA))))
		  (equal (INST-opcode (INST-at-stgs '((LSU lch)
						      (LSU wbuf0 lch)
						      (LSU wbuf1 lch))
						    MT))
			 3)
		  (not (INST-load-accs-error-detected-p
			(INST-at-stgs '((LSU lch)
					     (LSU wbuf0 lch)
					     (LSU wbuf1 lch))
					   MT)))
		  (not (b1p (inst-specultv?
			     (INST-at-stgs '((LSU lch)
					     (LSU wbuf0 lch)
					     (LSU wbuf1 lch))
					   MT))))
		  (not (b1p (INST-modified?
			     (INST-at-stgs '((LSU lch)
					     (LSU wbuf0 lch)
					     (LSU wbuf1 lch))
					   MT)))))
	     (equal (LSU-latch-val (LSU-lch (MA-LSU MA)))
		    (INST-ld-dest-val (INST-at-stgs '((LSU lch)
						      (LSU wbuf0 lch)
						      (LSU wbuf1 lch))
						    MT))))
  :hints (("goal" :use ((:instance uniq-inst-at-stgs*
				   (stgs '((LSU lch)
					   (LSU wbuf0 lch)
					   (LSU wbuf1 lch))))
			(:instance uniq-inst-at-stgs*
				   (stgs '((LSU wbuf0 lch)
					   (LSU wbuf1 lch)))))
		  :in-theory (e/d (inst-at-stgs* INST-DEST-VAL
                                     LSU-field-inst-at-lemmas
				     INST-opcode INST-LD-DEST-VAL)
				  ())))))

; If the opcode of the completing instruction is 3,
; the correct destination value is on the CDB.
(defthm CDB-val-inst-dest-val-inst-of-tag-opcode-3
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (rob-index-p rix)
		  (b1p (CDB-ready-for? rix MA))
		  (equal (INST-opcode (inst-of-tag rix MT)) 3)
		  (not (INST-load-accs-error-detected-p (inst-of-tag rix MT)))
		  (not (b1p (inst-specultv? (inst-of-tag rix MT))))
		  (not (b1p (INST-modified? (inst-of-tag rix MT)))))
	     (equal (CDB-val MA)
		    (INST-dest-val (inst-of-tag rix MT))))
  :hints (("goal" :in-theory (enable CDB-val CDB-ready-for?
				     INST-dest-val opcode-inst-type
				     CDB-tag
				     INST-LSU-if-INST-store
				     INST-LSU-if-INST-load
				     LSU-field-inst-at-lemmas
				     CDB-FOR-LSU?
				     INST-opcode
				     lift-b-ops)
		  :use (:instance CDB-for-LSU-if-CDB-ready-for-INST-LSU))))
)

(encapsulate nil
(local
(defthm LSU-latch-val-INST-ld-im-dest-val-help
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg stg MT)
		  (or (equal stg '(LSU wbuf0 lch))
		      (equal stg '(LSU wbuf1 lch)))
		  (not (b1p (inst-specultv? (INST-at-stg stg MT))))
		  (not (b1p (INST-modified? (INST-at-stg stg MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (equal (opcode (INST-word (INST-at-stg stg MT))) 6)))
  :hints (("goal" :cases ((b1p (INST-store? (INST-at-stg stg MT))))
		  :in-theory (enable LSU-field-lemmas))
	  ("subgoal 1" :in-theory (e/d (opcode-inst-type INST-opcode)
		                    (LSU-STORE-IF-AT-LSU-WBUF))))))
(local
(defthm LSU-latch-val-INST-ld-im-dest-val
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (b1p (LSU-latch-valid? (LSU-lch (MA-LSU MA))))
		  (equal (INST-opcode (INST-at-stgs '((LSU lch)
						      (LSU wbuf0 lch)
						      (LSU wbuf1 lch))
						    MT))
			 6)
		  (not (INST-load-accs-error-detected-p
			(INST-at-stgs '((LSU lch)
					(LSU wbuf0 lch)
					(LSU wbuf1 lch))
				      MT)))
		  (not (b1p (inst-specultv?
			     (INST-at-stgs '((LSU lch)
					     (LSU wbuf0 lch)
					     (LSU wbuf1 lch))
					   MT))))
		  (not (b1p (INST-modified?
			     (INST-at-stgs '((LSU lch)
					     (LSU wbuf0 lch)
					     (LSU wbuf1 lch))
					   MT)))))
     (equal (LSU-latch-val (LSU-lch (MA-LSU MA)))
	    (INST-ld-im-dest-val (INST-at-stgs '((LSU lch)
						 (LSU wbuf0 lch)
						 (LSU wbuf1 lch))
					       MT))))
  :hints (("goal" :use ((:instance uniq-inst-at-stgs*
				   (stgs '((LSU lch)
					   (LSU wbuf0 lch)
					   (LSU wbuf1 lch))))
			(:instance uniq-inst-at-stgs*
				   (stgs '((LSU wbuf0 lch)
					   (LSU wbuf1 lch)))))
		  :in-theory (e/d (inst-at-stgs* INST-DEST-VAL
						 LSU-field-inst-at-lemmas
				     INST-opcode INST-LD-DEST-VAL)
				  ())))))

; If the opcode of the completing instruction is 6,
; the correct destination value is on the CDB.
(defthm CDB-val-inst-dest-val-inst-of-tag-opcode-6
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (rob-index-p rix)
		  (b1p (CDB-ready-for? rix MA))
		  (equal (INST-opcode (inst-of-tag rix MT)) 6)
		  (not (INST-load-accs-error-detected-p (inst-of-tag rix MT)))
		  (not (b1p (inst-specultv? (inst-of-tag rix MT))))
		  (not (b1p (INST-modified? (inst-of-tag rix MT)))))
	     (equal (CDB-val MA)
		    (INST-dest-val (inst-of-tag rix MT))))
    :hints (("goal" :in-theory (enable CDB-val CDB-ready-for?
				     INST-dest-val opcode-inst-type
				     CDB-tag
				     INST-LSU-if-INST-store
				     INST-LSU-if-INST-load
				     CDB-FOR-LSU?
				     LSU-field-inst-at-lemmas
				     INST-opcode
				     lift-b-ops)
		  :use (:instance CDB-for-LSU-if-CDB-ready-for-INST-LSU))))
)

; If the opcode of the completing instruction is 1,
; the correct destination value is on the CDB.
(defthm CDB-val-inst-dest-val-inst-of-tag-opcode-1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (rob-index-p rix)
		  (b1p (CDB-ready-for? rix MA))
		  (equal (INST-opcode (inst-of-tag rix MT)) 1)
		  (not (b1p (inst-specultv? (inst-of-tag rix MT))))
		  (not (b1p (INST-modified? (inst-of-tag rix MT)))))
	     (equal (CDB-val MA)
		    (INST-dest-val (inst-of-tag rix MT))))
  :hints (("goal" :in-theory (enable CDB-val CDB-ready-for?
				     INST-dest-val opcode-inst-type
				     CDB-tag
				     CDB-FOR-MU?
				     MU-RS-field-inst-at-lemmas
				     INST-opcode
				     lift-b-ops
				     MU-field-lemmas
				     INST-MULT-dest-val)
		  :use (:instance CDB-for-MU-if-CDB-ready-for-INST-MU))))

; The val signal on the CDB contains the correct result of the
; instruction completing in this cycle.
(defthm CDB-val-inst-dest-val
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (b1p (CDB-ready-for? rix MA))
		  (rob-index-p rix)
		  (INST-writeback-p (inst-of-tag rix MT))
		  (not (INST-excpt-detected-p (inst-of-tag rix MT)))
		  (not (b1p (inst-specultv? (inst-of-tag rix MT))))
		  (not (b1p (INST-modified? (inst-of-tag rix MT)))))
	     (equal (CDB-val MA)
		    (INST-dest-val (inst-of-tag rix MT))))
  :hints (("goal" :in-theory (enable INST-writeback-p INST-opcode
				     INST-DATA-ACCS-ERROR-DETECTED-P
				     INST-excpt-detected-p))))

(defthm CDB-val-inst-dest-val*
    (let ((j (inst-of-tag (CDB-tag MA) MT)))
      (implies (and (and (inv MT MA) (MAETT-p MT) (MA-state-p MA) )
		    (INST-writeback-p j)
		    (not (b1p (inst-specultv? j)))
		    (not (b1p (INST-modified? j)))
		    (not (INST-excpt-detected-p j))
		    (b1p (CDB-ready? MA)))
	       (equal (CDB-val MA) (INST-dest-val j))))
  :hints (("goal" :in-theory (enable lift-b-ops CDB-ready-for?
				     bv-eqv-iff-equal )
		  :restrict ((CDB-val-inst-dest-val
			      ((rix (CDB-tag MA)))))))
  :rule-classes nil)

(in-theory (disable CDB-val-inst-dest-val-inst-of-tag-opcode-0
		    CDB-val-inst-dest-val-inst-of-tag-opcode-1
		    CDB-val-inst-dest-val-inst-of-tag-opcode-3
		    CDB-val-inst-dest-val-inst-of-tag-opcode-6
		    CDB-val-inst-dest-val-inst-of-tag-opcode-9
		    CDB-val-inst-dest-val-inst-of-tag-opcode-10))
(in-theory (disable CDB-val-inst-dest-val))

(in-theory (disable uniq-inst-of-tag-if-CDB-ready-for))

;;;;;;;;End of lemmas about CDB output;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;Proof of INST-inv continues;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;Proof of IU-inst-inv;;;;;;;;;;;;;;;;;;;;;;;;;;;
(encapsulate nil
(local
(defthm complete-stg-LRM-before
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (exist-uncommitted-LRM-before-p I rname MT)
		  (equal (INST-stg i) '(DQ 0))
		  (b1p (robe-complete? 
			(nth-robe
			 (INST-tag (LRM-before i rname MT))
			 (MA-rob MA)))))
     (complete-stg-p (INST-stg (LRM-before i rname MT))))
  :hints (("goal" :in-theory (disable INST-in-order-LRM-before
				      INST-is-at-one-of-the-stages
				      committed-p)
		  :use ((:instance INST-is-at-one-of-the-stages
			     (i (LRM-before i rname MT)))
			(:instance INST-in-order-LRM-before))))))

(local
(defthm complete-stg-LSRM-before
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (exist-uncommitted-LSRM-before-p I rname MT)
		  (equal (INST-stg i) '(DQ 0))
		  (b1p (robe-complete? 
			(nth-robe
			 (INST-tag (LSRM-before i rname MT))
			 (MA-rob MA)))))
     (complete-stg-p (INST-stg (LSRM-before i rname MT))))
  :hints (("goal" :in-theory (disable INST-in-order-LSRM-before
				      INST-is-at-one-of-the-stages
				      committed-p)
		  :use ((:instance INST-is-at-one-of-the-stages
			     (i (LSRM-before i rname MT)))
			(:instance INST-in-order-LSRM-before)))))
)

; A critical lemma. 
; When an instruction is dispatched, its operand may be obtained from
; the ROB, where register values are temporarily stored.  Signal
; DQ-out-tag1 from the dispatch logic designates the ROB entry where
; the first operand for the dispatched instruction is temporarily
; stored.  The robe-val field of the ROB entry designated by
; DQ-out-tag1 is equal to the ideal first operand value
; (INST-src-val1 i) for instruction i, when the instruction at the
; ROB entry has completed its execution.
(defthm robe-val-DQ-out-tag1-INST-src-val1-if-IU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-IU? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (robe-complete? (nth-robe (DQ-out-tag1 (MA-DQ MA))
						 (MA-ROB MA))))
		  (not (b1p (DQ-out-ready1? (MA-DQ MA)))))
	     (equal (robe-val (nth-robe (DQ-out-tag1 (MA-DQ MA))
					(MA-ROB MA)))
		    (INST-src-val1 i)))
  :hints (("goal" :in-theory (e/d (DQ-out-ready1?
				   DQ-out-tag1
				   INST-SRC-val1
				   INST-cntlv  
				   INST-DECODE-ERROR-DETECTED-P
				   dispatch-to-IU?
				   DQ-ready-to-IU?
				   decode logbit* rdb
				   exception-relations
				   INST-exunit-relations
				   equal-b1p-converter
				   lift-b-ops)
				  (INST-decode-error-if-INST-ra-not-srname-p
				   RETIRED-DISPATCHED-INST
				   UNIQ-INST-OF-TAG-IF-ROBE-VALID
				   ROBE-COMPLETE-NTH-ROBE-RIX
				   COMPLETED-DISPATCHED-INST
				   )))
	  (when-found (EQUAL '9 (INST-OPCODE I))
		      (:use
		       (:instance INST-decode-error-if-INST-ra-not-srname-p)))
	  (when-found (b1p (INST-decode-error? i))
		      (:cases ((b1p (INST-fetch-error? i)))))))

; A critical lemma. 
; As discussed in the comment for the previous lemma, operands may be
; obtained from the ROB.  The robe-val field of the ROB entry designated by
; DQ-out-tag2 is equal to the ideal operand value (INST-src-val2 i) for the
; dispatched instruction i, if the instruction in the ROB entry has completed.
(defthm robe-val-DQ-out-tag2-INST-src-val2-if-IU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-IU? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (robe-complete? (nth-robe (DQ-out-tag2 (MA-DQ MA))
						 (MA-ROB MA))))
		  (not (b1p (DQ-out-ready2? (MA-DQ MA)))))
	     (equal (robe-val (nth-robe (DQ-out-tag2 (MA-DQ MA))
					(MA-ROB MA)))
		    (INST-src-val2 i)))
  :hints (("goal" :in-theory (e/d (DQ-out-ready2?
				   DQ-out-tag2
				   INST-SRC-val2
				   INST-cntlv
				   INST-DECODE-ERROR-DETECTED-P
				   dispatch-to-IU?
				   DQ-ready-to-IU?
				   equal-b1p-converter
				   lift-b-ops)
				  (INST-decode-error-if-INST-ra-not-srname-p
				   RETIRED-DISPATCHED-INST
				   UNIQ-INST-OF-TAG-IF-ROBE-VALID
				   ROBE-COMPLETE-NTH-ROBE-RIX
				   COMPLETED-DISPATCHED-INST)))))
)

; A critical lemma. 
; CDB-val-INST-src-val1-if-dispatch-IU
; The value on the CDB is the first operand for instruction i, when
; CDB-ready-for? is true for DQ-out-tag1, i.e., the
; first source operand is just in time ready on the CDB.
; This shows that the forwarding logic is working fine. 
;
; Proof of CDB-val-INST-src-val1-if-dispatch-IU
; The sketch of the proof is like this.
; (INST-src-val1 i) = (read-reg rname (ISA-RF (INST-Pre-ISA i))).
; The right hand side is actually the destination value of 
; the last register modifier before i 
;                   = (INST-dest-val (LRM-before i rname MT)
; Since i is at stage (DQ 0),
;                   = (INST-dest-val (inst-of-tag (reg-ref-tag rname MA)) 
;                   = (INST-dest-val (inst-of-tag (DQ-out-tag1 (MA-DQ-MA))))
; This value is returned through CDB when CDB-ready-for? flag is on,
;                   = (CDB-val MA)
(defthm CDB-val-INST-src-val1-if-dispatch-IU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-IU? MA)) 
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (CDB-ready-for? (DQ-out-tag1 (MA-DQ MA)) MA))
		  (not (b1p (robe-complete? (nth-robe (DQ-out-tag1 (MA-DQ MA))
						      (MA-ROB MA)))))
		  (not (b1p (DQ-out-ready1? (MA-DQ MA)))))
	     (equal (CDB-val MA) (INST-src-val1 i)))
  :hints (("goal" :in-theory (enable INST-src-val1
				     CDB-val-inst-dest-val
				     DQ-out-tag1
				     lift-b-ops
				     INST-cntlv
				     DISPATCH-TO-IU?
				     DQ-READY-TO-IU?
				     INST-DECODE-ERROR-DETECTED-P
				     DQ-out-ready1?))))

; Similar to CDB-val-INST-src-val1-if-dispatch-IU.
; The value on the CDB is the second operand of for instruction i, when
; CDB-ready-for? is true for DQ-out-tag2.
; See CDB-val-INST-src-val1-if-dispatch-IU.
(defthm CDB-val-INST-src-val2-if-dispatch-IU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-IU? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (CDB-ready-for? (DQ-out-tag2 (MA-DQ MA)) MA))
		  (not (b1p (robe-complete? (nth-robe (DQ-out-tag2 (MA-DQ MA))
						      (MA-ROB MA)))))
		  (not (b1p (DQ-out-ready2? (MA-DQ MA)))))
	     (equal (CDB-val MA) (INST-src-val2 i)))
  :hints (("goal" :in-theory (enable INST-src-val2
				     CDB-val-inst-dest-val
				     DQ-out-tag2
				     lift-b-ops
				     INST-cntlv
				     DISPATCH-TO-IU?
				     DQ-READY-TO-IU?
				     INST-DECODE-ERROR-DETECTED-P
				     DQ-out-ready2?))))

(in-theory (disable CDB-val-INST-src-val1-if-dispatch-IU
		    CDB-val-INST-src-val2-if-dispatch-IU))

; An output signal dispatch-val1 from the dispatching logic designates
; the first operand of the dispatched instruction i.
; The proof derives from
;  robe-val-DQ-out-tag1-INST-src-val1-if-IU and
;  CDB-val-INST-src-val1-if-dispatch-IU.
(defthm dispatch-val1-INST-src-val1-if-dispatched-to-IU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (dispatch-to-IU? MA))
		  (b1p (dispatch-ready1? MA)))
	     (equal (dispatch-val1 MA) (INST-src-val1 i)))
  :hints (("goal" :in-theory (enable dispatch-ready1? dispatch-val1
				     CDB-val-INST-src-val1-if-dispatch-IU
				     lift-b-ops))))

; An output signal dispatch-val2 from the dispatching logic is the second
; operand of the dispatched instruction i.
(defthm dispatch-val2-INST-src-val2-if-dispatch-to-IU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (INST-in i MT)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (dispatch-to-IU? MA))
		  (b1p (dispatch-ready2? MA)))
	     (equal (dispatch-val2 MA) (INST-src-val2 i)))
  :hints (("goal" :in-theory (enable dispatch-ready2? dispatch-val2
				     CDB-val-INST-src-val2-if-dispatch-IU
				     lift-b-ops))))

; The instruction invariants are preserved when instruction moves from
; (DQ 0) to (IU RS0).
(defthm IU-RS0-inst-inv-step-INST-from-DQ0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS)))
		  (equal (INST-stg i) '(DQ 0))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(IU RS0)))
	     (IU-RS0-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (e/d (lift-b-ops inst-inv-def
				     step-IU
				     step-IU-RS0
				     INST-IU-op?
				     INST-cntlv
				     equal-b1p-converter
				     INST-EXCPT-DETECTED-P
				     exception-relations
				     decode logbit* rdb
				     dispatch-inst?
				     dispatch-cntlv)
				  (INST-decode-error-if-INST-ra-not-srname-p))
		  :cases ((b1p (dispatch-inst? MA))))
	  ("subgoal 1" :cases ((b1p (INST-fetch-error? I))))
	  ("subgoal 1.2" :cases ((b1p (INST-decode-error? I))))
	  ("subgoal 1.2.2"
	   :use (:instance INST-decode-error-if-INST-ra-not-srname-p))))

; The instruction invariants are preserved when instruction moves from
; (DQ 0) to (IU RS1).
(defthm IU-RS1-inst-inv-step-INST-from-DQ0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS)))
		  (equal (INST-stg i) '(DQ 0))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(IU RS1)))
	     (IU-RS1-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops inst-inv-def
				     step-IU
				     step-IU-RS1
				     INST-IU-op?
				     INST-cntlv
				     equal-b1p-converter
				     exception-relations
				     decode logbit* rdb
				     dispatch-inst?)
		  :cases ((b1p (dispatch-inst? MA))))
	  ("subgoal 1" :cases ((b1p (INST-fetch-error? I))))
	  ("subgoal 1.2" :cases ((b1p (INST-decode-error? I))))
	  ("subgoal 1.2.2"
	   :use (:instance INST-decode-error-if-INST-ra-not-srname-p))))

; The RA field of an integer unit instruction that manipulates a special
; register designates a legitimate special register.
(defthm srname-p-INST-ra-cntlv-operand3
    (implies (and (b1p (logbit 3 (cntlv-operand (INST-cntlv i))))
		  (IU-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (srname-p (INST-ra i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter
						IU-stg-p)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

; No exception occurs in the IU. 
(defthm INST-excpt-detected-p-step-INST-IU
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (IU-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA) (INST-p i)
		  (MA-input-p sigs))
	     (not (INST-excpt-detected-p (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (e/d (INST-excpt-detected-p IU-STG-P) ()))))

; Suppose instruction i is in a reservation station.  If the first
; operand for i is not ready in the reservation station, there must be
; a register modifier of the operand register.  Since operand type is
; 1, it is the value of the register specified by ra.
(defthm exist-uncommitted-LRM-INST-ra-if-IU-RS0-cntlv-operand0
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(IU RS0))
		  (not (b1p (RS-ready1? (IU-RS0 (MA-IU MA)))))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i))))
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (INST-p i) (INST-in i MT))
	     (exist-uncommitted-LRM-before-p i (INST-ra i) MT))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Suppose instruction i is in a reservation station.
; If the first operand for i is not ready in the reservation station,
; there must be a register modifier of the operand register.
; Since operand type is 2, it is the value of the register specified by rc.
(defthm exist-uncommitted-LRM-INST-ra-if-IU-RS0-cntlv-operand2
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(IU RS0))
		  (not (b1p (RS-ready1? (IU-RS0 (MA-IU MA)))))
		  (b1p (logbit 2 (cntlv-operand (INST-cntlv i))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (exist-uncommitted-LRM-before-p i (INST-rc i) MT))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Suppose instruction i is in a reservation station.  If the first
; operand for i is not ready in the reservation station, there must be
; a register modifier of the operand register.  Since operand type is
; 3, it is the value of the register specified by ra.
(defthm exist-uncommitted-LRM-INST-ra-if-IU-RS0-cntlv-operand3
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(IU RS0))
		  (not (b1p (RS-ready1? (IU-RS0 (MA-IU MA)))))
		  (b1p (logbit 3 (cntlv-operand (INST-cntlv i))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (exist-uncommitted-LSRM-before-p i (INST-ra i) MT))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Suppose instruction i is in a reservation station.
; If the second operand for i is not ready in the reservation station,
; there must be a register modifier of the operand register.
(defthm exist-uncommitted-LRM-INST-rb-if-IU-RS0-cntlv-operand0
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(IU RS0))
		  (not (b1p (RS-ready2? (IU-RS0 (MA-IU MA)))))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (exist-uncommitted-LRM-before-p i (INST-rb i) MT))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Src1 field of a reservation station contains the tag to refer to
; the last register modifier of the first operand register.
; This lemma directly derives from the consistent-RS-p.
; See the def. of consistent-RS-p.  Similar to the following
; two lemmas. 
(defthm IU-RS0-src1-INST-tag-LRM-before-if-cntlv-operand0
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(IU RS0))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i))))
		  (not (b1p (RS-ready1? (IU-RS0 (MA-IU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (RS-src1 (IU-RS0 (MA-IU MA)))
		    (INST-tag (LRM-before i (INST-ra i) MT))))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))
  
(defthm IU-RS0-src1-INST-tag-LRM-before-if-cntlv-operand2
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(IU RS0))
		  (b1p (logbit 2 (cntlv-operand (INST-cntlv i))))
		  (not (b1p (RS-ready1? (IU-RS0 (MA-IU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (RS-src1 (IU-RS0 (MA-IU MA)))
		    (INST-tag (LRM-before i (INST-rc i) MT))))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

(defthm IU-RS0-src1-INST-tag-LRM-before-if-cntlv-operand3
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(IU RS0))
		  (b1p (logbit 3 (cntlv-operand (INST-cntlv i))))
		  (not (b1p (RS-ready1? (IU-RS0 (MA-IU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (RS-src1 (IU-RS0 (MA-IU MA)))
		    (INST-tag (LSRM-before i (INST-ra i) MT))))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))
  
; Src2 field of a reservation station contains the tag to refer to
; the last register modifier of the second operand register.
; This lemma directly derives from the consistent-RS-p.
(defthm IU-RS0-src2-INST-tag-LRM-before
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(IU RS0))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i))))
		  (not (b1p (RS-ready2? (IU-RS0 (MA-IU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (RS-src2 (IU-RS0 (MA-IU MA)))
		    (INST-tag (LRM-before i (INST-rb i) MT))))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Following four lemmas are similar lemmas for reservation station 2.
; See the comment of
;   IU-RS0-src1-INST-tag-LRM-before-if-cntlv-operand0
(defthm exist-uncommitted-LRM-INST-ra-if-IU-RS1-cntlv-operand0
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(IU RS1))
		  (not (b1p (RS-ready1? (IU-RS1 (MA-IU MA)))))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (exist-uncommitted-LRM-before-p i (INST-ra i) MT))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

(defthm exist-uncommitted-LRM-INST-ra-if-IU-RS1-cntlv-operand2
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(IU RS1))
		  (not (b1p (RS-ready1? (IU-RS1 (MA-IU MA)))))
		  (b1p (logbit 2 (cntlv-operand (INST-cntlv i))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (exist-uncommitted-LRM-before-p i (INST-rc i) MT))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

(defthm exist-uncommitted-LRM-INST-ra-if-IU-RS1-cntlv-operand3
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(IU RS1))
		  (not (b1p (RS-ready1? (IU-RS1 (MA-IU MA)))))
		  (b1p (logbit 3 (cntlv-operand (INST-cntlv i))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (exist-uncommitted-LSRM-before-p i (INST-ra i) MT))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

(defthm exist-uncommitted-LRM-INST-rb-if-IU-RS1-cntlv-operand0
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(IU RS1))
		  (not (b1p (RS-ready2? (IU-RS1 (MA-IU MA)))))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (exist-uncommitted-LRM-before-p i (INST-rb i) MT))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Src1 field of a reservation station contains the tag to refer to
; the last register modifier of the first operand register.
; See IU-RS0-src1-INST-tag-LRM-before-if-cntlv-operand0.
(defthm IU-RS1-src1-INST-tag-LRM-before-if-cntlv-operand0
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(IU RS1))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i))))
		  (not (b1p (RS-ready1? (IU-RS1 (MA-IU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (RS-src1 (IU-RS1 (MA-IU MA)))
		    (INST-tag (LRM-before i (INST-ra i) MT))))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))
  
(defthm IU-RS1-src1-INST-tag-LRM-before-if-cntlv-operand2
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(IU RS1))
		  (b1p (logbit 2 (cntlv-operand (INST-cntlv i))))
		  (not (b1p (RS-ready1? (IU-RS1 (MA-IU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (RS-src1 (IU-RS1 (MA-IU MA)))
		    (INST-tag (LRM-before i (INST-rc i) MT))))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

(defthm IU-RS1-src1-INST-tag-LRM-before-if-cntlv-operand3
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(IU RS1))
		  (b1p (logbit 3 (cntlv-operand (INST-cntlv i))))
		  (not (b1p (RS-ready1? (IU-RS1 (MA-IU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (RS-src1 (IU-RS1 (MA-IU MA)))
		    (INST-tag (LSRM-before i (INST-ra i) MT))))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))
  
; Src2 field of a reservation station contains the tag to refer to
; the last register modifier of the second operand register.
(defthm IU-RS1-src2-INST-tag-LRM-before
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(IU RS1))
		  (b1p (logbit 0 (cntlv-operand (INST-cntlv i))))
		  (not (b1p (RS-ready2? (IU-RS1 (MA-IU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (RS-src2 (IU-RS1 (MA-IU MA)))
		    (INST-tag (LRM-before i (INST-rb i) MT))))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

(encapsulate nil
; local lemma that shows that the value on the CDB is the correct
; source operand value. 
(local
(defthm CDB-val-INST-src-val1-if-CDB-ready-for
     (implies (and (equal (INST-stg i) '(IU RS0))
		   (not (b1p (RS-ready1? (IU-RS0 (MA-IU MA)))))
		   (b1p (CDB-ready-for? (RS-src1 (IU-RS0 (MA-IU MA))) MA))
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-p i) (INST-in i MT))
	      (equal (equal (CDB-val MA) (INST-src-val1 i)) T))
  :hints (("goal" :in-theory (e/d (CDB-VAL-INST-DEST-VAL
				   INST-cntlv
				   INST-IU?
				   equal-b1p-converter
				   decode logbit* rdb lift-b-ops
				   INST-src-val1)
				  (INST-IU-IF-IU-STG-P))
		  :use (:instance INST-IU-IF-IU-STG-P)))))

(local
(defthm CDB-val-INST-src-val2-if-CDB-ready-for
     (implies (and (equal (INST-stg i) '(IU RS0))
		   (not (b1p (RS-ready2? (IU-RS0 (MA-IU MA)))))
		   (b1p (CDB-ready-for? (RS-src2 (IU-RS0 (MA-IU MA))) MA))
		   (not (b1p (INST-IU-op? i)))
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-p i) (INST-in i MT))
	      (equal (equal (CDB-val MA) (INST-src-val2 i)) T))
  :hints (("goal" :in-theory (e/d (CDB-VAL-INST-DEST-VAL
				   INST-cntlv
				   INST-IU?
				   INST-IU-op?
				   equal-b1p-converter
				   decode logbit* rdb lift-b-ops
				   INST-src-val2)
				  (INST-IU-IF-IU-STG-P))
		  :use (:instance INST-IU-IF-IU-STG-P)))))

; The instruction invariants are preserved when an instruction stays
; in (IU RS0).
(defthm IU-RS0-inst-inv-step-INST-from-IU-RS0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg i) '(IU RS0))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(IU RS0)))
	     (IU-RS0-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops inst-inv-def
				     step-IU
				     step-IU-RS0
				     INST-IU-op?
				     exception-relations))))
)

(encapsulate nil
(local
(defthm CDB-val-INST-src-val1-if-CDB-ready-for
     (implies (and (equal (INST-stg i) '(IU RS1))
		   (not (b1p (RS-ready1? (IU-RS1 (MA-IU MA)))))
		   (b1p (CDB-ready-for? (RS-src1 (IU-RS1 (MA-IU MA))) MA))
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-p i) (INST-in i MT))
	      (equal (equal (CDB-val MA) (INST-src-val1 i)) T))
  :hints (("goal" :in-theory (e/d (CDB-VAL-INST-DEST-VAL
				   INST-cntlv
				   INST-IU?
				   equal-b1p-converter
				   decode logbit* rdb lift-b-ops
				   INST-src-val1)
				  (INST-IU-IF-IU-STG-P))
		  :use (:instance INST-IU-IF-IU-STG-P)))))

(local
(defthm CDB-val-INST-src-val2-if-CDB-ready-for
     (implies (and (equal (INST-stg i) '(IU RS1))
		   (not (b1p (RS-ready2? (IU-RS1 (MA-IU MA)))))
		   (b1p (CDB-ready-for? (RS-src2 (IU-RS1 (MA-IU MA))) MA))
		   (not (b1p (INST-IU-op? i)))
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-p i) (INST-in i MT))
	      (equal (equal (CDB-val MA) (INST-src-val2 i)) T))
  :hints (("goal" :in-theory (e/d (CDB-VAL-INST-DEST-VAL
				   INST-cntlv
				   INST-IU?
				   INST-IU-op?
				   equal-b1p-converter
				   decode logbit* rdb lift-b-ops
				   INST-src-val2)
				  (INST-IU-IF-IU-STG-P))
		  :use (:instance INST-IU-IF-IU-STG-P)))))

; The instruction invariants are preserved when an instruction stays
; in (IU RS1).
(defthm IU-RS1-inst-inv-step-INST-from-IU-RS1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg i) '(IU RS1))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(IU RS1)))
	     (IU-RS1-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops inst-inv-def
				     step-IU
				     step-IU-RS1
				     INST-IU-op?
				     exception-relations))))
)

; The instruction invariant is preserved for i, if i's next stage is
; (IU RS0).
(defthm IU-RS0-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS))) 
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(IU RS0)))
	     (IU-RS0-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :use (:instance stages-reachable-to-IU-RS0))))

; The instruction invariant is preserved for i, if i's next stage is
; (IU RS1).
(defthm IU-RS1-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS))) 
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(IU RS1)))
	     (IU-RS1-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :use (:instance stages-reachable-to-IU-RS1))))

; The instruction invariant is preserved for instruction i if i is
; in the integer unit in the next cycle.
(defthm IU-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS)))
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (IU-stg-p (INST-stg (step-INST I MT MA sigs))))
	     (IU-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable IU-stg-p IU-inst-inv))))

;;;;;;;;;;;Proof of MU-INST-inv;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Proof is similar to CDB-val-INST-src-val1-if-dispatch-IU
(encapsulate nil
(local
(defthm execute-stg-LRM-before
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (exist-uncommitted-LRM-before-p I rname MT)
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (robe-complete? 
			     (nth-robe
			      (INST-tag
			       (LRM-before i rname MT))
			      (MA-rob MA))))))
     (execute-stg-p (INST-stg (LRM-before i rname MT))))
  :hints (("goal" :in-theory (disable INST-in-order-LRM-before
				      INST-is-at-one-of-the-stages
				      committed-p)
		  :use ((:instance INST-is-at-one-of-the-stages
			     (i (LRM-before i rname MT)))
			(:instance INST-in-order-LRM-before))))))
(local
(defthm execute-stg-LSRM-before
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (exist-uncommitted-LSRM-before-p I rname MT)
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (robe-complete? 
			     (nth-robe
			      (INST-tag
			       (LSRM-before i rname MT))
			      (MA-rob MA))))))
     (execute-stg-p (INST-stg (LSRM-before i rname MT))))
  :hints (("goal" :in-theory (disable INST-in-order-LSRM-before
				      INST-is-at-one-of-the-stages
				      committed-p)
		  :use ((:instance INST-is-at-one-of-the-stages
				   (i (LSRM-before i rname MT)))
			(:instance INST-in-order-LSRM-before))))))

; The value on the CDB is the first operand  for instruction i, when
; CDB-ready-for? is true for DQ-out-tag1.
(defthm CDB-val-INST-src-val1-if-dispatch-MU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-MU? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (CDB-ready-for? (DQ-out-tag1 (MA-DQ MA)) MA))
		  (not (b1p (robe-complete? (nth-robe (DQ-out-tag1 (MA-DQ MA))
						      (MA-ROB MA)))))
		  (not (b1p (DQ-out-ready1? (MA-DQ MA)))))
	     (equal (CDB-val MA) (INST-src-val1 i)))
  :hints (("goal" :in-theory (enable INST-src-val1
				     CDB-val-inst-dest-val
				     DQ-out-tag1
				     lift-b-ops
				     INST-cntlv
				     DISPATCH-inst?
				     dispatch-to-MU?
				     DQ-READY-TO-MU?
				     INST-DECODE-ERROR-DETECTED-P
				     DQ-out-ready1?))))

; The value on the CDB is the second operand  for instruction i, when
; CDB-ready-for? is true for DQ-out-tag2.
(defthm CDB-val-INST-src-val2-if-dispatch-MU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-MU? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (CDB-ready-for? (DQ-out-tag2 (MA-DQ MA)) MA))
		  (not (b1p (robe-complete? (nth-robe (DQ-out-tag2 (MA-DQ MA))
						      (MA-ROB MA)))))
		  (not (b1p (DQ-out-ready2? (MA-DQ MA)))))
	     (equal (CDB-val MA) (INST-src-val2 i)))
  :hints (("goal" :in-theory (enable INST-src-val2
				     CDB-val-inst-dest-val
				     DQ-out-tag2
				     lift-b-ops
				     INST-cntlv
				     DISPATCH-inst?
				     dispatch-to-MU?
				     DQ-READY-TO-MU?
				     INST-DECODE-ERROR-DETECTED-P
				     DQ-out-ready2?))))

)

(in-theory (disable CDB-val-INST-src-val1-if-dispatch-MU
		    CDB-val-INST-src-val2-if-dispatch-MU))

(encapsulate nil
(local
(defthm complete-stg-LRM-before
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (exist-uncommitted-LRM-before-p I rname MT)
		  (equal (INST-stg i) '(DQ 0))
		  (b1p (robe-complete? 
			(nth-robe
			 (INST-tag (LRM-before i rname MT))
			 (MA-rob MA)))))
     (complete-stg-p (INST-stg (LRM-before i rname MT))))
  :hints (("goal" :in-theory (disable INST-in-order-LRM-before
				      INST-is-at-one-of-the-stages
				      committed-p)
		  :use ((:instance INST-is-at-one-of-the-stages
			     (i (LRM-before i rname MT)))
			(:instance INST-in-order-LRM-before))))))

(local
(defthm complete-stg-LSRM-before
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (exist-uncommitted-LSRM-before-p I rname MT)
		  (equal (INST-stg i) '(DQ 0))
		  (b1p (robe-complete? 
			(nth-robe
			 (INST-tag (LSRM-before i rname MT))
			 (MA-rob MA)))))
     (complete-stg-p (INST-stg (LSRM-before i rname MT))))
  :hints (("goal" :in-theory (disable INST-in-order-LSRM-before
				      INST-is-at-one-of-the-stages
				      committed-p)
		  :use ((:instance INST-is-at-one-of-the-stages
			     (i (LSRM-before i rname MT)))
			(:instance INST-in-order-LSRM-before)))))
)

; When an instruction is dispatched, its operand may be obtained from
; the ROB, where register values are temporarily stored.  DQ-out-tag1
; designates the ROB entry where the first operand for the dispatched
; instruction is temporarily stored.  The lemma shows that the
; robe-val field of the ROB entry is equal to the first operand value
; for instruction i.
(defthm robe-val-DQ-out-tag1-INST-src-val1-if-dispatch-MU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-MU? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (robe-complete? (nth-robe (DQ-out-tag1 (MA-DQ MA))
						 (MA-ROB MA))))
		  (not (b1p (DQ-out-ready1? (MA-DQ MA)))))
	     (equal (robe-val (nth-robe (DQ-out-tag1 (MA-DQ MA))
					(MA-ROB MA)))
		    (INST-src-val1 i)))
  :hints (("goal" :in-theory (e/d (DQ-out-ready1?
				   DQ-out-tag1
				   INST-SRC-val1
				   INST-cntlv  ; decode rdb logbit*
				   INST-DECODE-ERROR-DETECTED-P
				   dispatch-to-MU?
				   DQ-ready-to-MU?
				   decode logbit* rdb
				   exception-relations
				   INST-exunit-relations
				   equal-b1p-converter
				   lift-b-ops)
				  ()))))

; As discussed in the comment for the previous lemma, operands may be
; obtained from the ROB.  The robe-val field of the ROB entry designated by
; DQ-out-tag2 is equal to the ideal operand value (INST-src-val2 i) for the
; dispatched instruction i.
(defthm robe-val-DQ-out-tag2-INST-src-val2-if-MU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-MU? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (robe-complete? (nth-robe (DQ-out-tag2 (MA-DQ MA))
						 (MA-ROB MA))))
		  (not (b1p (DQ-out-ready2? (MA-DQ MA)))))
	     (equal (robe-val (nth-robe (DQ-out-tag2 (MA-DQ MA))
					(MA-ROB MA)))
		    (INST-src-val2 i)))
  :hints (("goal" :in-theory (e/d (DQ-out-ready2?
				   DQ-out-tag2
				   INST-SRC-val2
				   INST-cntlv
				   INST-DECODE-ERROR-DETECTED-P
				   dispatch-to-MU?
				   DQ-ready-to-MU?
				   exception-relations
				   equal-b1p-converter
				   lift-b-ops)
				  (ROBE-VAL-DQ-OUT-TAG2-INST-SRC-VAL2-IF-IU)))))
)

; Signal dispatch-val1 from the dispatching logic is the first
; operand value for the dispatched instruction i.
; This combines the results of 
;  CDB-val-INST-src-val1-if-dispatch-MU 
;  robe-val-DQ-out-tag1-INST-src-val1-if-dispatch-MU
(defthm dispatch-val1-INST-src-val1-if-dispatched-to-MU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (dispatch-to-MU? MA))
		  (b1p (dispatch-ready1? MA)))
	     (equal (dispatch-val1 MA) (INST-src-val1 i)))
  :hints (("goal" :in-theory (enable dispatch-ready1? dispatch-val1
				     CDB-val-INST-src-val1-if-dispatch-MU
				     lift-b-ops))))

; Signal dispatch-val2 from the dispatching logic is the second
; operand value for the dispatched instruction i.
;    CDB-val-INST-src-val2-if-dispatch-MU
;    robe-val-DQ-out-tag2-INST-src-val2-if-MU
(defthm dispatch-val2-INST-src-val2-if-dispatched-to-MU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (INST-in i MT)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (dispatch-to-MU? MA))
		  (b1p (dispatch-ready2? MA)))
	     (equal (dispatch-val2 MA) (INST-src-val2 i)))
  :hints (("goal" :in-theory (enable dispatch-ready2? dispatch-val2
				     CDB-val-INST-src-val2-if-dispatch-MU
				     lift-b-ops))))

; The instruction invariants are preserved for instruction that
; moves from DQ0 to MU-RS0.
(defthm MU-RS0-inst-inv-step-INST-from-DQ0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i) (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS)))
		  (equal (INST-stg i) '(DQ 0))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(MU RS0)))
	     (MU-RS0-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (e/d (lift-b-ops inst-inv-def
					      lift-b-ops
					      step-MU step-MU-RS0
					      DQ-ready-to-MU?
					      INST-MU?
					      INST-cntlv 
					      equal-b1p-converter
					      INST-EXCPT-DETECTED-P
					      exception-relations
					      dispatch-inst? dispatch-to-MU?
					      dispatch-cntlv)
				  (INST-decode-error-if-INST-ra-not-srname-p))
		  :cases ((b1p (dispatch-inst? MA))))
	  ("subgoal 1" :cases ((b1p (INST-fetch-error? I))))
	  ("subgoal 1.2" :cases ((b1p (INST-decode-error? I))))))

					      
; The instruction invariants are preserved for instruction that
; moves from DQ0 to MU-RS1.
(defthm MU-RS1-inst-inv-step-INST-from-DQ0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i) (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS)))
		  (equal (INST-stg i) '(DQ 0))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(MU RS1)))
	     (MU-RS1-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
    :hints (("goal" :in-theory (e/d (lift-b-ops inst-inv-def
					      step-MU step-MU-RS1
					      INST-cntlv 
					      dispatch-inst?
					      equal-b1p-converter
					      INST-EXCPT-DETECTED-P
					      exception-relations)
				  ())
		  :cases ((b1p (dispatch-inst? MA))))
	  ("subgoal 1" :cases ((b1p (INST-fetch-error? I))))
	  ("subgoal 1.2" :cases ((b1p (INST-decode-error? I))))))

; No exception occurs in the MU.
(defthm INST-excpt-detected-p-step-INST-MU
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (MU-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA) (INST-p i)
		  (MA-input-p sigs))
	     (not (INST-excpt-detected-p (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (e/d (INST-excpt-detected-p MU-STG-P) ()))))

; Suppose instruction i is stored in a reservation station.
; If the first operand for i is not ready in the reservation station,
; there must be a register modifier of the operand register.
(defthm exist-uncommitted-LRM-INST-ra-if-MU-RS0
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(MU RS0))
		  (not (b1p (RS-ready1? (MU-RS0 (MA-MU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (exist-uncommitted-LRM-before-p i (INST-ra i) MT))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Suppose instruction i is stored in a reservation station.
; If the second operand for i is not ready in the reservation station,
; there must be a register modifier of the operand register.
(defthm exist-uncommitted-LRM-INST-rb-if-MU-RS0
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(MU RS0))
		  (not (b1p (RS-ready2? (MU-RS0 (MA-MU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (exist-uncommitted-LRM-before-p i (INST-rb i) MT))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Similar lemmas for RS1. 
(defthm exist-uncommitted-LRM-INST-ra-if-MU-RS1
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(MU RS1))
		  (not (b1p (RS-ready1? (MU-RS1 (MA-MU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (exist-uncommitted-LRM-before-p i (INST-ra i) MT))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Similar lemmas for RS1. 
(defthm exist-uncommitted-LRM-INST-rb-if-MU-RS1
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(MU RS1))
		  (not (b1p (RS-ready2? (MU-RS1 (MA-MU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (exist-uncommitted-LRM-before-p i (INST-rb i) MT))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Src1 field of a reservation station RS0 contains the tag referring to
; the last register modifier of the first operand register.
(defthm MU-RS0-src1-INST-tag-LRM-before
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(MU RS0))
		  (not (b1p (RS-ready1? (MU-RS0 (MA-MU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (RS-src1 (MU-RS0 (MA-MU MA)))
		    (INST-tag (LRM-before i (INST-ra i) MT))))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; A similar lemma for RS1.
(defthm MU-RS1-src1-INST-tag-LRM-before
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(MU RS1))
		  (not (b1p (RS-ready1? (MU-RS1 (MA-MU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (RS-src1 (MU-RS1 (MA-MU MA)))
		    (INST-tag (LRM-before i (INST-ra i) MT))))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Src1 field of a reservation station RS0 contains the tag referring to
; the last register modifier of the second operand register.
(defthm MU-RS0-src2-INST-tag-LRM-before
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(MU RS0))
		  (not (b1p (RS-ready2? (MU-RS0 (MA-MU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (RS-src2 (MU-RS0 (MA-MU MA)))
		    (INST-tag (LRM-before i (INST-rb i) MT))))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; A similar lemma for RS1.
(defthm MU-RS1-src2-INST-tag-LRM-before
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(MU RS1))
		  (not (b1p (RS-ready2? (MU-RS1 (MA-MU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (RS-src2 (MU-RS1 (MA-MU MA)))
		    (INST-tag (LRM-before i (INST-rb i) MT))))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

(encapsulate nil
#| 
Following lemmas are for presentation.

The following lemma tells what is (INST-src-val1 i) is for a multiply
instruction.
(defthm CDB-val-INST-src-val1-if-CDB-ready-for-MU-RS0
     (implies (and (equal (INST-stg i) '(MU RS0))
		   (not (b1p (RS-ready1? (MU-RS0 (MA-MU MA)))))
		   (b1p (CDB-ready-for? (RS-src1 (MU-RS0 (MA-MU MA))) MA))
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-p i) (INST-in i MT))
	      (equal (read-reg (INST-ra i)
			       (ISA-RF (INST-pre-ISA i)))
		     (INST-src-val1 i)))
  :hints (("goal" :in-theory (e/d (CDB-VAL-INST-DEST-VAL
				   INST-cntlv
				   INST-MU?
				   equal-b1p-converter
				   decode logbit* rdb lift-b-ops
				   INST-src-val1)
				  (INST-MU-IF-MU-STG-P))
		  :use (:instance INST-MU-IF-MU-STG-P))))

|#

(local
(defthm CDB-val-INST-src-val1-if-CDB-ready-for-MU-RS0
     (implies (and (equal (INST-stg i) '(MU RS0))
		   (not (b1p (RS-ready1? (MU-RS0 (MA-MU MA)))))
		   (b1p (CDB-ready-for? (RS-src1 (MU-RS0 (MA-MU MA))) MA))
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-p i) (INST-in i MT))
	      (equal (equal (CDB-val MA) (INST-src-val1 i)) T))
  :hints (("goal" :in-theory (e/d (CDB-VAL-INST-DEST-VAL
				   INST-cntlv
				   INST-MU?
				   equal-b1p-converter
				   decode logbit* rdb lift-b-ops
				   INST-src-val1)
				  (INST-MU-IF-MU-STG-P))
		  :use (:instance INST-MU-IF-MU-STG-P)))))

; This lemma is for presentation.
(local
(defthm CDB-val-INST-src-val1-if-CDB-ready-for-MU-RS0*
     (implies (and (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-p i) (INST-in i MT)
		   (equal (INST-stg i) '(MU RS0))
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (b1p (CDB-ready? MA))
		   (equal (CDB-tag MA) (RS-src1 (MU-RS0 (MA-MU MA))))
		   (not (b1p (RS-ready1? (MU-RS0 (MA-MU MA))))))
	      (equal (CDB-val MA)
		     (INST-src-val1 i)))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter
				   CDB-ready-for?) ())))
  :rule-classes nil))

(local
(defthm CDB-val-INST-src-val2-if-CDB-ready-for-MU-RS0
     (implies (and (equal (INST-stg i) '(MU RS0))
		   (not (b1p (RS-ready2? (MU-RS0 (MA-MU MA)))))
		   (b1p (CDB-ready-for? (RS-src2 (MU-RS0 (MA-MU MA))) MA))
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-p i) (INST-in i MT))
	      (equal (equal (CDB-val MA) (INST-src-val2 i)) T))
  :hints (("goal" :in-theory (e/d (CDB-VAL-INST-DEST-VAL
				   INST-cntlv
				   INST-IU?
				   INST-IU-op?
				   equal-b1p-converter
				   decode logbit* rdb lift-b-ops
				   INST-src-val2)
				  (INST-IU-IF-IU-STG-P))
		  :use (:instance INST-IU-IF-IU-STG-P)))))

; The instruction invariants are preserved for instruction i that stays
; in MU-RS0.
(defthm MU-RS0-inst-inv-step-INST-from-MU-RS0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i) (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg i) '(MU RS0))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(MU RS0)))
	     (MU-RS0-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops inst-inv-def
				     step-MU
				     step-MU-RS0
				     exception-relations))))
)

(encapsulate nil
(local
(defthm CDB-val-INST-src-val1-if-CDB-ready-for-MU-RS1
     (implies (and (equal (INST-stg i) '(MU RS1))
		   (not (b1p (RS-ready1? (MU-RS1 (MA-MU MA)))))
		   (b1p (CDB-ready-for? (RS-src1 (MU-RS1 (MA-MU MA))) MA))
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-p i) (INST-in i MT))
	      (equal (equal (CDB-val MA) (INST-src-val1 i)) T))
  :hints (("goal" :in-theory (e/d (CDB-VAL-INST-DEST-VAL
				   INST-cntlv
				   INST-MU?
				   equal-b1p-converter
				   decode logbit* rdb lift-b-ops
				   INST-src-val1)
				  (INST-MU-IF-MU-STG-P))
		  :use (:instance INST-MU-IF-MU-STG-P)))))

(local
(defthm CDB-val-INST-src-val2-if-CDB-ready-for-MU-RS1
     (implies (and (equal (INST-stg i) '(MU RS1))
		   (not (b1p (RS-ready2? (MU-RS1 (MA-MU MA)))))
		   (b1p (CDB-ready-for? (RS-src2 (MU-RS1 (MA-MU MA))) MA))
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-p i) (INST-in i MT))
	      (equal (equal (CDB-val MA) (INST-src-val2 i)) T))
  :hints (("goal" :in-theory (e/d (CDB-VAL-INST-DEST-VAL
				   INST-cntlv
				   INST-IU?
				   INST-IU-op?
				   equal-b1p-converter
				   decode logbit* rdb lift-b-ops
				   INST-src-val2)
				  (INST-IU-IF-IU-STG-P))
		  :use (:instance INST-IU-IF-IU-STG-P)))))

; The instruction invariants are preserved for instruction i that stays
; in MU-RS1.
(defthm MU-RS1-inst-inv-step-INST-from-MU-RS1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i) (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg i) '(MU RS1))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(MU RS1)))
	     (MU-RS1-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops inst-inv-def
				     step-MU
				     step-MU-RS1
				     exception-relations))))
)

; The instruction invariants are preserved for instruction i whose
; next state is MU-RS0.
(defthm MU-RS0-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i) (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS)))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(MU RS0)))
	     (MU-RS0-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :use (:instance stages-reachable-to-MU-RS0))))

; The instruction invariants are preserved for instruction i whose
; next state is MU-RS1.
(defthm MU-RS1-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i) (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS)))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(MU RS1)))
	     (MU-RS1-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
    :hints (("goal" :use (:instance stages-reachable-to-MU-RS1))))

; Instruction invariants are preserved for instruction i that moves
; from MU-RS0 to MU-lch1.
(defthm MU-lch1-inst-inv-step-INST-from-MU-RS0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i) (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg i) '(MU RS0))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(MU lch1)))
	     (MU-lch1-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops inst-inv-def
				     step-MU
				     step-MU-lch1
				     issue-MU-RS0? MU-RS1-ISSUE-READY?
				     issue-MU-RS1? MU-RS0-ISSUE-READY?
				     exception-relations))))

; Instruction invariants are preserved for instruction i that moves
; from MU-RS1 to MU-lch1.
(defthm MU-lch1-inst-inv-step-INST-from-MU-RS1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i) (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg i) '(MU RS1))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(MU lch1)))
	     (MU-lch1-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops inst-inv-def
				     step-MU
				     step-MU-lch1
				     issue-MU-RS0? MU-RS1-ISSUE-READY?
				     issue-MU-RS1? MU-RS0-ISSUE-READY?
				     exception-relations))))

; Instruction invariants are preserved for instruction i that stays
; in MU-lch1.
(defthm MU-lch1-inst-inv-step-INST-from-MU-lch1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i) (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg i) '(MU lch1))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(MU lch1)))
	     (MU-lch1-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops inst-inv-def
				     step-MU
				     step-MU-lch1
				     exception-relations))))

; Instruction invariants are preserved for instruction i whose next state
; is MU-lch1.
(defthm MU-lch1-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i) (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(MU lch1)))
	     (MU-lch1-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :use (:instance stages-reachable-to-MU-lch1))))

; Instruction invariants are preserved for instruction i that moves from
; MU-lch1 to MU-lch2.
(defthm MU-lch2-inst-inv-step-INST-from-MU-lch1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i) (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg i) '(MU lch1))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(MU lch2)))
	     (MU-lch2-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops inst-inv-def
				     step-MU
				     step-MU-lch2
				     exception-relations))))

; Instruction invariants are preserved for instruction i that stays
; in MU-lch2.
(defthm MU-lch2-inst-inv-step-INST-from-MU-lch2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i) (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg i) '(MU lch2))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(MU lch2)))
	     (MU-lch2-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops inst-inv-def
				     step-MU
				     step-MU-lch2
				     exception-relations))))

; Instruction invariants are preserved for instruction i whose next stage
; is MU-lch2.
(defthm MU-lch2-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i) (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(MU lch2)))
	     (MU-lch2-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :use (:instance stages-reachable-to-MU-lch2))))

; A landmark lemma.  The instruction invariants are preserved for
; instruction i whose next state is in the MU.
(defthm MU-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i) (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS)))
		  (MU-stg-p (INST-stg (step-INST I MT MA sigs))))
	     (MU-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable MU-stg-p MU-inst-inv))))

;;;;;;;;;;;;;;;;;;;;Proof of BU-inst-inv;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(encapsulate nil
(local
(defthm complete-stg-LRM-before
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (exist-uncommitted-LRM-before-p I rname MT)
		  (equal (INST-stg i) '(DQ 0))
		  (b1p (robe-complete? 
			(nth-robe
			 (INST-tag (LRM-before i rname MT))
			 (MA-rob MA)))))
     (complete-stg-p (INST-stg (LRM-before i rname MT))))
  :hints (("goal" :in-theory (disable INST-in-order-LRM-before
				      INST-is-at-one-of-the-stages
				      committed-p)
		  :use ((:instance INST-is-at-one-of-the-stages
			     (i (LRM-before i rname MT)))
			(:instance INST-in-order-LRM-before))))))

; As discussed in the comment for the previous lemma, operands may be
; obtained from the ROB.  The robe-val field of the ROB entry designated by
; DQ-out-tag3 contains the correct source operand value for the 
; dispatched instruction i.
(defthm robe-val-DQ-out-tag3-INST-src-val3-if-BU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-BU? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (robe-complete? (nth-robe (DQ-out-tag3 (MA-DQ MA))
						 (MA-ROB MA))))
		  (not (b1p (DQ-out-ready3? (MA-DQ MA)))))
	     (equal (robe-val (nth-robe (DQ-out-tag3 (MA-DQ MA))
					(MA-ROB MA)))
		    (INST-src-val3 i)))
  :hints (("goal" :in-theory (e/d (DQ-out-ready3?
				   DQ-out-tag3
				   INST-SRC-val3
				   INST-cntlv
				   INST-DECODE-ERROR-DETECTED-P
				   dispatch-to-BU?
				   DQ-ready-to-BU?
				   decode logbit* rdb
				   exception-relations
				   equal-b1p-converter
				   lift-b-ops)
				  ()))))
)

; Proof is similar to CDB-val-INST-src-val1-if-dispatch-IU
(encapsulate nil
(local
(defthm execute-stg-LRM-before
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (exist-uncommitted-LRM-before-p I rname MT)
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (robe-complete? 
			     (nth-robe
			      (INST-tag
			       (LRM-before i rname MT))
			      (MA-rob MA))))))
     (execute-stg-p (INST-stg (LRM-before i rname MT))))
  :hints (("goal" :in-theory (disable INST-in-order-LRM-before
				      INST-is-at-one-of-the-stages
				      committed-p)
		  :use ((:instance INST-is-at-one-of-the-stages
			     (i (LRM-before i rname MT)))
			(:instance INST-in-order-LRM-before))))))

; The value on the CDB is the third operand value for instruction i, when
; CDB-ready-for? is true for DQ-out-tag3.
(defthm CDB-val-INST-src-val-if-dispatch-BU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-BU? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (CDB-ready-for? (DQ-out-tag3 (MA-DQ MA)) MA))
		  (not (b1p (robe-complete? (nth-robe (DQ-out-tag3 (MA-DQ MA))
						      (MA-ROB MA)))))
		  (not (b1p (DQ-out-ready3? (MA-DQ MA)))))
	     (equal (CDB-val MA) (INST-src-val3 i)))
  :hints (("goal" :in-theory (enable INST-src-val1
				     cdb-val-inst-dest-val
				     INST-src-val3
				     DQ-out-tag3
				     lift-b-ops
				     INST-cntlv
				     DISPATCH-inst?
				     dispatch-to-BU?
				     DQ-READY-TO-BU?
				     INST-DECODE-ERROR-DETECTED-P
				     DQ-out-ready3?))))
)
(in-theory (disable CDB-val-INST-src-val-if-dispatch-BU))

; An output from the dispatching logic dispatch-val3 is the third
; operand of the dispatched instruction i.
; This combines the results of two lemmas:
;  robe-val-DQ-out-tag3-INST-src-val3-if-BU
;  CDB-val-INST-src-val-if-dispatch-BU
(defthm dispatch-val3-INST-src-val1-if-dispatched-to-BU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (dispatch-to-BU? MA))
		  (b1p (dispatch-ready3? MA)))
	     (equal (dispatch-val3 MA) (INST-src-val3 i)))
  :hints (("goal" :in-theory (enable dispatch-ready3? dispatch-val3
				     CDB-val-INST-src-val-if-dispatch-BU
				     lift-b-ops))))

; The instruction invariants are preserved for instruction i that moves
; from DQ0 to BU-RS0.
(defthm BU-RS0-inst-inv-step-INST-from-DQ0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS)))
		  (equal (INST-stg I) '(DQ 0))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(BU RS0)))
	     (BU-RS0-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (e/d (lift-b-ops inst-inv-def
					      step-BU step-BU-RS0
					      INST-cntlv 
					      dispatch-inst?
					      equal-b1p-converter
					      INST-EXCPT-DETECTED-P
					      exception-relations)
				  ())
		  :cases ((b1p (dispatch-inst? MA))))
	  ("subgoal 1" :cases ((b1p (INST-fetch-error? I))))
	  ("subgoal 1.2" :cases ((b1p (INST-decode-error? I))))))

; The instruction invariants are preserved for instruction i that moves
; from DQ0 to BU-RS1.
(defthm BU-RS1-inst-inv-step-INST-from-DQ0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS)))
		  (equal (INST-stg I) '(DQ 0))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(BU RS1)))
	     (BU-RS1-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (e/d (lift-b-ops inst-inv-def
					      step-BU step-BU-RS1
					      INST-cntlv 
					      dispatch-inst?
					      equal-b1p-converter
					      INST-EXCPT-DETECTED-P
					      exception-relations)
				  ())
		  :cases ((b1p (dispatch-inst? MA))))
	  ("subgoal 1" :cases ((b1p (INST-fetch-error? I))))
	  ("subgoal 1.2" :cases ((b1p (INST-decode-error? I))))))

; Exception does not occur in the BU.
(defthm INST-excpt-detected-p-step-INST-BU
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (BU-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA) (INST-p i)
		  (MA-input-p sigs))
	     (not (INST-excpt-detected-p (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (e/d (INST-excpt-detected-p BU-STG-P) ()))))

; Suppose instruction i is stored in a reservation station.
; If the first operand for i is not ready in the reservation station,
; there must be a register modifier of the operand register.
(defthm exist-uncommitted-LRM-INST-rc-if-BU-RS0
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(BU RS0))
		  (not (b1p (BU-RS-ready? (BU-RS0 (MA-BU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (exist-uncommitted-LRM-before-p i (INST-rc i) MT))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Similar to exist-uncommitted-LRM-INST-rc-if-BU-RS0.
(defthm exist-uncommitted-LRM-INST-rc-if-BU-RS1
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(BU RS1))
		  (not (b1p (BU-RS-ready? (BU-RS1 (MA-BU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (exist-uncommitted-LRM-before-p i (INST-rc i) MT))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Src field of a reservation station contains the tag to refer to
; the last register modifier of the operand register.
(defthm BU-RS0-src-INST-tag-LRM-before
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(BU RS0))
		  (not (b1p (BU-RS-ready? (BU-RS0 (MA-BU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (BU-RS-src (BU-RS0 (MA-BU MA)))
		    (INST-tag (LRM-before i (INST-rc i) MT))))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Similar to BU-RS0-src-INST-tag-LRM-before.
(defthm BU-RS1-src1-INST-tag-LRM-before
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(BU RS1))
		  (not (b1p (BU-RS-ready? (BU-RS1 (MA-BU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (BU-RS-src (BU-RS1 (MA-BU MA)))
		    (INST-tag (LRM-before i (INST-rc i) MT))))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

(encapsulate nil
(local
(defthm CDB-val-INST-src-val3-if-CDB-ready-for-BU-RS0
     (implies (and (equal (INST-stg i) '(BU RS0))
		   (not (b1p (BU-RS-ready? (BU-RS0 (MA-BU MA)))))
		   (b1p (CDB-ready-for? (BU-RS-src (BU-RS0 (MA-BU MA))) MA))
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-p i) (INST-in i MT))
	      (equal (equal (CDB-val MA) (INST-src-val3 i)) T))
  :hints (("goal" :in-theory (e/d (CDB-VAL-INST-DEST-VAL
				   INST-cntlv
				   INST-BU?
				   equal-b1p-converter
				   decode logbit* rdb lift-b-ops
				   INST-src-val3)
				  (INST-BU-IF-BU-STG-P))
		  :use (:instance INST-BU-IF-BU-STG-P)))))

; The instruction invariants are preserved for instruction i that stays
; in BU-RS0.
(defthm BU-RS0-inst-inv-step-INST-from-BU-RS0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg I) '(BU RS0))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(BU RS0)))
	     (BU-RS0-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops inst-inv-def
				     step-BU
				     step-BU-RS0
				     exception-relations))))
)

(encapsulate nil
(local
(defthm CDB-val-INST-src-val3-if-CDB-ready-for-BU-RS1
     (implies (and (equal (INST-stg i) '(BU RS1))
		   (not (b1p (BU-RS-ready? (BU-RS1 (MA-BU MA)))))
		   (b1p (CDB-ready-for? (BU-RS-src (BU-RS1 (MA-BU MA))) MA))
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-p i) (INST-in i MT))
	      (equal (equal (CDB-val MA) (INST-src-val3 i)) T))
  :hints (("goal" :in-theory (e/d (CDB-VAL-INST-DEST-VAL
				   INST-cntlv
				   INST-BU?
				   equal-b1p-converter
				   decode logbit* rdb lift-b-ops
				   INST-src-val3)
				  (INST-BU-IF-BU-STG-P))
		  :use (:instance INST-BU-IF-BU-STG-P)))))

; The instruction invariants are preserved for instruction i that stays
; in BU-RS1.
(defthm BU-RS1-inst-inv-step-INST-from-BU-RS1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg I) '(BU RS1))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(BU RS1)))
	     (BU-RS1-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops inst-inv-def
				     step-BU
				     step-BU-RS1
				     exception-relations))))
)

; The instruction invariants are preserved for instruction i whose next
; stage is BU-RS0.
(defthm BU-RS0-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS)))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(BU RS0)))
	     (BU-RS0-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :use (:instance stages-reachable-to-BU-RS0))))

; The instruction invariants are preserved for instruction i whose next
; stage is BU-RS1.
(defthm BU-RS1-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS)))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(BU RS1)))
	     (BU-RS1-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :use (:instance stages-reachable-to-BU-RS1))))

; The instruction invariants are preserved for instruction i which will be
; in BU in the next cycle.
(defthm BU-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS)))
		  (BU-stg-p (INST-stg (step-INST I MT MA sigs))))
	     (BU-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable BU-stg-p BU-inst-inv))))

;;;;;;;;;;;;;;;;;;;Proof of LSU-inst-inv-step-INST;;;;;;;;;;;;;;;;
; The proof of LSU-inst-inv-step-INST has following subgoals.
;   LSU-RS0-inst-inv-step-INST
;   LSU-RS1-inst-inv-step-INST
;   LSU-wbuf1-inst-inv-step-INST
;   LSU-wbuf0-inst-inv-step-INST
;   LSU-rbuf-inst-inv-step-INST
;   LSU-wbuf0-lch-inst-inv-step-INST
;   LSU-wbuf1-lch-inst-inv-step-INST
;   LSU-lch-inst-inv-step-INST
; LSU-lch-inst-inv-step-INST takes a considerable amount of work and
; this includes the proof for the load-bypassing and load-hoisting. 

(encapsulate nil
(local
(defthm complete-stg-LRM-before
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (exist-uncommitted-LRM-before-p I rname MT)
		  (equal (INST-stg i) '(DQ 0))
		  (b1p (robe-complete? 
			(nth-robe
			 (INST-tag (LRM-before i rname MT))
			 (MA-rob MA)))))
     (complete-stg-p (INST-stg (LRM-before i rname MT))))
  :hints (("goal" :in-theory (disable INST-in-order-LRM-before
				      INST-is-at-one-of-the-stages
				      committed-p)
		  :use ((:instance INST-is-at-one-of-the-stages
			     (i (LRM-before i rname MT)))
			(:instance INST-in-order-LRM-before))))))

; The robe-val field of the ROB entry designated by DQ-out-tag1
; contains the correct source operand value for the dispatched
; instruction i.
(defthm robe-val-DQ-out-tag1-INST-src-val1-if-LSU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-LSU? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (robe-complete? (nth-robe (DQ-out-tag1 (MA-DQ MA))
						 (MA-ROB MA))))
		  (not (b1p (DQ-out-ready1? (MA-DQ MA)))))
	     (equal (robe-val (nth-robe (DQ-out-tag1 (MA-DQ MA))
					(MA-ROB MA)))
		    (INST-src-val1 i)))
  :hints (("goal" :in-theory (e/d (DQ-out-ready1?
				   DQ-out-tag1
				   INST-SRC-val1
				   INST-cntlv
				   INST-DECODE-ERROR-DETECTED-P
				   dispatch-to-LSU?
				   DQ-ready-to-LSU?
				   decode logbit* rdb
				   exception-relations
				   equal-b1p-converter
				   lift-b-ops)
				  (RETIRED-DISPATCHED-INST
				   UNIQ-INST-OF-TAG-IF-ROBE-VALID
				   ROBE-COMPLETE-NTH-ROBE-RIX
				   COMPLETED-DISPATCHED-INST)))))

; The robe-val field of the ROB entry designated by DQ-out-tag2
; contains the correct source operand value for the dispatched
; instruction i.
(defthm robe-val-DQ-out-tag2-INST-src-val2-if-LSU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-LSU? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (robe-complete? (nth-robe (DQ-out-tag2 (MA-DQ MA))
						 (MA-ROB MA))))
		  (not (b1p (DQ-out-ready2? (MA-DQ MA)))))
	     (equal (robe-val (nth-robe (DQ-out-tag2 (MA-DQ MA))
					(MA-ROB MA)))
		    (INST-src-val2 i)))
  :hints (("goal" :in-theory (e/d (DQ-out-ready2?
				   DQ-out-tag2
				   INST-SRC-val2
				   INST-cntlv
				   INST-DECODE-ERROR-DETECTED-P
				   dispatch-to-LSU?
				   DQ-ready-to-LSU?
				   decode logbit* rdb
				   exception-relations
				   equal-b1p-converter
				   lift-b-ops)
				  (RETIRED-DISPATCHED-INST
				   UNIQ-INST-OF-TAG-IF-ROBE-VALID
				   ROBE-COMPLETE-NTH-ROBE-RIX
				   COMPLETED-DISPATCHED-INST)))))

; The robe-val field of the ROB entry designated by DQ-out-tag3
; contains the correct source operand value for the dispatched
; instruction i.
(defthm robe-val-DQ-out-tag3-INST-src-val3-if-LSU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-LSU? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (robe-complete? (nth-robe (DQ-out-tag3 (MA-DQ MA))
						 (MA-ROB MA))))
		  (not (b1p (DQ-out-ready3? (MA-DQ MA)))))
	     (equal (robe-val (nth-robe (DQ-out-tag3 (MA-DQ MA))
					(MA-ROB MA)))
		    (INST-src-val3 i)))
  :hints (("goal" :in-theory (e/d (DQ-out-ready3?
				   DQ-out-tag3
				   INST-SRC-val3
				   INST-cntlv
				   INST-DECODE-ERROR-DETECTED-P
				   decode logbit* rdb
				   exception-relations
				   equal-b1p-converter
				   lift-b-ops)
				  (RETIRED-DISPATCHED-INST
				   UNIQ-INST-OF-TAG-IF-ROBE-VALID
				   ROBE-COMPLETE-NTH-ROBE-RIX
				   COMPLETED-DISPATCHED-INST)))))
)

(encapsulate nil
(local
(defthm execute-stg-LRM-before
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (exist-uncommitted-LRM-before-p I rname MT)
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (robe-complete? 
			     (nth-robe
			      (INST-tag
			       (LRM-before i rname MT))
			      (MA-rob MA))))))
     (execute-stg-p (INST-stg (LRM-before i rname MT))))
  :hints (("goal" :in-theory (disable INST-in-order-LRM-before
				      INST-is-at-one-of-the-stages
				      committed-p)
		  :use ((:instance INST-is-at-one-of-the-stages
			     (i (LRM-before i rname MT)))
			(:instance INST-in-order-LRM-before))))))

; The value obtained from CDB is the correct operand value for instruction i.
(defthm CDB-val-INST-src-val1-if-dispatch-LSU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-LSU? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (CDB-ready-for? (DQ-out-tag1 (MA-DQ MA)) MA))
		  (not (b1p (robe-complete? (nth-robe (DQ-out-tag1 (MA-DQ MA))
						      (MA-ROB MA)))))
		  (not (b1p (DQ-out-ready1? (MA-DQ MA)))))
	     (equal (CDB-val MA) (INST-src-val1 i)))
  :hints (("goal" :in-theory (e/d (INST-src-val1
				     cdb-val-inst-dest-val
				     INST-src-val1
				     DQ-out-tag1
				     lift-b-ops
				     INST-cntlv
				     DISPATCH-inst?
				     dispatch-to-LSU?
				     DQ-READY-TO-LSU?
				     INST-DECODE-ERROR-DETECTED-P
				     DQ-out-ready1?)
				  (RETIRED-DISPATCHED-INST
				   UNIQ-INST-OF-TAG-IF-ROBE-VALID
				   ROBE-COMPLETE-NTH-ROBE-RIX
				   COMPLETED-DISPATCHED-INST)))))

; The value obtained from CDB is the correct operand value for instruction i.
(defthm CDB-val-INST-src-val2-if-dispatch-LSU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-LSU? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (CDB-ready-for? (DQ-out-tag2 (MA-DQ MA)) MA))
		  (not (b1p (robe-complete? (nth-robe (DQ-out-tag2 (MA-DQ MA))
						      (MA-ROB MA)))))
		  (not (b1p (DQ-out-ready2? (MA-DQ MA)))))
	     (equal (CDB-val MA) (INST-src-val2 i)))
  :hints (("goal" :in-theory (e/d (INST-src-val2
				     cdb-val-inst-dest-val
				     INST-src-val2
				     DQ-out-tag2
				     lift-b-ops
				     INST-cntlv
				     DISPATCH-inst?
				     dispatch-to-LSU?
				     DQ-READY-TO-LSU?
				     INST-DECODE-ERROR-DETECTED-P
				     DQ-out-ready2?)
				  (RETIRED-DISPATCHED-INST
				   UNIQ-INST-OF-TAG-IF-ROBE-VALID
				   ROBE-COMPLETE-NTH-ROBE-RIX
				   COMPLETED-DISPATCHED-INST)))))

; The value obtained from CDB is the correct operand value for instruction i.
(defthm CDB-val-INST-src-val3-if-dispatch-LSU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-LSU? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (CDB-ready-for? (DQ-out-tag3 (MA-DQ MA)) MA))
		  (not (b1p (robe-complete? (nth-robe (DQ-out-tag3 (MA-DQ MA))
						      (MA-ROB MA)))))
		  (not (b1p (DQ-out-ready3? (MA-DQ MA)))))
	     (equal (CDB-val MA) (INST-src-val3 i)))
  :hints (("goal" :in-theory (e/d (INST-src-val3
				     cdb-val-inst-dest-val
				     INST-src-val3
				     DQ-out-tag3
				     lift-b-ops
				     INST-cntlv
				     DISPATCH-inst?
				     dispatch-to-LSU?
				     DQ-READY-TO-LSU?
				     INST-DECODE-ERROR-DETECTED-P
				     DQ-out-ready3?)
				  (RETIRED-DISPATCHED-INST
				   UNIQ-INST-OF-TAG-IF-ROBE-VALID
				   ROBE-COMPLETE-NTH-ROBE-RIX
				   COMPLETED-DISPATCHED-INST)))))
)
(in-theory (disable CDB-val-INST-src-val1-if-dispatch-LSU
		    CDB-val-INST-src-val2-if-dispatch-LSU
		    CDB-val-INST-src-val3-if-dispatch-LSU))

; An output signal dispatch-val1 from the dispatching logic is the first
; operand of the dispatched instruction i.
; This combines the result of 
;   robe-val-DQ-out-tag1-INST-src-val1-if-LSU
;   CDB-val-INST-src-val1-if-dispatch-LSU
(defthm dispatch-val1-INST-src-val1-if-dispatched-to-LSU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (dispatch-to-LSU? MA))
		  (b1p (dispatch-ready1? MA)))
	     (equal (dispatch-val1 MA) (INST-src-val1 i)))
  :hints (("goal" :in-theory (enable dispatch-ready1? dispatch-val1
				     CDB-val-INST-src-val1-if-dispatch-LSU
				     lift-b-ops))))

; An output signal dispatch-val2 from the dispatching logic is the second
; operand of the dispatched instruction i.
; This combines the result of 
;    robe-val-DQ-out-tag2-INST-src-val2-if-LSU
;    CDB-val-INST-src-val2-if-dispatch-LSU
(defthm dispatch-val2-INST-src-val2-if-dispatched-to-LSU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (dispatch-to-LSU? MA))
		  (b1p (dispatch-ready2? MA)))
	     (equal (dispatch-val2 MA) (INST-src-val2 i)))
  :hints (("goal" :in-theory (enable dispatch-ready2? dispatch-val2
				     CDB-val-INST-src-val2-if-dispatch-LSU
				     lift-b-ops))))

; An output signal dispatch-val3 from the dispatching logic is the third
; operand of the dispatched instruction i.
; This combines the result of 
;   robe-val-DQ-out-tag3-INST-src-val3-if-LSU
;   CDB-val-INST-src-val3-if-dispatch-LSU
(defthm dispatch-val3-INST-src-val3-if-dispatched-to-LSU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (b1p (dispatch-to-LSU? MA))
		  (b1p (dispatch-ready3? MA)))
	     (equal (dispatch-val3 MA) (INST-src-val3 i)))
  :hints (("goal" :in-theory (enable dispatch-ready3? dispatch-val3
				     CDB-val-INST-src-val3-if-dispatch-LSU
				     lift-b-ops))))

; The operand type of the load store instruction is immediate (designated
; by (INST-LSU-op? i)), dispatch-ready1 is 1. 
(defthm dispatch-ready1-if-INST-LSU-op
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(DQ 0))
		  (b1p (INST-LSU-op? i))
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p I)))
	     (equal (dispatch-ready1? MA) 1))
  :hints (("goal" :in-theory (enable dispatch-ready1? lift-b-ops
				     DQ-out-ready1? INST-LSU-OP?
				     INST-cntlv
				     equal-b1p-converter))))

; The instruction invariants are preserved if i moves from DQ0 to LSU-RS0.
(defthm LSU-RS0-inst-inv-step-INST-from-DQ0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS)))
		  (equal (INST-stg I) '(DQ 0))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU RS0)))
	     (LSU-RS0-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (e/d (lift-b-ops inst-inv-def
					      step-LSU step-LSU-RS0
					      INST-cntlv 
					      dispatch-inst?
					      equal-b1p-converter
					      INST-EXCPT-DETECTED-P
					      exception-relations
					      INST-LSU-op? INST-ld-st?)
				  ())
		  :cases ((b1p (dispatch-inst? MA))))
	  ("subgoal 1" :cases ((b1p (INST-fetch-error? I))))
	  ("subgoal 1.2" :cases ((b1p (INST-decode-error? I))))))

; The instruction invariants are preserved if i moves from DQ0 to LSU-RS1.
(defthm LSU-RS1-inst-inv-step-INST-from-DQ0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS)))
		  (equal (INST-stg I) '(DQ 0))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU RS1)))
	     (LSU-RS1-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (e/d (lift-b-ops inst-inv-def
					      step-LSU step-LSU-RS1
					      INST-cntlv 
					      dispatch-inst?
					      equal-b1p-converter
					      INST-EXCPT-DETECTED-P
					      exception-relations
					      INST-LSU-op? INST-ld-st?)
				  ())
		  :cases ((b1p (dispatch-inst? MA))))
	  ("subgoal 1" :cases ((b1p (INST-fetch-error? I))))
	  ("subgoal 1.2" :cases ((b1p (INST-decode-error? I))))))

; No exception is detected at the reservation stations of LSU.
(defthm INST-excpt-detected-p-step-INST-LSU
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (or (equal (INST-stg i) '(LSU RS0))
		      (equal (INST-stg i) '(LSU RS1)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA) (INST-p i)
		  (MA-input-p sigs))
	     (not (INST-excpt-detected-p (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (e/d (INST-excpt-detected-p LSU-STG-P
				 INST-data-accs-error-detected-p
 				 INST-load-accs-error-detected-p
				 INST-store-accs-error-detected-p) ()))))

; Suppose instruction i is stored in a reservation station.
; If the first operand for i is not ready in the reservation station,
; there must be a register modifier of the operand register.
(defthm exist-uncommitted-LRM-INST-ra-if-LSU-RS0
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(LSU RS0))
		  (not (b1p (LSU-RS-rdy1? (LSU-RS0 (MA-LSU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (exist-uncommitted-LRM-before-p i (INST-ra i) MT))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Similar to exist-uncommitted-LRM-INST-ra-if-LSU-RS0.
(defthm exist-uncommitted-LRM-INST-ra-if-LSU-RS1
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(LSU RS1))
		  (not (b1p (LSU-RS-rdy1? (LSU-RS1 (MA-LSU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (exist-uncommitted-LRM-before-p i (INST-ra i) MT))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Similar to exist-uncommitted-LRM-INST-ra-if-LSU-RS0.
(defthm exist-uncommitted-LRM-INST-rb-if-LSU-RS0
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(LSU RS0))
		  (not (b1p (LSU-RS-rdy2? (LSU-RS0 (MA-LSU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (exist-uncommitted-LRM-before-p i (INST-rb i) MT))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Similar to exist-uncommitted-LRM-INST-ra-if-LSU-RS0.
(defthm exist-uncommitted-LRM-INST-rb-if-LSU-RS1
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(LSU RS1))
		  (not (b1p (LSU-RS-rdy2? (LSU-RS1 (MA-LSU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (exist-uncommitted-LRM-before-p i (INST-rb i) MT))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Similar to exist-uncommitted-LRM-INST-ra-if-LSU-RS0.
(defthm exist-uncommitted-LRM-INST-rc-if-LSU-RS0
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(LSU RS0))
		  (not (b1p (LSU-RS-rdy3? (LSU-RS0 (MA-LSU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (exist-uncommitted-LRM-before-p i (INST-rc i) MT))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Similar to exist-uncommitted-LRM-INST-ra-if-LSU-RS0.
(defthm exist-uncommitted-LRM-INST-rc-if-LSU-RS1
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(LSU RS1))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (LSU-RS-rdy3? (LSU-RS1 (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (exist-uncommitted-LRM-before-p i (INST-rc i) MT))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Src field of a reservation station contains the tag to refer to
; the last register modifier of the operand register.
(defthm LSU-RS0-src-INST-tag-LRM-before
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(LSU RS0))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (LSU-RS-rdy1? (LSU-RS0 (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (LSU-RS-src1 (LSU-RS0 (MA-LSU MA)))
		    (INST-tag (LRM-before i (INST-ra i) MT))))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Similar to LSU-RS0-src-INST-tag-LRM-before.
(defthm LSU-RS1-src1-INST-tag-LRM-before
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(LSU RS1))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (LSU-RS-rdy1? (LSU-RS1 (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (LSU-RS-src1 (LSU-RS1 (MA-LSU MA)))
		    (INST-tag (LRM-before i (INST-ra i) MT))))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Similar to LSU-RS0-src-INST-tag-LRM-before.
(defthm LSU-RS0-src2-INST-tag-LRM-before
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(LSU RS0))
		  (not (b1p (LSU-RS-rdy2? (LSU-RS0 (MA-LSU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (LSU-RS-src2 (LSU-RS0 (MA-LSU MA)))
		    (INST-tag (LRM-before i (INST-rb i) MT))))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Similar to LSU-RS0-src-INST-tag-LRM-before.
(defthm LSU-RS1-src2-INST-tag-LRM-before
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(LSU RS1))
		  (not (b1p (LSU-RS-rdy2? (LSU-RS1 (MA-LSU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (LSU-RS-src2 (LSU-RS1 (MA-LSU MA)))
		    (INST-tag (LRM-before i (INST-rb i) MT))))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Similar to LSU-RS0-src-INST-tag-LRM-before.
(defthm LSU-RS0-src3-INST-tag-LRM-before
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(LSU RS0))
		  (not (b1p (LSU-RS-rdy3? (LSU-RS0 (MA-LSU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (LSU-RS-src3 (LSU-RS0 (MA-LSU MA)))
		    (INST-tag (LRM-before i (INST-rc i) MT))))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

; Similar to LSU-RS0-src-INST-tag-LRM-before.
(defthm LSU-RS1-src3-INST-tag-LRM-before
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(LSU RS1))
		  (not (b1p (LSU-RS-rdy3? (LSU-RS1 (MA-LSU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (LSU-RS-src3 (LSU-RS1 (MA-LSU MA)))
		    (INST-tag (LRM-before i (INST-rc i) MT))))
  :hints (("goal" :in-theory (enable consistent-RS-p-def)
		  :use (:instance consistent-RS-entry-p-if-INST-in))))

(encapsulate nil
(local
(defthm CDB-val-INST-src-val1-if-CDB-ready-for-LSU-RS0
     (implies (and (equal (INST-stg i) '(LSU RS0))
		   (not (b1p (LSU-RS-rdy1? (LSU-RS0 (MA-LSU MA)))))
		   (b1p (CDB-ready-for?
			 (LSU-RS-src1 (LSU-RS0 (MA-LSU MA))) MA))
		   (not (b1p (INST-LSU-op? i)))
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-p i) (INST-in i MT))
	      (equal (equal (CDB-val MA) (INST-src-val1 i)) T))
  :hints (("goal" :in-theory (e/d (CDB-VAL-INST-DEST-VAL
				   INST-cntlv
				   INST-LSU?
				   equal-b1p-converter
				   decode logbit* rdb lift-b-ops
				   INST-LSU-op?
				   INST-src-val1)
				  (INST-LSU-IF-LSU-STG-P))
		  :use (:instance INST-LSU-IF-LSU-STG-P)))))

(local
(defthm CDB-val-INST-src-val2-if-CDB-ready-for-LSU-RS0
     (implies (and (equal (INST-stg i) '(LSU RS0))
		   (not (b1p (LSU-RS-rdy2? (LSU-RS0 (MA-LSU MA)))))
		   (b1p (CDB-ready-for?
			 (LSU-RS-src2 (LSU-RS0 (MA-LSU MA))) MA))
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-p i) (INST-in i MT))
	      (equal (equal (CDB-val MA) (INST-src-val2 i)) T))
  :hints (("goal" :in-theory (e/d (CDB-VAL-INST-DEST-VAL
				   INST-cntlv
				   INST-LSU?
				   equal-b1p-converter
				   decode logbit* rdb lift-b-ops
				   INST-LSU-op?
				   INST-src-val2)
				  (INST-LSU-IF-LSU-STG-P))
		  :use (:instance INST-LSU-IF-LSU-STG-P)))))

(local
(defthm CDB-val-INST-src-val3-if-CDB-ready-for-LSU-RS0
     (implies (and (equal (INST-stg i) '(LSU RS0))
		   (not (b1p (LSU-RS-rdy3? (LSU-RS0 (MA-LSU MA)))))
		   (b1p (CDB-ready-for?
			 (LSU-RS-src3 (LSU-RS0 (MA-LSU MA))) MA))
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-p i) (INST-in i MT))
	      (equal (equal (CDB-val MA) (INST-src-val3 i)) T))
  :hints (("goal" :in-theory (e/d (CDB-VAL-INST-DEST-VAL
				   INST-cntlv
				   INST-LSU?
				   equal-b1p-converter
				   decode logbit* rdb lift-b-ops
				   INST-LSU-op?
				   INST-src-val3)
				  (INST-LSU-IF-LSU-STG-P))
		  :use (:instance INST-LSU-IF-LSU-STG-P)))))

; The instruction invariants are preserved for i that stays in LSU-RS0.
(defthm LSU-RS0-inst-inv-step-INST-from-LSU-RS0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg I) '(LSU RS0))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU RS0)))
	     (LSU-RS0-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops LSU-RS0-inst-inv
				     step-LSU
				     step-LSU-RS0
				     exception-relations))))
)

(encapsulate nil
(local
(defthm CDB-val-INST-src-val1-if-CDB-ready-for-LSU-RS1
     (implies (and (equal (INST-stg i) '(LSU RS1))
		   (not (b1p (LSU-RS-rdy1? (LSU-RS1 (MA-LSU MA)))))
		   (b1p (CDB-ready-for?
			 (LSU-RS-src1 (LSU-RS1 (MA-LSU MA))) MA))
		   (not (b1p (INST-LSU-op? i)))
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-p i) (INST-in i MT))
	      (equal (equal (CDB-val MA) (INST-src-val1 i)) T))
  :hints (("goal" :in-theory (e/d (CDB-VAL-INST-DEST-VAL
				   INST-cntlv
				   INST-LSU?
				   equal-b1p-converter
				   decode logbit* rdb lift-b-ops
				   INST-LSU-op?
				   INST-src-val1)
				  (INST-LSU-IF-LSU-STG-P))
		  :use (:instance INST-LSU-IF-LSU-STG-P)))))

(local
(defthm CDB-val-INST-src-val2-if-CDB-ready-for-LSU-RS1
     (implies (and (equal (INST-stg i) '(LSU RS1))
		   (not (b1p (LSU-RS-rdy2? (LSU-RS1 (MA-LSU MA)))))
		   (b1p (CDB-ready-for?
			 (LSU-RS-src2 (LSU-RS1 (MA-LSU MA))) MA))
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-p i) (INST-in i MT))
	      (equal (equal (CDB-val MA) (INST-src-val2 i)) T))
  :hints (("goal" :in-theory (e/d (CDB-VAL-INST-DEST-VAL
				   INST-cntlv
				   INST-LSU?
				   equal-b1p-converter
				   decode logbit* rdb lift-b-ops
				   INST-LSU-op?
				   INST-src-val2)
				  (INST-LSU-IF-LSU-STG-P))
		  :use (:instance INST-LSU-IF-LSU-STG-P)))))

(local
(defthm CDB-val-INST-src-val3-if-CDB-ready-for-LSU-RS1
     (implies (and (equal (INST-stg i) '(LSU RS1))
		   (not (b1p (LSU-RS-rdy3? (LSU-RS1 (MA-LSU MA)))))
		   (b1p (CDB-ready-for?
			 (LSU-RS-src3 (LSU-RS1 (MA-LSU MA))) MA))
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-p i) (INST-in i MT))
	      (equal (equal (CDB-val MA) (INST-src-val3 i)) T))
  :hints (("goal" :in-theory (e/d (CDB-VAL-INST-DEST-VAL
				   INST-cntlv
				   INST-LSU?
				   equal-b1p-converter
				   decode logbit* rdb lift-b-ops
				   INST-LSU-op?
				   INST-src-val3)
				  (INST-LSU-IF-LSU-STG-P))
		  :use (:instance INST-LSU-IF-LSU-STG-P)))))

; The instruction invariants are preserved for i that stays in LSU-RS1.
(defthm LSU-RS1-inst-inv-step-INST-from-LSU-RS1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg I) '(LSU RS1))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU RS1)))
	     (LSU-RS1-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops inst-inv-def
				     step-LSU
				     step-LSU-RS1
				     exception-relations)
		  :cases ((b1p (LSU-RS-RDY1? (LSU-RS1 (MA-LSU MA))))))))
)

; A landmark lemma. 
; The instruction invariants are preserved for i whose next stage is
; LSU-RS0.
(defthm LSU-RS0-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS)))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU RS0)))
	     (LSU-RS0-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :use (:instance stages-reachable-to-LSU-RS0))))

; A landmark lemma.
; The instruction invariants are preserved for i whose next stage is
; LSU-RS1.
(defthm LSU-RS1-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS)))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU RS1)))
	     (LSU-RS1-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :use (:instance stages-reachable-to-LSU-RS1))))

(deflabel begin-LSU-issue-logic-lemmas)
; Instruction in LSU are issued in program order.  We need extra care
; so that this order is preserved by the LSU issuing hardware. 

; When instruction in RS0 is ready to be issued, operand 1 is ready.
(defthm LSU-RS-rdy1-if-RS0-issue-ready
    (implies (b1p (LSU-RS0-issue-ready? LSU))
	     (b1p (LSU-RS-rdy1? (LSU-RS0 LSU))))
  :hints (("goal" :in-theory (enable lift-b-ops LSU-RS0-issue-ready?
				     equal-b1p-converter))))

; When instruction in RS0 is ready to be issued, operand 2 is ready.
(defthm LSU-RS-rdy2-if-RS0-issue-ready
    (implies (and (not (b1p (LSU-RS-op (LSU-RS0 LSU))))
		  (b1p (LSU-RS0-issue-ready? LSU)))
	     (b1p (LSU-RS-rdy2? (LSU-RS0 LSU))))
  :hints (("goal" :in-theory (enable lift-b-ops LSU-RS0-issue-ready?
				     equal-b1p-converter))))

; When instruction in RS0 is ready to be issued, operand 3 is ready.
(defthm LSU-RS-rdy3-if-RS0-issue-ready
    (implies (and (b1p (LSU-RS-ld-st? (LSU-RS0 LSU)))
		  (b1p (LSU-RS0-issue-ready? LSU)))
	     (b1p (LSU-RS-rdy3? (LSU-RS0 LSU))))
  :hints (("goal" :in-theory (enable lift-b-ops LSU-RS0-issue-ready?
				     equal-b1p-converter))))

; When instruction in RS1 is ready to be issued, operand 1 is ready.
(defthm LSU-RS-rdy1-if-RS1-issue-ready
    (implies (b1p (LSU-RS1-issue-ready? LSU))
	     (b1p (LSU-RS-rdy1? (LSU-RS1 LSU))))
  :hints (("goal" :in-theory (enable lift-b-ops LSU-RS1-issue-ready?
				     equal-b1p-converter))))  

; When instruction in RS1 is ready to be issued, operand 2 is ready.
(defthm LSU-RS-rdy2-if-RS1-issue-ready
    (implies (and (not (b1p (LSU-RS-op (LSU-RS1 LSU))))
		  (b1p (LSU-RS1-issue-ready? LSU)))
	     (b1p (LSU-RS-rdy2? (LSU-RS1 LSU))))
  :hints (("goal" :in-theory (enable lift-b-ops LSU-RS1-issue-ready?
				     equal-b1p-converter))))  

; When instruction in RS1 is ready to be issued, operand 3 is ready.
(defthm LSU-RS-rdy3-if-RS1-issue-ready
    (implies (and (b1p (LSU-RS-ld-st? (LSU-RS1 LSU)))
		  (b1p (LSU-RS1-issue-ready? LSU)))
	     (b1p (LSU-RS-rdy3? (LSU-RS1 LSU))))
  :hints (("goal" :in-theory (enable lift-b-ops LSU-RS1-issue-ready?
				     equal-b1p-converter))))  

; Instructions in RS0 and RS1 cannot be ready to be issued simultaneously.
(defthm LSU-RS0-ISSUE-READY-LSU-RS1-ISSUE-READY-exclusive
    (implies (b1p (LSU-RS0-issue-ready? (MA-LSU MA)))
	     (not (b1p (LSU-RS1-issue-ready? (MA-LSU MA)))))
  :hints (("goal" :in-theory (enable LSU-RS0-issue-ready? LSU-RS1-issue-ready?
				     lift-b-ops))))

(deflabel end-LSU-issue-logic-lemmas)
(deftheory LSU-issue-logic-lemmas
    (set-difference-theories (universal-theory 'end-LSU-issue-logic-lemmas)
			     (universal-theory 'begin-LSU-issue-logic-lemmas)))
(in-theory (disable LSU-issue-logic-lemmas)) 
  
; The instruction invariants are preserved for instruction i that moves
; from LSU-RS0 to LSU-wbuf1.
(defthm LSU-wbuf1-inst-inv-step-INST-from-RS0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg I) '(LSU RS0))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU wbuf1)))
	     (LSU-WBUF1-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops inst-inv-def
				     step-LSU
				     step-wbuf1
				     LSU-issue-logic-lemmas
				     issue-logic-def
				     issued-write
				     update-wbuf1
				     INST-SRC-VAL1 INST-STORE-ADDR
				     INST-SRC-VAL2 INST-SRC-VAL3
				     INST-LSU-OP? INST-LD-ST?
				     INST-SELECT-WBUF0?
				     INST-store?
				     decode rdb logbit*
				     INST-cntlv
				     exception-relations))))

; The instruction invariants are preserved for instruction i that moves
; from LSU-RS1 to LSU-wbuf1.
(defthm LSU-wbuf1-inst-inv-step-INST-from-RS1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg I) '(LSU RS1))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU wbuf1)))
	     (LSU-WBUF1-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops inst-inv-def
				     step-LSU
				     step-wbuf1
				     LSU-issue-logic-lemmas
				     issue-logic-def
				     issued-write
				     update-wbuf1
				     INST-SRC-VAL1 INST-STORE-ADDR
				     INST-SRC-VAL2 INST-SRC-VAL3
				     INST-SELECT-WBUF0?
				     INST-LSU-OP? INST-LD-ST?
				     INST-store?
				     decode rdb logbit*
				     INST-cntlv
				     exception-relations))))

; The instruction invariants are preserved for instruction i that stays
; in wbuf1.
(defthm LSU-wbuf1-inst-inv-step-INST-from-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg I) '(LSU wbuf1))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU wbuf1)))
	     (LSU-WBUF1-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops inst-inv-def
				     step-LSU step-wbuf1 issue-logic-def
				     LSU-store-if-at-LSU-wbuf
				     RELEASE-WBUF0?
				     UPDATE-WBUF1
				     exception-relations))))

; A landmark lemma. 
; The instruction invariants are preserved for instruction i whose
; next stage is LSU-wbuf1.
(defthm LSU-wbuf1-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU wbuf1)))
	     (LSU-WBUF1-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :use (:instance stages-reachable-to-LSU-wbuf1))))

; The instruction invariants are preserved for instruction i that moves
; from RS0 to wbuf0.
(defthm LSU-wbuf0-inst-inv-step-INST-from-RS0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg I) '(LSU RS0))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU wbuf0)))
	     (LSU-WBUF0-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops inst-inv-def
				     step-LSU step-wbuf0
				     LSU-issue-logic-lemmas
				     issue-logic-def
				     issued-write update-wbuf0
				     wbuf1-output
				     INST-SRC-VAL1 INST-STORE-ADDR
				     INST-SRC-VAL2 INST-SRC-VAL3
				     INST-SELECT-WBUF0?
				     INST-LSU-OP? INST-LD-ST?
				     INST-store?
				     decode rdb logbit*
				     INST-cntlv
				     exception-relations))))

; The instruction invariants are preserved for instruction i that moves
; from RS1 to wbuf0.
(defthm LSU-wbuf0-inst-inv-step-INST-from-RS1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg I) '(LSU RS1))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU wbuf0)))
	     (LSU-WBUF0-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
    :hints (("goal" :in-theory (enable lift-b-ops inst-inv-def
				     step-LSU step-wbuf0
				     LSU-issue-logic-lemmas
				     issue-logic-def
				     issued-write update-wbuf0
				     wbuf1-output
				     INST-SRC-VAL1 INST-STORE-ADDR
				     INST-SRC-VAL2 INST-SRC-VAL3
				     INST-SELECT-WBUF0?
				     INST-LSU-OP? INST-LD-ST?
				     INST-store?
				     decode rdb logbit*
				     INST-cntlv
				     exception-relations))))
(encapsulate nil
(local
 (defthm not-INST-excpt-detected-p-if-moved-from-wbuf1-to-wbuf0
     (implies (and (inv MT MA)
		   (equal (INST-stg i) '(LSU wbuf1))
		   (equal (INST-stg (step-INST i MT MA sigs))
			  '(LSU wbuf0))
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-in i MT) (INST-p i)
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i))))
	      (not (INST-excpt-detected-p (step-INST i MT MA sigs))))
   :hints (("goal" :in-theory (enable INST-excpt-detected-p
				      INST-data-accs-error-detected-p
				      INST-load-accs-error-detected-p
				      INST-store-accs-error-detected-p
				      exception-relations)))))

; The instruction invariants are preserved for instruction i that moves
; from wbuf1 to wbuf0.
(defthm LSU-wbuf0-inst-inv-step-INST-from-RS1-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg I) '(LSU wbuf1))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU wbuf0)))
	     (LSU-WBUF0-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops inst-inv-def
				     step-LSU step-wbuf0 issue-logic-def
				     LSU-store-if-at-LSU-wbuf
				     RELEASE-WBUF0? wbuf1-output
				     RELEASE-WBUF0-READY?
				     issued-write UPDATE-WBUF0
				     exception-relations))))
)

; The instruction invariants are preserved for instruction i that stays
; in wbuf0
(defthm LSU-wbuf0-inst-inv-step-INST-from-RS1-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg I) '(LSU wbuf0))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU wbuf0)))
	     (LSU-WBUF0-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops inst-inv-def
				     step-LSU step-wbuf0 issue-logic-def
				     LSU-store-if-at-LSU-wbuf
				     RELEASE-WBUF0? wbuf1-output
				     RELEASE-WBUF0-READY?
				     issued-write UPDATE-WBUF0
				     exception-relations))))

; A landmark lemma. 
; The instruction invariants are preserved for instruction i whose next 
; stage is wbuf0.
(defthm LSU-wbuf0-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU wbuf0)))
	     (LSU-WBUF0-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :use (:instance stages-reachable-to-LSU-wbuf0))))

(local
(defthm opcode-for-LSU-RS
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (or (EQUAL (INST-STG I) '(LSU RS0))
		      (EQUAL (INST-STG I) '(LSU RS1))))
	     (or (equal (INST-opcode i) 3) (equal (INST-opcode i) 4)
		 (equal (INST-opcode i) 6) (equal (INST-opcode i) 7)))
  :hints (("goal" :in-theory (e/d (INST-LSU? INST-cntlv lift-b-ops
					     equal-b1p-converter
					     decode rdb logbit*)
				  (INST-LSU-IF-LSU-STG-P))
		  :use (:instance INST-LSU-IF-LSU-STG-P)))
   :rule-classes nil))

(local
(defthm opcode-for-LSU-wbuf
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (or (EQUAL (INST-STG I) '(LSU wbuf0))
		      (EQUAL (INST-STG I) '(LSU wbuf1))
		      (EQUAL (INST-STG I) '(LSU wbuf0 lch))
		      (EQUAL (INST-STG I) '(LSU wbuf1 lch))))
	     (or (equal (INST-opcode i) 4) (equal (INST-opcode i) 7)))
  :hints (("goal" :in-theory (e/d (INST-LSU? INST-cntlv lift-b-ops
					     equal-b1p-converter
					     INST-store? INST-ld-st?
					     decode rdb logbit*)
				  ())
		  :use (:instance LSU-store-if-at-LSU-wbuf)))
   :rule-classes nil))

(local
(defthm opcode-for-LSU-rbuf-lch
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (or (EQUAL (INST-STG I) '(LSU rbuf))
		      (EQUAL (INST-STG I) '(LSU lch))))
	     (or (equal (INST-opcode i) 3) (equal (INST-opcode i) 6)))
  :hints (("goal" :in-theory (e/d (INST-LSU? INST-cntlv lift-b-ops
					     equal-b1p-converter
					     INST-load? INST-ld-st?
					     decode rdb logbit*)
				  ())
		  :use (:instance LSU-load-if-at-LSU-rbuf-lch)))
   :rule-classes nil))

; The instruction invariants are preserved for instruction i that moves
; from RS0 to rbuf.
(defthm LSU-rbuf-inst-inv-step-INST-from-LSU-RS0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (INST-in i MT)
		  (MA-input-p sigs)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg i) '(LSU RS0))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU rbuf)))
	     (LSU-rbuf-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (e/d (LSU-rbuf-inst-inv
				   issue-logic-def LSU-issue-logic-lemmas
				   step-LSU step-rbuf
				   INST-load-addr INST-src-val1
				   INST-src-val2 INST-src-val3
				   INST-LSU-OP?  INST-LD-ST?
				   decode rdb logbit* INST-cntlv
				   INST-load?
				   lift-b-ops)
				  ())
		  :use (:instance opcode-for-LSU-RS))))

; The instruction invariants are preserved for instruction i that moves
; from RS1 to rbuf.
(defthm LSU-rbuf-inst-inv-step-INST-from-LSU-RS1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (INST-in i MT)
		  (MA-input-p sigs)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg i) '(LSU RS1))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU rbuf)))
	     (LSU-rbuf-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable LSU-rbuf-inst-inv
				     issue-logic-def LSU-issue-logic-lemmas
				     step-LSU step-rbuf
				     INST-load-addr INST-src-val1
				     INST-src-val2 INST-src-val3
				     INST-LSU-OP?  INST-LD-ST?
				     decode rdb logbit* INST-cntlv
				     INST-load?
				     lift-b-ops )
		  :use (:instance opcode-for-LSU-RS))))

; The instruction invariants are preserved for instruction i that stays
; in rbuf.
(defthm LSU-rbuf-inst-inv-step-INST-from-LSU-rbuf
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (INST-in i MT)
		  (MA-input-p sigs)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg i) '(LSU rbuf))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU rbuf)))
	     (LSU-rbuf-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable lift-b-ops inst-inv-def
				     step-LSU step-rbuf issue-logic-def
				     LSU-load-if-at-LSU-rbuf-lch
				     exception-relations))))

; A landmark lemma. 
; The instruction invariants are preserved for instruction i whose next stage
; is rbuf.
(defthm LSU-rbuf-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (INST-in i MT)
		  (MA-input-p sigs)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU rbuf)))
	     (LSU-rbuf-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :use (:instance stages-reachable-to-LSU-rbuf))))

; The write operation at wbuf0 is not ready to be released until it commits.
(defthm not-release-wbuf0-if-LSU-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (or (equal (INST-stg i) '(LSU wbuf0))
		      (equal (INST-stg i) '(LSU wbuf0 lch))
		      (equal (INST-stg i) '(complete wbuf0))))
	     (equal (release-wbuf0? (MA-LSU MA) sigs) 0))
  :hints (("goal" :in-theory (enable release-wbuf0? lift-b-ops
				     equal-b1p-converter
				     release-wbuf0-ready?))))

; If there is an unchecked write operation in wbuf0, a load instruction is
; not released. 
(defthm not-release-rbuf-if-LSU-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(LSU wbuf0)))
	     (equal (release-rbuf? (MA-LSU MA) MA sigs) 0))
  :hints (("goal" :in-theory (enable lift-b-ops CHECK-WBUF0?
				     equal-b1p-converter
				     release-rbuf?))))

; If there is an unchecked write operation in wbuf1, a load instruction is
; not released. 
(defthm not-release-rbuf-if-LSU-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(LSU wbuf1)))
	     (equal (release-rbuf? (MA-LSU MA) MA sigs) 0))
  :hints (("goal" :in-theory (enable lift-b-ops CHECK-WBUF1?
				     equal-b1p-converter
				     release-rbuf?))))

; The exception flags are set depending on whether the protection of the
; store memory address is violated or not.
(defthm INST-excpt-flags-step-inst-if-LSU-write-prohibited-at-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(LSU wbuf0))
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU wbuf0 lch))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (equal (INST-excpt-flags (step-INST i MT MA sigs))
		    (if (b1p (LSU-write-prohibited? (MA-LSU MA) (MA-mem MA)
						    (SRF-su (MA-SRF MA))))
			6 0)))
  :hints (("goal" :in-theory (enable INST-excpt-flags
				     INST-DATA-ACCS-ERROR-DETECTED-P
				     INST-load-accs-error-detected-p
				     INST-store-accs-error-detected-p
				     LSU-WRITE-PROHIBITED?
				     lift-b-ops
				     write-error?)
		  :use (:instance opcode-for-LSU-wbuf))))

; Similar to INST-excpt-flags-step-inst-if-LSU-write-prohibited-at-wbuf0.
(defthm INST-excpt-flags-step-inst-if-LSU-write-prohibited-at-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(LSU wbuf1))
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU wbuf1 lch))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (equal (INST-excpt-flags (step-INST i MT MA sigs))
		    (if (b1p (LSU-write-prohibited? (MA-LSU MA) (MA-mem MA)
						    (SRF-su (MA-SRF MA))))
			6 0)))
  :hints (("goal" :in-theory (enable INST-excpt-flags
				     INST-DATA-ACCS-ERROR-DETECTED-P
				     INST-load-accs-error-detected-p
				     INST-store-accs-error-detected-p
				     LSU-WRITE-PROHIBITED?
				     check-wbuf0? check-wbuf1?
				     lift-b-ops
				     write-error?)
		  :use (:instance opcode-for-LSU-wbuf))))

; A landmark lemma. 
; The instruction invariants are preserved for the instruction
; whose next address is LSU-wbuf-lch
(defthm LSU-wbuf0-lch-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU wbuf0 lch)))
	     (LSU-wbuf0-lch-inst-inv (step-INST i MT MA sigs)
				     (MA-step MA sigs)))
  :hints (("goal" :use (:instance stages-reachable-to-LSU-wbuf0-lch)
		  :in-theory (enable LSU-wbuf0-lch-inst-inv
				     lift-b-ops
				     wbuf1-output step-wbuf0 update-wbuf0
				     LSU-store-if-at-LSU-wbuf
				     CHECK-WBUF0? issued-write
				     step-LSU step-lsu-lch))))

; A landmark lemma. 
; The instruction invariants are preserved for the instruction
; whose next stage is LSU-wbuf1-lch.
(defthm LSU-wbuf1-lch-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU wbuf1 lch)))
	     (LSU-wbuf1-lch-inst-inv (step-INST i MT MA sigs)
				     (MA-step MA sigs)))
  :hints (("goal" :use (:instance stages-reachable-to-LSU-wbuf1-lch)
		  :in-theory (enable LSU-wbuf1-lch-inst-inv
				     lift-b-ops
				     wbuf1-output step-wbuf1 update-wbuf1
				     LSU-store-if-at-LSU-wbuf
				     CHECK-WBUF1? issued-write
				     RELEASE-WBUF0?
				     step-LSU step-lsu-lch))))

; From here, we prove lemma LSU-lch-inst-inv-step-INST.
; There are two major lemmas to prove.
; The first lemma to prove is 
;   LSU-forward-wbuf-INST-dest-val
; This proves that load-forwarding is working fine. 
; The second lemma 
;   read-mem-INST-load-addr-INST-dest-val
; proves that memory access (possibly using load-bypassing) is working fine. 

; If load instruction i violates the protection of the memory,
; the exception flags are set appropriately.
(defthm INST-excpt-flags-step-inst-if-LSU-read-prohibited-at-rbuf
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(LSU rbuf))
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU lch))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (equal (INST-excpt-flags (step-INST i MT MA sigs))
		    (if (b1p (LSU-read-prohibited? (MA-LSU MA) (MA-mem MA)
						    (SRF-su (MA-SRF MA))))
			6 0)))
  :hints (("goal" :in-theory (enable INST-excpt-flags
				     INST-DATA-ACCS-ERROR-DETECTED-P
				     INST-load-accs-error-detected-p
				     INST-store-accs-error-detected-p
				     LSU-read-PROHIBITED?
				     check-wbuf0? check-wbuf1?
				     lift-b-ops
				     read-error?)
		  :use (:instance opcode-for-LSU-rbuf-lch))))

; INST-load-accs-error is detected when the released load instruction
; violates the memory access. 
(defthm inst-load-accs-error-detected-p-if-lsu-read-prohibited
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(LSU rbuf))
		  (b1p (release-rbuf? (MA-LSU MA) MA sigs))
		  (b1p (LSU-read-prohibited? (MA-LSU MA) (MA-mem MA)
					     (SRF-su (MA-SRF MA))))
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (INST-load-accs-error-detected-p (step-INST i MT MA sigs)))
  :hints (("goal" :in-theory (enable LSU-read-prohibited? lift-b-ops
				     read-error?
				     INST-load-accs-error-detected-p)
		  :use (:instance opcode-for-LSU-rbuf-lch))))

; From here, we start discussing the memory modifiers. 
; The first goal is proving LSU-forward-wbuf-INST-dest-val.
; This lemma suggests that the load forwarding is working correctly.
(encapsulate nil
(local
(defthm not-no-inst-at-wbuf0-if-LSU-wbuf-valid-help-help
    (implies (uniq-INST-at-stgs-in-trace '((LSU WBUF0)
					   (LSU WBUF0 LCH)
					   (COMPLETE WBUF0)
					   (COMMIT WBUF0)) trace)
	     (not (no-inst-at-wbuf0-p trace)))))

(local
(defthm not-no-inst-at-wbuf0-if-LSU-wbuf-valid-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-INST-at-stgs '((LSU WBUF0)
				       (LSU WBUF0 LCH)
				       (COMPLETE WBUF0)
				       (COMMIT WBUF0)) MT))
	     (not (no-inst-at-wbuf0-p (MT-trace MT))))
  :hints (("goal" :in-theory (enable uniq-INST-at-stgs)))))

; A help lemma. The wbuf0 is valid, then no-inst-at-wbuf0-p is nil.
(defthm not-no-inst-at-wbuf0-if-LSU-wbuf-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
	     (not (no-inst-at-wbuf0-p (MT-trace MT)))))
)

(encapsulate nil
(local
(defthm not-no-inst-at-wbuf1-if-LSU-wbuf-valid-help-help
    (implies (uniq-INST-at-stgs-in-trace '((LSU WBUF1)
					   (LSU WBUF1 LCH)
					   (COMPLETE WBUF1)
					   (COMMIT WBUF1)) trace)
	     (not (no-inst-at-wbuf1-p trace)))))

(local
(defthm not-no-inst-at-wbuf1-if-LSU-wbuf-valid-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-INST-at-stgs '((LSU WBUF1)
				       (LSU WBUF1 LCH)
				       (COMPLETE WBUF1)
				       (COMMIT WBUF1)) MT))
	     (not (no-inst-at-wbuf1-p (MT-trace MT))))
  :hints (("goal" :in-theory (enable uniq-INST-at-stgs)))))

; A help lemma. The wbuf1 is valid, then no-inst-at-wbuf1-p is nil.
(defthm not-no-inst-at-wbuf1-if-LSU-wbuf-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
	     (not (no-inst-at-wbuf1-p (MT-trace MT)))))
)

(encapsulate nil
(local
(defthm exist-LMM-before-p-if-rbuf-wbuf0-help
     (implies (and (inv MT MA)
		   (subtrace-p trace MT)
		   (INST-listp trace)
		   (member-equal i trace) (INST-p i)
		   (MAETT-p MT) (MA-state-p MA)
		   (equal (INST-stg i) '(LSU rbuf))
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (in-order-wbuf0-rbuf-p trace)
		   (equal (wbuf-addr (LSU-wbuf0 (MA-LSU MA))) addr)
		   (not (no-inst-at-wbuf0-p trace)))
	      (trace-exist-LMM-before-p i addr trace))
  :hints (("goal" :restrict ((LSU-WBUF0-ADDR-=-INST-STORE-ADDR
			      ((i (car trace)))))
		  :in-theory (enable wbuf0-stg-p)))))

; Suppose rbuf-wbuf0? flag is on, and the store instruction at wbuf0
; precedes the load instruction.  In that case, there is a memory
; modifier before the load instruction.
(defthm exist-LMM-before-p-if-rbuf-wbuf0
     (implies (and (inv MT MA)
		   (INST-in i MT) (INST-p i)
		   (MAETT-p MT) (MA-state-p MA)
		   (equal (INST-stg i) '(LSU rbuf))
		   (b1p (rbuf-wbuf0? (LSU-rbuf (MA-LSU MA))))
		   (equal (wbuf-addr (LSU-wbuf0 (MA-LSU MA))) addr)
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i))))
	      (exist-LMM-before-p i addr MT))
  :hints (("goal" :in-theory (enable exist-LMM-before-p
				     INST-in)
		  :restrict ((LSU-RBUF-VALID-IF-INST-IN ((i i)))))))
)

(encapsulate nil
(local
(defthm exist-LMM-before-p-if-rbuf-wbuf1-help
     (implies (and (inv MT MA)
		   (subtrace-p trace MT)
		   (INST-listp trace)
		   (member-equal i trace) (INST-p i)
		   (MAETT-p MT) (MA-state-p MA)
		   (equal (INST-stg i) '(LSU rbuf))
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (in-order-wbuf1-rbuf-p trace)
		   (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) addr)
		   (not (no-inst-at-wbuf1-p trace)))
	      (trace-exist-LMM-before-p i addr trace))
  :hints (("goal" :restrict ((LSU-WBUF1-ADDR-=-INST-STORE-ADDR
			      ((i (car trace)))))
		  :in-theory (enable wbuf1-stg-p)))))

; Suppose rbuf-wbuf1? flag is 1, and the store instruction in wbuf1
; precedes the load instruction.  In that case, there is a memory
; modifier before the load instruction.
(defthm exist-LMM-before-p-if-rbuf-wbuf1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA))))
		  (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) addr)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (exist-LMM-before-p i addr MT))
  :hints (("goal" :in-theory (enable exist-LMM-before-p
				     INST-in)
		  :restrict ((LSU-RBUF-VALID-IF-INST-IN ((i i)))))))
)  

(encapsulate nil
(local
(defthm not-LSU-wbuf1-LMM-1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (exist-LMM-before-p i addr MT)
		  (not (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA))))))
	     (not (equal (INST-stg (LMM-before i addr MT))
			 '(LSU wbuf1))))
  :hints (("goal" :use (:instance INST-in-order-p-rbuf-wbuf1
				  (j (LMM-before i addr MT)))))))

(local
(defthm not-LSU-wbuf1-LMM-2
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (exist-LMM-before-p i addr MT)
		  (not (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) addr))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (not (equal (INST-stg (LMM-before i addr MT))
			 '(LSU wbuf1))))
  :hints (("goal" :restrict ((LSU-WBUF1-ADDR-=-INST-STORE-ADDR 
			      ((i (LMM-before i addr MT)))))))))

(local
(defthm not-LSU-wbuf1-lch-LMM-1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (exist-LMM-before-p i addr MT)
		  (not (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA))))))
	     (not (equal (INST-stg (LMM-before i addr MT))
			 '(LSU wbuf1 lch))))
  :hints (("goal" :use (:instance INST-in-order-p-rbuf-wbuf1
				  (j (LMM-before i addr MT)))))))

(local
(defthm not-LSU-wbuf1-lch-LMM-2
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (exist-LMM-before-p i addr MT)
		  (not (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) addr))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (not (equal (INST-stg (LMM-before i addr MT))
			 '(LSU wbuf1 lch))))
  :hints (("goal" :restrict ((LSU-WBUF1-ADDR-=-INST-STORE-ADDR 
			      ((i (LMM-before i addr MT)))))))))

(local
(defthm wbuf0-stg-p-LMM-before-if-execute-stg
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (b1p (rbuf-wbuf0? (LSU-rbuf (MA-LSU MA))))
		  (equal (wbuf-addr (LSU-wbuf0 (MA-LSU MA))) addr)
		  (or (not (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA)))))
		      (not (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) addr)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (execute-stg-p
		   (INST-stg (LMM-before i addr MT))))
	     (wbuf0-stg-p
	      (INST-stg
	       (LMM-before i addr MT))))
  :hints (("goal" :in-theory (enable execute-stg-p LSU-stg-p)))))

(local
(defthm not-complete-wbuf1-LMM-1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (exist-LMM-before-p i addr MT)
		  (not (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA))))))
	     (not (equal (INST-stg (LMM-before i addr MT))
			 '(complete wbuf1))))
  :hints (("goal" :use (:instance INST-in-order-p-rbuf-wbuf1
				  (j (LMM-before i addr MT)))))))

(local
(defthm not-complete-wbuf1-LMM-2
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (exist-LMM-before-p i addr MT)
		  (not (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) addr))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (not (equal (INST-stg (LMM-before i addr MT))
			 '(complete wbuf1))))
  :hints (("goal" :restrict ((LSU-WBUF1-ADDR-=-INST-STORE-ADDR 
			      ((i (LMM-before i addr MT)))))))))

(local
(defthm wbuf0-stg-p-LMM-before-if-complete
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (b1p (rbuf-wbuf0? (LSU-rbuf (MA-LSU MA))))
		  (equal (wbuf-addr (LSU-wbuf0 (MA-LSU MA))) addr)
		  (or (not (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA)))))
		      (not (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) addr)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (complete-stg-p
		   (INST-stg (LMM-before i addr MT))))
	     (wbuf0-stg-p
	      (INST-stg
	       (LMM-before i addr MT))))
    :hints (("goal" :in-theory (enable complete-stg-p)))))

(local
(defthm not-commit-wbuf1-LMM-1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (exist-LMM-before-p i addr MT)
		  (not (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA))))))
	     (not (equal (INST-stg (LMM-before i addr MT))
			 '(commit wbuf1))))
  :hints (("goal" :use (:instance INST-in-order-p-rbuf-wbuf1
				  (j (LMM-before i addr MT)))))))

(local
(defthm not-commit-wbuf1-LMM-2
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (exist-LMM-before-p i addr MT)
		  (not (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) addr))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (not (equal (INST-stg (LMM-before i addr MT))
			 '(commit wbuf1))))
  :hints (("goal" :restrict ((LSU-WBUF1-ADDR-=-INST-STORE-ADDR 
			      ((i (LMM-before i addr MT)))))))))

(local
(defthm wbuf0-stg-p-LMM-before-if-commit
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (b1p (rbuf-wbuf0? (LSU-rbuf (MA-LSU MA))))
		  (equal (wbuf-addr (LSU-wbuf0 (MA-LSU MA))) addr)
		  (or (not (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA)))))
		      (not (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) addr)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (commit-stg-p
		   (INST-stg (LMM-before i addr MT))))
	     (wbuf0-stg-p
	      (INST-stg
	       (LMM-before i addr MT))))
  :hints (("goal" :in-theory (enable commit-stg-p)))))

(local
(defthm not-retire-stg-p-LMM-before-help
    (implies (and (wbuf-stg-p (INST-stg (inst-at-stgs stgs MT)))
		  (retire-stg-p (INST-stg (LMM-before i addr MT))))
	     (not (equal (LMM-before i addr MT)
			 (inst-at-stgs stgs MT))))
  :hints (("goal" :in-theory (enable wbuf-stg-p retire-stg-p)))))

(local
(defthm not-retire-stg-p-LMM-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (b1p (rbuf-wbuf0? (LSU-rbuf (MA-LSU MA))))
		  (equal (wbuf-addr (LSU-wbuf0 (MA-LSU MA))) addr)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (not (retire-stg-p
		   (INST-stg (LMM-before i addr MT)))))
  :hints (("goal" :use ((:instance INST-in-order-p-retire-wbuf0
				  (i (LMM-before i addr MT))
				  (j (INST-at-stgs '((LSU wbuf0)
						     (LSU wbuf0 lch)
						     (complete wbuf0)
						     (commit wbuf0)) MT)))
			(:instance INST-in-order-p-wbuf0-rbuf
				   (j i)
				   (i (INST-at-stgs '((LSU wbuf0)
						     (LSU wbuf0 lch)
						     (complete wbuf0)
						     (commit wbuf0)) MT)))
			(:instance INST-IN-ORDER-P-INST-SPECULTV
				   (i (INST-at-stgs '((LSU wbuf0)
						     (LSU wbuf0 lch)
						     (complete wbuf0)
						     (commit wbuf0)) MT))
				   (j i))
			(:instance INST-IN-ORDER-P-INST-MODIFIED
				   (i (INST-at-stgs '((LSU wbuf0)
						     (LSU wbuf0 lch)
						     (complete wbuf0)
						     (commit wbuf0)) MT))
				   (j i)))
		  :in-theory (e/d (LSU-wbuf-field-inst-at-lemmas)
				  (INST-IN-ORDER-P-INST-SPECULTV
				   INST-IN-ORDER-P-INST-MODIFIED))))))

; If rbuf-wbuf0? is 1, (i.e., the store instruction at wbuf0 precedes
; the load instruction), the store address and the load address match,
; and wbuf1 does not contain the memory modifier, then the last memory
; modifier before i is at a wbuf0 stage.  There are two conditions
; that the store instruction at wbuf1 is not a memory modifier.  The
; rbuf-wbuf1? is 0, or the load and store addresses don't match.
(defthm wbuf0-stg-p-LMM-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (b1p (rbuf-wbuf0? (LSU-rbuf (MA-LSU MA))))
		  (equal (wbuf-addr (LSU-wbuf0 (MA-LSU MA))) addr)
		  (or (not (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA)))))
		      (not (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) addr)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (wbuf0-stg-p
	      (INST-stg
	       (LMM-before i addr MT))))
  :hints (("goal" :in-theory (e/d ()
				  (INST-IN-ORDER-LMM-BEFORE
				   INST-is-at-one-of-the-stages))
		  :use ((:instance INST-is-at-one-of-the-stages
			   (i (LMM-before i addr MT)))))))
)

(encapsulate  nil
(local
(defthm not-LSU-wbuf0-LMM-before-help
    (implies (and (wbuf1-stg-p (INST-stg (inst-at-stgs stgs MT)))
		  (wbuf0-stg-p (INST-stg
				(LMM-before i addr MT))))
	     (not (equal (LMM-before i addr MT)
			 (inst-at-stgs stgs MT))))
  :hints (("goal" :in-theory (enable wbuf1-stg-p wbuf0-stg-p)))))

(local
(defthm not-LSU-wbuf0-LMM-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA))))
		  (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) addr)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (not (equal (INST-stg (LMM-before i addr MT))
			 '(LSU wbuf0))))
  :hints (("goal" :use ((:instance INST-in-order-p-wbuf0-wbuf1
				   (i (LMM-before i addr MT))
				   (j (INST-at-stgs '((LSU wbuf1)
						      (LSU wbuf1 lch)
						      (complete wbuf1)
						      (commit wbuf1)) MT)))
			(:instance INST-in-order-p-wbuf1-rbuf
				   (j i)
				   (i (INST-at-stgs '((LSU wbuf1)
						      (LSU wbuf1 lch)
						      (complete wbuf1)
						      (commit wbuf1)) MT)))
			(:instance INST-IN-ORDER-P-INST-SPECULTV
				   (i (INST-at-stgs '((LSU wbuf1)
						     (LSU wbuf1 lch)
						     (complete wbuf1)
						     (commit wbuf1)) MT))
				   (j i))
			(:instance INST-IN-ORDER-P-INST-MODIFIED
				   (i (INST-at-stgs '((LSU wbuf1)
						     (LSU wbuf1 lch)
						     (complete wbuf1)
						     (commit wbuf1)) MT))
				   (j i)))
		  :in-theory (disable INST-IN-ORDER-P-INST-MODIFIED
				      INST-IN-ORDER-P-INST-SPECULTV)))))

(local
(defthm not-LSU-wbuf0-lch-LMM-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA))))
		  (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) addr)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (not (equal (INST-stg (LMM-before i addr MT))
			 '(LSU wbuf0 lch))))
    :hints (("goal" :use ((:instance INST-in-order-p-wbuf0-wbuf1
				   (i (LMM-before i addr MT))
				   (j (INST-at-stgs '((LSU wbuf1)
						      (LSU wbuf1 lch)
						      (complete wbuf1)
						      (commit wbuf1)) MT)))
			(:instance INST-in-order-p-wbuf1-rbuf
				   (j i)
				   (i (INST-at-stgs '((LSU wbuf1)
						      (LSU wbuf1 lch)
						      (complete wbuf1)
						      (commit wbuf1)) MT)))
			(:instance INST-IN-ORDER-P-INST-SPECULTV
				   (i (INST-at-stgs '((LSU wbuf1)
						     (LSU wbuf1 lch)
						     (complete wbuf1)
						     (commit wbuf1)) MT))
				   (j i))
			(:instance INST-IN-ORDER-P-INST-MODIFIED
				   (i (INST-at-stgs '((LSU wbuf1)
						     (LSU wbuf1 lch)
						     (complete wbuf1)
						     (commit wbuf1)) MT))
				   (j i)))
		  :in-theory (disable INST-IN-ORDER-P-INST-MODIFIED
				      INST-IN-ORDER-P-INST-SPECULTV)))))

(local
(defthm wbuf1-stg-p-LMM-before-if-execute-stg
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA))))
		  (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) addr)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (execute-stg-p
		   (INST-stg (LMM-before i addr MT))))
	      (wbuf1-stg-p (INST-stg (LMM-before i addr MT))))
    :hints (("goal" :in-theory (enable execute-stg-p LSU-stg-p)))))

(local
(defthm not-complete-wbuf0-LMM-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA))))
		  (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) addr)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (not (equal (INST-stg (LMM-before i addr MT))
			 '(complete wbuf0))))
    :hints (("goal" :use ((:instance INST-in-order-p-wbuf0-wbuf1
				   (i (LMM-before i addr MT))
				   (j (INST-at-stgs '((LSU wbuf1)
						      (LSU wbuf1 lch)
						      (complete wbuf1)
						      (commit wbuf1)) MT)))
			(:instance INST-in-order-p-wbuf1-rbuf
				   (j i)
				   (i (INST-at-stgs '((LSU wbuf1)
						      (LSU wbuf1 lch)
						      (complete wbuf1)
						      (commit wbuf1)) MT)))
			(:instance INST-IN-ORDER-P-INST-SPECULTV
				   (i (INST-at-stgs '((LSU wbuf1)
						     (LSU wbuf1 lch)
						     (complete wbuf1)
						     (commit wbuf1)) MT))
				   (j i))
			(:instance INST-IN-ORDER-P-INST-MODIFIED
				   (i (INST-at-stgs '((LSU wbuf1)
						     (LSU wbuf1 lch)
						     (complete wbuf1)
						     (commit wbuf1)) MT))
				   (j i)))
		  :in-theory (disable INST-IN-ORDER-P-INST-MODIFIED
				      INST-IN-ORDER-P-INST-SPECULTV)))))

(local
(defthm wbuf1-stg-p-LMM-before-if-complete-stg
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA))))
		  (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) addr)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (complete-stg-p
		   (INST-stg (LMM-before i addr MT))))
	      (wbuf1-stg-p (INST-stg (LMM-before i addr MT))))
  :hints (("goal" :in-theory (enable complete-stg-p)))))

(local
(defthm not-commit-wbuf0-LMM-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA))))
		  (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) addr)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (not (equal (INST-stg (LMM-before i addr MT))
			 '(commit wbuf0))))
    :hints (("goal" :use ((:instance INST-in-order-p-wbuf0-wbuf1
				   (i (LMM-before i addr MT))
				   (j (INST-at-stgs '((LSU wbuf1)
						      (LSU wbuf1 lch)
						      (complete wbuf1)
						      (commit wbuf1)) MT)))
			(:instance INST-in-order-p-wbuf1-rbuf
				   (j i)
				   (i (INST-at-stgs '((LSU wbuf1)
						      (LSU wbuf1 lch)
						      (complete wbuf1)
						      (commit wbuf1)) MT)))
			(:instance INST-IN-ORDER-P-INST-SPECULTV
				   (i (INST-at-stgs '((LSU wbuf1)
						     (LSU wbuf1 lch)
						     (complete wbuf1)
						     (commit wbuf1)) MT))
				   (j i))
			(:instance INST-IN-ORDER-P-INST-MODIFIED
				   (i (INST-at-stgs '((LSU wbuf1)
						     (LSU wbuf1 lch)
						     (complete wbuf1)
						     (commit wbuf1)) MT))
				   (j i)))
		  :in-theory (disable INST-IN-ORDER-P-INST-MODIFIED
				      INST-IN-ORDER-P-INST-SPECULTV)))))

(local
(defthm wbuf1-stg-p-LMM-before-if-commit-stg
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA))))
		  (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) addr)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (commit-stg-p
		   (INST-stg (LMM-before i addr MT))))
	      (wbuf1-stg-p (INST-stg (LMM-before i addr MT))))
  :hints (("goal" :in-theory (enable commit-stg-p)))))

(local
(defthm not-retire-stg-LMM-before-help
    (implies (and (wbuf1-stg-p (INST-stg (inst-at-stgs stgs MT)))
		  (retire-stg-p (INST-stg
				(LMM-before i addr MT))))
	     (not (equal (LMM-before i addr MT)
			 (inst-at-stgs stgs MT))))
  :hints (("goal" :in-theory (enable wbuf1-stg-p retire-stg-p)))))

(local
(defthm not-retire-stg-LMM-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA))))
		  (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) addr)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (not (retire-stg-p
		   (INST-stg (LMM-before i addr MT)))))
    :hints (("goal" :use ((:instance INST-in-order-p-retire-wbuf1
				   (i (LMM-before i addr MT))
				   (j (INST-at-stgs '((LSU wbuf1)
						      (LSU wbuf1 lch)
						      (complete wbuf1)
						      (commit wbuf1)) MT)))
			(:instance INST-in-order-p-wbuf1-rbuf
				   (j i)
				   (i (INST-at-stgs '((LSU wbuf1)
						      (LSU wbuf1 lch)
						      (complete wbuf1)
						      (commit wbuf1)) MT)))
			(:instance INST-IN-ORDER-P-INST-SPECULTV
				   (i (INST-at-stgs '((LSU wbuf1)
						     (LSU wbuf1 lch)
						     (complete wbuf1)
						     (commit wbuf1)) MT))
				   (j i))
			(:instance INST-IN-ORDER-P-INST-MODIFIED
				   (i (INST-at-stgs '((LSU wbuf1)
						     (LSU wbuf1 lch)
						     (complete wbuf1)
						     (commit wbuf1)) MT))
				   (j i)))
		  :in-theory (disable INST-IN-ORDER-P-INST-MODIFIED
				      INST-IN-ORDER-P-INST-SPECULTV)))))

; If rbuf-wbuf1? is on, and the load and store addresses match,
; then the last memory modifier before i is at wbuf1. 
(defthm wbuf1-stg-p-LMM-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA))))
		  (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) addr)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	      (wbuf1-stg-p
	       (INST-stg
		(LMM-before i addr MT))))
  :hints (("goal" :in-theory (e/d ()
				  (INST-IN-ORDER-LMM-BEFORE
				   INST-is-at-one-of-the-stages))
		  :use ((:instance INST-is-at-one-of-the-stages
			   (i (LMM-before i addr MT)))))))
)

; If i is a memory modifier, the third operand value is stored in the
; memory at address addr.
(defthm read-mem-ISA-post-ISA-mem-modifier
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (mem-modifier-p addr i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (INST-exintr? i)))
		  (not (b1p (INST-excpt? i))))
	     (equal (read-mem addr (ISA-mem (INST-post-ISA i)))
		    (INST-src-val3 i)))
  :hints (("goal" :in-theory (enable mem-modifier-p lift-b-ops
				     INST-ld-st?  INST-excpt?
				     INST-fetch-error? INST-cntlv
				     INST-opcode INST-store-addr
				     ISA-st ISA-sti
				     INST-im INST-src-val3 INST-rc
				     INST-rb INST-ra
				     INST-data-access-error?
				     INST-STORE-ERROR? INST-decode-error?
				     DECODE-ILLEGAL-INST?
				     ISA-step INST-store?))))
	   
; An important lemma. 
; This proves that the load-bypassing is working fine.
; The third source value of the last memory modifier before instruction i
; is the correct value read by instruction i from addr.
(defthm INST-src-val3-LMM-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (addr-p addr)
		  (exist-LMM-before-p i addr MT)
		  (not (retire-stg-p (INST-stg
				      (LMM-before i addr MT))))
		  (execute-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (equal (INST-src-val3 (LMM-before i addr MT))
		    (read-mem addr (ISA-mem (INST-pre-ISA i)))))
  :hints (("goal" :use (:instance read-mem-LMM-before)
		  :in-theory (e/d (INST-exintr-INST-in-if-not-retired)
				  (INST-POST-ISA-INST-IN)))))

; This lemmas says that the result of the load instruction i is
; the memory value at address (INST-load-addr i) in the pre-ISA of i.
(defthm read-mem-INST-load-addr-INST-pre-ISA
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (INST-load? i)))
	     (equal (read-mem (INST-load-addr i) (ISA-mem (INST-pre-ISA i)))
		    (INST-dest-val i)))
  :hints (("goal" :In-theory (enable INST-load? INST-load-addr
				     lift-b-ops INST-LSU? INST-ld-st?
				     INST-cntlv INST-opcode 
				     INST-ld-dest-val INST-ld-im-dest-val
				     INST-src-val1 INST-src-val2
				     decode logbit* rdb
				     INST-dest-val))))

; Field wbuf-val of write buffer 0 contains the result value of
; the load instruction i, if the rbuf-wbuf0? flag is on, and the load
; and store addresses match.
(defthm LSU-wbuf0-val-=-INST-dest-val
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(LSU rbuf))
		  (MA-input-p sigs) (MA-state-p MA) (MAETT-p MT)
		  (b1p (rbuf-wbuf0? (LSU-rbuf (MA-LSU MA))))
		  (not (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA)))))
		  (equal (INST-load-addr i)
			 (wbuf-addr (LSU-wbuf0 (MA-LSU MA))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (equal (wbuf-val (LSU-wbuf0 (MA-LSU MA)))
		    (INST-dest-val i)))
  :hints (("goal" :in-theory (enable LSU-LOAD-IF-AT-LSU-RBUF-LCH)
		  :restrict
		  ((LSU-wbuf0-val-=-INST-src-val3 
		    ((i (LMM-before i (INST-load-addr i) MT))))
		   (LSU-wbuf0-addr-=-INST-store-addr 
		    ((i (LMM-before i (INST-load-addr i) MT))))))))

; Again field wbuf-val of wbuf0 contains the result value for
; instruction i.  The difference between the previous lemma and
; this lemma is the reason of wbuf1 not intercepting. 
; In the previous lemma, rbuf-wbuf1? was 0.  In this lemma, the load
; address does not match the store address of the write in wbuf1.
(defthm LSU-wbuf0-val-=-INST-dest-val-2
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(LSU rbuf))
		  (MA-input-p sigs) (MA-state-p MA) (MAETT-p MT)
		  (b1p (rbuf-wbuf0? (LSU-rbuf (MA-LSU MA))))
		  (equal (INST-load-addr i)
			 (wbuf-addr (LSU-wbuf0 (MA-LSU MA))))
		  (not (equal (INST-load-addr i)
			      (wbuf-addr (LSU-wbuf1 (MA-LSU MA)))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (equal (wbuf-val (LSU-wbuf0 (MA-LSU MA)))
		    (INST-dest-val i)))
  :hints (("goal" :in-theory (enable LSU-LOAD-IF-AT-LSU-RBUF-LCH)
		  :restrict
		  ((LSU-wbuf0-val-=-INST-src-val3 
		    ((i (LMM-before i (INST-load-addr i) MT))))
		   (LSU-wbuf0-addr-=-INST-store-addr 
		    ((i (LMM-before i (INST-load-addr i) MT))))))))

; Field wbuf-val of write buffer 1 contain the result value for load
; instruction i, when the load and store addresses are equal.
(defthm LSU-wbuf1-val-=-INST-dest-val
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(LSU rbuf))
		  (MA-input-p sigs) (MA-state-p MA) (MAETT-p MT)
		  (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA))))
		  (equal (INST-load-addr i)
			 (wbuf-addr (LSU-wbuf1 (MA-LSU MA))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (equal (wbuf-val (LSU-wbuf1 (MA-LSU MA)))
		    (INST-dest-val i)))
  :hints (("goal" :in-theory (enable LSU-LOAD-IF-AT-LSU-RBUF-LCH)
		  :restrict
		  ((LSU-wbuf1-val-=-INST-src-val3 
		    ((i (LMM-before i (INST-load-addr i) MT))))
		   (LSU-wbuf1-addr-=-INST-store-addr 
		    ((i (LMM-before i (INST-load-addr i) MT))))))))

; A landmark lemma. 
; If LSU-address-match? is 1, then the load forwarding value LSU-forward-wbuf
; is the correct result of the load instruction at the rbuf stage. 
; This guarantees that the load-forwarding is working correctly.
; See the definition of LSU-forward-wbuf.
(defthm LSU-forward-wbuf-INST-dest-val
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(LSU rbuf))
		  (MA-input-p sigs)
		  (b1p (release-rbuf? (MA-LSU MA) MA sigs))
		  (b1p (LSU-address-match? (MA-LSU MA)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	      (equal (LSU-forward-wbuf (MA-LSU MA))
		     (INST-dest-val i)))
  :hints (("goal" :in-theory (enable LSU-forward-wbuf lift-b-ops
				     LSU-address-match?))))

;; From here we prove read-mem-INST-load-addr-INST-dest-val.
;; This lemma proves that the normal memory read possibly
;; with load bypassing is working correctly.

; A help lemma.
; Suppose instruction i and  j (which is (car trace)).  J precedes i 
; in program order.  If there is no memory modifier between
; j and i, then the memory value at address addr in the pre-ISA state of j
; and  the pre-ISA state of i are identical.
(local
(defthm read-mem-when-no-mem-modifier-before
    (implies (and (inv MT MA)
		  (consp trace)
		  (subtrace-p trace MT)
		  (not (trace-exist-LMM-before-p i addr trace))
		  (member-equal i trace)
		  (syntaxp (not (and (consp i) (equal (car i) 'car))))
		  (INST-listp trace)
		  (INST-p i)
		  (addr-p addr)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (read-mem addr (ISA-mem (INST-pre-ISA (car trace))))
		    (read-mem addr (ISA-mem (INST-pre-ISA i)))))
  :hints ((when-found (INST-PRE-ISA (CAR (CDR TRACE)))
		      (:cases ((consp (cdr trace)))))
	  ("goal" :induct t))))

(encapsulate nil
; A help lemma. 
; There is no retired memory modifier following a non-retired instruction.
(local
(defthm not-INST-in-order-p-retired-non-retired
    (implies (and (inv MT MA)
		  (not (retire-stg-p (INST-stg i)))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (retire-stg-p (INST-stg j))
		  (INST-in-order-p i j MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (not (mem-modifier-p addr j)))
  :hints (("goal" :in-theory (enable INST-in-order-p-retired-store-non-retired
				     mem-modifier-p)))))

(local
(defthm not-trace-exist-mem-modifier-cdr-if-no-active-induct
    (implies (and (inv MT MA)
		  (subtrace-after-p j trace MT)
		  (INST-p j) (INST-in j MT) 
		  (INST-listp trace)
		  (not (retire-stg-p (INST-stg j)))
		  (not (trace-exist-non-retired-LMM-before-p i addr trace))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (trace-exist-LMM-before-p i addr trace)))
  :hints (("goal" :restrict ((not-INST-in-order-p-retired-non-retired
			      ((i j))))))
  :rule-classes nil))

; A help lemma. 
; If trace-exist-non-retired-LMM-before-p and 
; trace-exist-LMM-before-p are equivalent on (cdr trace)
; if (car trace) is retired.
(local
(defthm not-trace-exist-mem-modifier-cdr-if-no-active
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (INST-p j) (INST-listp trace)
		  (not (retire-stg-p (INST-stg (car trace))))
		  (not (trace-exist-non-retired-LMM-before-p i addr
							     (cdr trace)))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (trace-exist-LMM-before-p i addr (cdr trace))))
  :hints (("goal" :use (:instance
			not-trace-exist-mem-modifier-cdr-if-no-active-induct
			(j (car trace)) (trace (cdr trace)))))))

(local
(defthm read-mem-when-no-active-mem-modifier-before-induct
    (implies (and (inv MT MA)
		  (consp trace)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (member-equal i trace)
		  (INST-p i) (INST-in i MT)
		  (addr-p addr)
		  (not (retire-stg-p (INST-stg i)))
		  (not (trace-exist-non-retired-LMM-before-p i addr trace))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (read-mem addr
			      (trace-mem trace
					 (ISA-mem (INST-pre-ISA (car trace)))))
		    (read-mem addr (ISA-mem (INST-pre-ISA i)))))
  :hints ((when-found (INST-PRE-ISA (CAR (CDR TRACE)))
		      (:cases ((consp (cdr trace)))))
	  ("goal" :restrict ((read-mem-when-no-mem-modifier-before
			      ((i i))))))
  :rule-classes nil))

(local
(defthm read-mem-when-no-active-mem-modifier-before-help
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (retire-stg-p (INST-stg i)))
		  (not (exist-non-retired-LMM-before-p i addr MT))
		  (MAETT-p MT) (MA-state-p MA)
		  (addr-p addr))
	     (equal (read-mem addr (MT-mem MT))
		    (read-mem addr (ISA-mem (INST-pre-ISA i)))))
; Matt K. mod: Apparently heuristics have somehow changed.  The proof goes
; through by replacing the original hints with corresponding proof-builder
; commands.
#|
  :hints (("goal" :in-theory (e/d (exist-non-retired-LMM-before-p
				   INST-in MT-mem)
				  (MT-MEM-=-MA-MEM))
		  :use (:instance
			read-mem-when-no-active-mem-modifier-before-induct
			(trace (MT-trace MT)))))
|#
  :instructions ((:in-theory (e/d (exist-non-retired-LMM-before-p
				   INST-in MT-mem)
				  (MT-MEM-=-MA-MEM)))
                 (:use (:instance
			read-mem-when-no-active-mem-modifier-before-induct
			(trace (MT-trace MT))))
                 :prove)
  :rule-classes nil))

; A critical lemma.
;
; If there is no non-retired memory modifier before i, the memory value in
; the current state is the ideal load value for instruction i.  This
; helps to show that the load bypassing is working correctly.
(defthm read-mem-when-no-active-mem-modifier-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (retire-stg-p (INST-stg i)))
		  (not (exist-non-retired-LMM-before-p i addr MT))
		  (addr-p addr)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (read-mem addr (MA-mem MA))
		    (read-mem addr (ISA-mem (INST-pre-ISA i)))))
  :hints (("goal" :use (:instance
			read-mem-when-no-active-mem-modifier-before-help))))
)

(local
(defthm not-wbuf0-p-mem-modifier-if-LSU-address-match
    (implies (and (inv MT MA)
		  (not (b1p (LSU-address-match? (MA-LSU MA))))
		  (INST-in-order-p i j MT)
		  (equal (INST-stg j) '(LSU rbuf))
		  (wbuf0-stg-p (INST-stg i))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (inst-specultv? j)))
		  (not (b1p (INST-modified? j))))
	     (not (mem-modifier-p (INST-load-addr j) i)))
  :hints (("Goal" :in-theory (enable lift-b-ops LSU-address-match?
				     mem-modifier-p
				     inst-in-order-p-rbuf-wbuf0)
		  :cases ((b1p (inst-specultv? i)) (b1p (INST-modified? i)))
		  :restrict ((LSU-WBUF0-ADDR-=-INST-STORE-ADDR
			      ((i i))))))))

(local
(defthm not-wbuf1-p-mem-modifier-if-LSU-address-match
    (implies (and (inv MT MA)
		  (not (b1p (LSU-address-match? (MA-LSU MA))))
		  (INST-in-order-p i j MT)
		  (equal (INST-stg j) '(LSU rbuf))
		  (wbuf1-stg-p (INST-stg i))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (inst-specultv? j)))
		  (not (b1p (INST-modified? j))))
	     (not (mem-modifier-p (INST-load-addr j) i)))
  :hints (("Goal" :in-theory (enable lift-b-ops LSU-address-match?
				     mem-modifier-p
				     inst-in-order-p-rbuf-wbuf1)
		  :cases ((b1p (inst-specultv? i)) (b1p (INST-modified? i)))
		  :restrict ((LSU-WBUF1-ADDR-=-INST-STORE-ADDR
			      ((i i))))))))

(local
(defthm not-mem-modifier-p-if-IU-MU-BU
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (or (BU-stg-p (INST-stg i)) (IU-stg-p (INST-stg i))
		      (MU-stg-p (INST-stg i)))
		  (INST-p i)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (mem-modifier-p addr i)))
  :hints (("goal" :in-theory (enable mem-modifier-p equal-b1p-converter
				     INST-TYPE-EXCLUSIVE)
		  :use ((:instance INST-BU-IF-BU-STG-P)
			(:instance INST-IU-IF-IU-STG-P)
			(:instance INST-MU-IF-MU-STG-P))))))

(local
(defthm not-mem-modifier-p-if-rbuf-lch
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (or (equal (INST-stg i) '(LSU rbuf))
		      (equal (INST-stg i) '(LSU lch)))
		  (INST-p i)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (mem-modifier-p addr i)))
  :hints (("goal" :in-theory (enable mem-modifier-p
				     LSU-LOAD-IF-AT-LSU-RBUF-LCH)))))

(local
(defthm not-mem-modifier-p-if-complete
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(complete))
		  (INST-p i)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (mem-modifier-p addr i)))
  :hints (("goal" :in-theory (enable mem-modifier-p
				     not-INST-store-if-complete)))))
(local
(in-theory (disable not-mem-modifier-p-if-complete
		    not-mem-modifier-p-if-rbuf-lch)))
     

(encapsulate nil
(local
(defthm retired-stg-p-mem-modifier-if-not-LSU-address-match-case1
    (implies (and (inv MT MA)
		  (not (b1p (LSU-address-match? (MA-LSU MA))))
		  (INST-in-order-p i j MT)
		  (equal (INST-stg j) '(LSU rbuf))
		  (commit-stg-p (INST-stg i))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (inst-specultv? j)))
		  (not (b1p (INST-modified? j))))
	     (not (mem-modifier-p (INST-load-addr j) i)))
  :hints (("Goal" :in-theory (enable commit-stg-p)))))

(local
(defthm retired-stg-p-mem-modifier-if-not-LSU-address-match-case2
    (implies (and (inv MT MA)
		  (not (b1p (LSU-address-match? (MA-LSU MA))))
		  (INST-in-order-p i j MT)
		  (equal (INST-stg j) '(LSU rbuf))
		  (complete-stg-p (INST-stg i))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (inst-specultv? j)))
		  (not (b1p (INST-modified? j))))
	     (not (mem-modifier-p (INST-load-addr j) i)))
  :hints (("goal" :in-theory (enable complete-stg-p
				     lift-b-ops
				     INST-excpt?
				     not-mem-modifier-p-if-complete)
		  :cases ((b1p (inst-specultv? i))
			  (b1p (INST-modified? i))
			  (b1p (INST-fetch-error? i))
			  (b1p (INST-decode-error? i)))))))

(local
 (defthm retired-stg-p-mem-modifier-if-not-LSU-address-match-case3
    (implies (and (inv MT MA)
		  (not (b1p (LSU-address-match? (MA-LSU MA))))
		  (INST-in-order-p i j MT)
		  (equal (INST-stg j) '(LSU rbuf))
		  (execute-stg-p (INST-stg i))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (inst-specultv? j)))
		  (not (b1p (INST-modified? j))))
	     (not (mem-modifier-p (INST-load-addr j) i)))
  :hints (("goal" :in-theory (enable execute-stg-p LSU-stg-p
				     not-mem-modifier-p-if-rbuf-lch
				     INST-in-order-p-LSU-issued-RS)
		  :cases ((b1p (inst-specultv? i))
			  (b1p (INST-modified? i)))))))

; Suppose instruction i is a memory modifier of the location where
; j is going to read.  If LSU-address-match? is 0, i must have already
; retired. 
(defthm retired-stg-p-mem-modifier-if-not-LSU-address-match
    (implies (and (inv MT MA)
		  (not (b1p (LSU-address-match? (MA-LSU MA))))
		  (INST-in-order-p i j MT)
		  (equal (INST-stg j) '(LSU rbuf))
		  (not (retire-stg-p (INST-stg i)))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (inst-specultv? j)))
		  (not (b1p (INST-modified? j))))
	     (not (mem-modifier-p (INST-load-addr j) i)))
  :hints (("goal" :use ((:instance INST-is-at-one-of-the-stages (i i)))
		  :in-theory (disable INST-is-at-one-of-the-stages))))
)

(encapsulate  nil
(local
(defthm not-exist-non-retired-LMM-before-p-if-not-address-match-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (equal (INST-stg i) '(LSU rbuf))
		  (not (b1p (LSU-address-match? (MA-LSU MA))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (member-equal i trace)
		  (INST-p i) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA))
	     (not (trace-exist-non-retired-LMM-before-p i (INST-load-addr i)
							  trace)))
  :hints (("goal" :in-theory (enable exception-relations)))))

; If LSU-address-match? is 0, there is no non-retired memory modifier
; at the address specified by INST-load-addr.
(defthm not-exist-non-retired-LMM-before-p-if-not-address-match
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (not (b1p (LSU-address-match? (MA-LSU MA))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA))
	     (not (exist-non-retired-LMM-before-p i (INST-load-addr i) MT)))
  :hints (("goal" :in-theory (enable INST-in
				     exist-non-retired-LMM-before-p))))
)

; A landmark lemma.
; If LSU-address-match? is 0, the value in the memory
; is, in fact, the destination value of instruction i. 
; This guarantees that the load bypassing is working correctly.
(defthm read-mem-INST-load-addr-INST-dest-val
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(LSU rbuf))
		  (not (b1p (LSU-address-match? (MA-LSU MA))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (read-mem (INST-load-addr i) (MA-mem MA))
		    (INST-dest-val i)))
  :hints (("goal" :in-theory (enable LSU-LOAD-IF-AT-LSU-RBUF-LCH))))
		   
; A landmark lemma
; The instruction invariants are preserved if i's next stage is LSU-lch.
; The proof has to consider the load-bypassing and load-forwarding. 
; The proof uses two lemmas:
;   LSU-forward-wbuf-INST-dest-val
;   read-mem-INST-load-addr-INST-dest-val
(defthm LSU-lch-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(LSU lch)))
	     (LSU-lch-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :use (:instance stages-reachable-to-LSU-lch)
		  :in-theory (enable LSU-lch-inst-inv MA-step lift-b-ops
				     LSU-LOAD-IF-AT-LSU-RBUF-LCH
				     CHECK-WBUF0? check-wbuf1?
				     release-rbuf?
				     step-LSU step-LSU-lch))))

; A landmark lemma
; Instruction invariants are preserved in the LSU.
(defthm LSU-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS)))
		  (LSU-stg-p (INST-stg (step-INST I MT MA sigs))))
	     (LSU-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable LSU-stg-p LSU-inst-inv))))

;;;;;;;;;;;;Proof of execute-inst-robe-inv-step-INST;;;;;;;;;;;;;;;;;

; When an instruction is dispatched, the entry at the tail of the ROB
; records the instruction.
(defthm robe-receive-inst-MT-rob-tail
    (implies (and (b1p (dispatch-inst? MA))
		  (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (robe-receive-INST? (MA-rob MA) (MT-rob-tail MT) MA) 1))
  :hints (("goal" :in-theory (enable robe-receive-INST?
				     equal-b1p-converter))))

; If both instructions dispatch and commit take place this cycle,
; ROB-head and ROB-tail are not identical, i.e., the ROB is not empty
; nor full.
(defthm ROB-head-tail-not-equal-if-dispatch-and-commit
    (implies (and (inv MT MA)
		  (b1p (dispatch-inst? MA))
		  (b1p (commit-inst? MA))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (equal (MT-ROB-head MT) (MT-ROB-tail MT))))
  :hints (("goal" :in-theory (enable MA-def lift-b-ops))))

; The output of dispatch-pc from the dispatch logic is the program
; counter value for the dispatched instruction i.
(defthm dispatch-pc-INST-pc
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (dispatch-pc MA) (INST-pc i)))
  :hints (("goal" :in-theory (enable dispatch-pc))))

; The output dispatch-dest-reg from the dispatch logic is the
; destination register for the dispatched instruction i.
(defthm dispatch-dest-reg-INST-dest-reg
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(DQ 0))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (INST-fetch-error-detected-p i))
		  (INST-writeback-p i))
	     (equal (dispatch-dest-reg MA) (INST-dest-reg i)))
  :hints (("goal" :in-theory (enable dispatch-dest-reg
				     DQ-OUT-DEST-REG
				     INST-cntlv
				     INST-opcode
				     lift-b-ops
				     INST-writeback-p
				     INST-DEST-REG))))
     
(local
(defthm INST-cntlv-exunit-branch-0-if-decode-error
    (implies (and (INST-p i) (b1p (INST-decode-error? i)))
	     (equal (logbit 3 (cntlv-exunit (INST-cntlv i))) 0))
  :hints (("goal" :in-theory (enable INST-cntlv INST-decode-error?
				     decode-illegal-inst?
				     bv-eqv-iff-equal
				     equal-b1p-converter
				     INST-opcode
				     decode rdb logbit* lift-b-ops)))))

; The signal dispatch-excpt from a dispatch logic is the exception flags
; for the dispatched instruction.
(defthm dispatch-excpt-INST-excpt-flags
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(DQ 0))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (equal (dispatch-excpt MA) (INST-excpt-flags i)))
  :hints (("goal" :in-theory (enable dispatch-excpt))))

; An important lemma.
; Instruction-ROB invariants are preserved when instruction is dispatched
; from (DQ 0).
(defthm execute-inst-robe-inv-step-INST-from-DQ-0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS)))
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg i) '(DQ 0))
		  (execute-stg-p (INST-stg (step-INST I MT MA sigs))))
     (execute-inst-robe-inv (step-INST i MT MA sigs)
			    (nth-robe (INST-tag (step-INST i MT MA sigs))
				      (step-ROB MA sigs))))
  :hints (("goal" :in-theory (enable execute-inst-robe-inv lift-b-ops
				     INST-pc
				     INST-sync?
				     INST-WB-SREG?
				     INST-wb?
				     INST-rfeh?
				     INST-BU?
				     word-addr-p
				     step-robe)
		  :cases ((b1p (dispatch-inst? MA))))
	  ("subgoal 1" :cases ((b1p (inst-fetch-error? i))))))

(encapsulate nil
(local
(defthm not-robe-receive-inst-INST-tag-help-help
    (implies (and (inv MT MA)
		  (consistent-rob-flg-p (MA-rob MA))
		  (consistent-robe-p (nth-robe rix (MA-rob MA))
				     rix (MA-rob MA))
		  (b1p (robe-valid? (nth-robe rix (MA-rob MA))))
		  (not (b1p (ROB-full? (MA-rob MA))))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (equal rix (MT-rob-tail MT))))
  :hints (("goal" :in-theory (e/d (consistent-rob-flg-p
				   lift-b-ops
				   bv-eqv-iff-equal
				   rob-full?
				   consistent-robe-p)
				  (CONSISTENT-ROBE-P-NTH-ROBE))))))

(local
(defthm not-robe-receive-inst-INST-tag-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (b1p (dispatch-inst? MA))
		  (dispatched-p i)
		  (not (committed-p i)))
	     (not (equal (INST-tag i) (MT-rob-tail MT))))
  :hints (("goal" :in-theory (enable robe-receive-inst? 
				     equal-b1p-converter
				     lift-b-ops)
		  :cases ((not (consistent-rob-flg-p (MA-rob MA)))
			  (not (consistent-robe-p (nth-robe (INST-tag i)
							    (MA-rob MA))
						  (INST-tag i) (MA-rob MA)))))
	  ("subgoal 3" :in-theory (disable CONSISTENT-ROBE-P-NTH-ROBE)
		       :cases ((b1p (rob-full? (MA-rob MA)))))
	  ("subgoal 2" :in-theory (enable inv consistent-MA-p
					  consistent-rob-p)))
  :rule-classes nil))

; Suppose i is a dispatched but has not been committed.  The ROB entry
; to which i is assigned does not record another instruction.  In a sense,
; this proves that no resource conflict hazard occurs in the ROB.
(defthm not-robe-receive-inst-INST-tag
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (dispatched-p i)
		  (not (committed-p i)))
	     (equal (robe-receive-inst? (MA-ROB MA) (INST-tag i) MA) 0))
  :hints (("goal" :in-theory (enable robe-receive-inst? 
				     equal-b1p-converter
				     bv-eqv-iff-equal
				     lift-b-ops)
		  :use (:instance not-robe-receive-inst-INST-tag-help))))
)

; Following proof may be tedious. You can skip to
;    complete-stg-step-INST-if-robe-receive-result
;
; A help lemma to prove
;  complete-stg-step-INST-if-robe-receive-result
; This is the case where i is current in the IU.
(defthm not-robe-receive-result-iff-complete-step-IU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (IU-stg-p (INST-stg i)))
	     (iff (b1p (robe-receive-result? (MA-rob MA) (INST-tag i) MA))
		  (complete-stg-p (INST-stg (step-INST-IU i MA sigs)))))
  :hints (("goal" :in-theory (enable robe-receive-result? lift-b-ops
				     CDB-def issue-logic-def
				     IU-RS-field-INST-at-lemmas
				     MU-field-INST-at-lemmas
				     BU-RS-field-INST-at-lemmas
				     LSU-field-INST-at-lemmas
				     INST-at-stg-inst-stg-execute-2
				     BU-output-def
				     IU-output-def
				     IU-stg-p
				     step-INST-IU))))

; A help lemma to prove
;  complete-stg-step-INST-if-robe-receive-result
; This is the case where i is current in the MU.
(defthm not-robe-receive-result-iff-complete-step-MU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (MU-stg-p (INST-stg i)))
	     (iff (b1p (robe-receive-result? (MA-rob MA) (INST-tag i) MA))
		  (complete-stg-p (INST-stg (step-INST-MU i MA sigs)))))
  :hints (("goal" :in-theory (enable robe-receive-result? lift-b-ops
				     CDB-def issue-logic-def
				     IU-RS-field-INST-at-lemmas
				     MU-field-INST-at-lemmas
				     BU-RS-field-INST-at-lemmas
				     LSU-field-INST-at-lemmas
				     INST-at-stg-inst-stg-execute-2
				     bv-eqv-iff-equal
				     BU-output-def
				     IU-output-def
				     MU-stg-p
				     step-INST-MU))))

; A help lemma to prove
;  complete-stg-step-INST-if-robe-receive-result
; This is the case where i is current in the BU.
(defthm not-robe-receive-result-iff-complete-step-BU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (BU-stg-p (INST-stg i)))
	     (iff (b1p (robe-receive-result? (MA-rob MA) (INST-tag i) MA))
		  (complete-stg-p (INST-stg (step-INST-BU i MA sigs)))))
  :hints (("goal" :in-theory (enable robe-receive-result? lift-b-ops
				     CDB-def issue-logic-def
				     IU-RS-field-INST-at-lemmas
				     MU-field-INST-at-lemmas
				     BU-RS-field-INST-at-lemmas
				     LSU-field-INST-at-lemmas
				     BU-output-def IU-output-def
				     INST-at-stg-inst-stg-execute-2
				     BU-stg-p step-INST-BU))))

; WARNING!!!
; Proof of a help lemma for complete-stg-step-INST-if-robe-receive-result
; is tedious and requires more lemmas.
; You can skip to not-robe-receive-result-iff-complete-step-LSU

; Instruction at reservation station LSU-RS0 does not complete its execution
; this cycle.
(defthm not-complete-step-inst-LSU-RS0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(LSU RS0)))
	     (not (complete-stg-p
		   (INST-stg (step-INST-LSU-RS0 i MA sigs)))))
  :hints (("goal" :in-theory (enable step-INST-LSU-RS0))))

; The ROB entry which holds the instruction at LSU-RS0 does not get the
; result this cycle.
(defthm not-robe-receive-result-if-LSU-RS0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(LSU RS0)))
	     (equal (robe-receive-result? (MA-rob MA) (INST-tag i) MA) 0))
  :hints (("goal" :in-theory (enable robe-receive-result? lift-b-ops
				     equal-b1p-converter
				     CDB-def issue-logic-def
				     IU-RS-field-INST-at-lemmas
				     MU-field-INST-at-lemmas
				     BU-RS-field-INST-at-lemmas
				     LSU-field-INST-at-lemmas
				     BU-output-def
				     IU-output-def
				     INST-at-stg-inst-stg-execute-2))))

; Instruction at reservation station LSU-RS1 does not complete its execution
; this cycle.
(defthm not-robe-receive-result-iff-complete-step-LSU-RS1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(LSU RS1)))
	     (not (complete-stg-p
		   (INST-stg (step-INST-LSU-RS1 i MA sigs)))))
  :hints (("goal" :in-theory (enable step-INST-LSU-RS1))))

; The ROB entry which holds the instruction at LSU-RS1 does not get the
; result this cycle.
(defthm not-robe-receive-result-if-LSU-RS1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(LSU RS1)))
	     (equal (robe-receive-result? (MA-rob MA) (INST-tag i) MA) 0))
  :hints (("goal" :in-theory (enable robe-receive-result? lift-b-ops
				     equal-b1p-converter
				     CDB-def issue-logic-def
				     IU-RS-field-INST-at-lemmas
				     MU-field-INST-at-lemmas
				     BU-RS-field-INST-at-lemmas
				     LSU-field-INST-at-lemmas
				     BU-output-def
				     IU-output-def
				     step-INST-LSU-RS1
				     INST-at-stg-inst-stg-execute-2))))

; Instruction at stage LSU-wbuf0 does not complete its execution
; this cycle.
(defthm not-complete-stg-p-step-INST-LSU-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(LSU wbuf0)))
	     (not (complete-stg-p (INST-stg (step-INST-LSU-wbuf0 i MA)))))
  :hints (("goal" :in-theory (enable step-INST-LSU-wbuf0))))

; The ROB entry which holds instruction at LSU-wbuf0 does not get the
; result this cycle.
(defthm not-robe-receive-result-if-LSU-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(LSU wbuf0)))
	     (equal (robe-receive-result? (MA-rob MA) (INST-tag i) MA) 0))
  :hints (("goal" :in-theory (enable robe-receive-result? lift-b-ops
				     equal-b1p-converter
				     CDB-def issue-logic-def
				     IU-RS-field-INST-at-lemmas
				     MU-field-INST-at-lemmas
				     BU-RS-field-INST-at-lemmas
				     LSU-field-INST-at-lemmas
				     BU-output-def
				     IU-output-def
				     step-INST-LSU-wbuf0
				     INST-at-stg-inst-stg-execute-2))))

; Instruction at stage LSU-wbuf1 does not complete its execution
; this cycle.
(defthm not-complete-stg-step-INST-LSU-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(LSU wbuf1)))
	     (not (complete-stg-p (INST-stg (step-INST-LSU-wbuf1 i MA sigs)))))
  :hints (("goal" :in-theory (enable step-INST-LSU-wbuf1))))

; The ROB entry which holds instruction at LSU-wbuf1 does not get the
; result this cycle.
(defthm not-robe-receive-result-if-LSU-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(LSU wbuf1)))
	     (equal (robe-receive-result? (MA-rob MA) (INST-tag i) MA) 0))
  :hints (("goal" :in-theory (enable robe-receive-result? lift-b-ops
				     equal-b1p-converter
				     CDB-def issue-logic-def
				     IU-RS-field-INST-at-lemmas
				     MU-field-INST-at-lemmas
				     BU-RS-field-INST-at-lemmas
				     LSU-field-INST-at-lemmas
				     BU-output-def
				     IU-output-def
				     step-INST-LSU-RS1
				     INST-at-stg-inst-stg-execute-2))))

; The instruction at stage LSU-rbuf does not complete its execution
; this cycle.
(defthm not-complete-stg-p-step-INST-LSU-rbuf
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(LSU rbuf)))
	     (not (complete-stg-p (INST-stg (step-INST-LSU-rbuf i MA sigs)))))
  :hints (("goal" :in-theory (enable step-INST-LSU-rbuf))))

; The ROB entry which holds instruction at LSU-rbuf does not get the
; result this cycle.
(defthm not-robe-receive-result-iff-complete-step-LSU-rbuf
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(LSU rbuf)))
	     (equal (robe-receive-result? (MA-rob MA) (INST-tag i) MA) 0))
  :hints (("goal" :in-theory (enable robe-receive-result? lift-b-ops
				     equal-b1p-converter
				     CDB-def issue-logic-def
				     IU-RS-field-INST-at-lemmas
				     MU-field-INST-at-lemmas
				     BU-RS-field-INST-at-lemmas
				     LSU-field-INST-at-lemmas
				     BU-output-def
				     IU-output-def
				     step-INST-LSU-RS1
				     INST-at-stg-inst-stg-execute-2))))

; The instruction at stage LSU-wbuf0-lch complete its execution
; this cycle.
(defthm complete-stg-p-step-INST-LSU-wbuf0-lch
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(LSU wbuf0 lch)))
	     (complete-stg-p (INST-stg (step-INST-LSU-wbuf0-lch i))))
  :hints (("goal" :in-theory (enable step-INST-LSU-wbuf0-lch))))

(local
(defthm not-uniq-inst-at-stgs-if-inst-in
    (implies (and (inv MT MA)
		  (INST-p I) (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (member-equal (INST-stg i)
				'((LSU LCH) (LSU WBUF0 LCH)
				  (LSU WBUF1 LCH))))
	     (equal (INST-at-stgs '((LSU LCH) (LSU WBUF0 LCH)
				    (LSU WBUF1 LCH))
				  MT)
		    i))
  :hints (("goal" :cases ((UNIQ-INST-AT-STGS '((LSU LCH)
                                                   (LSU WBUF0 LCH)
                                                   (LSU WBUF1 LCH))
                                                 MT)
			  (NO-INST-AT-STGS '((LSU LCH)
                                                 (LSU WBUF0 LCH)
                                                 (LSU WBUF1 LCH))
                                               MT))
		  :in-theory (enable NOT-NO-INST-AT-STGS-INST-STG-IF-INST-IN
				     INST-at-stgs-if-INST-in)))))

; The ROB entry holding the instruction at stage LSU-wbuf0-lch
; gets its result this cycle.
(defthm not-robe-receive-result-iff-complete-step-LSU-wbuf0-lch
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(LSU wbuf0 lch)))
	     (equal (robe-receive-result? (MA-rob MA) (INST-tag i) MA) 1))
  :hints (("goal" :in-theory (enable robe-receive-result? lift-b-ops
				     equal-b1p-converter
				     CDB-def issue-logic-def
				     IU-RS-field-INST-at-lemmas
				     MU-field-INST-at-lemmas
				     BU-RS-field-INST-at-lemmas
				     LSU-field-INST-at-lemmas
				     strong-inst-at-stg-theory
				     BU-output-def
				     IU-output-def
				     INST-at-stg-inst-stg-execute-2))))

; The instruction at stage LSU-wbuf1-lch completes its execution
; this cycle.
(defthm complete-stg-p-step-INST-LSU-wbuf1-lch
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(LSU wbuf1 lch)))
	     (complete-stg-p
	      (INST-stg (step-INST-LSU-wbuf1-lch i MA sigs))))
  :hints (("goal" :in-theory (enable step-INST-LSU-wbuf1-lch))))

; The ROB entry holding the instruction at stage LSU-wbuf1-lch
; gets its result this cycle.
(defthm robe-receive-result-if-LSU-wbuf1-lch
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(LSU wbuf1 lch)))
	     (equal (robe-receive-result? (MA-rob MA) (INST-tag i) MA) 1))
  :hints (("goal" :in-theory (enable robe-receive-result? lift-b-ops
				     equal-b1p-converter
				     CDB-def issue-logic-def
				     IU-RS-field-INST-at-lemmas
				     MU-field-INST-at-lemmas
				     BU-RS-field-INST-at-lemmas
				     LSU-field-INST-at-lemmas
				     strong-inst-at-stg-theory
				     BU-output-def
				     IU-output-def
				     INST-at-stg-inst-stg-execute-2))))

; Instruction at stage LSU-lch complete its execution
; this cycle.
(defthm not-robe-receive-result-iff-complete-step-LSU-lch
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(LSU lch)))
	     (complete-stg-p (INST-stg (step-INST-LSU-lch i))))
  :hints (("goal" :in-theory (enable step-INST-LSU-lch))))

; The ROB entry holding the instruction at stage LSU-lch
; gets its result this cycle.
(defthm robe-receive-result-if-execute-LSU-lch
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(LSU lch)))
	     (equal (robe-receive-result? (MA-rob MA) (INST-tag i) MA) 1))
  :hints (("goal" :in-theory (enable robe-receive-result? lift-b-ops
				     equal-b1p-converter
				     CDB-def issue-logic-def
				     IU-RS-field-INST-at-lemmas
				     MU-field-INST-at-lemmas
				     BU-RS-field-INST-at-lemmas
				     LSU-field-INST-at-lemmas
				     strong-inst-at-stg-theory
				     BU-output-def
				     IU-output-def
				     INST-at-stg-inst-stg-execute-2))))

; A help lemma to prove
;  complete-stg-step-INST-if-robe-receive-result
; This is the case where i is currently in the LSU.
(defthm not-robe-receive-result-iff-complete-step-LSU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (LSU-stg-p (INST-stg i)))
	     (iff (b1p (robe-receive-result? (MA-rob MA) (INST-tag i) MA))
		  (complete-stg-p (INST-stg (step-INST-LSU i MA sigs)))))
  :hints (("goal" :in-theory (enable LSU-stg-p step-INST-LSU))))

; Suppose i is an instruction in an execution stage. 
; The ROB entry assigned to i gets its result iff i completes this cycle.
(defthm complete-stg-step-INST-if-robe-receive-result
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (INST-p I)
		  (MAETT-p MT) (MA-state-p MA)
		  (execute-stg-p (INST-stg i)))
	     (iff (complete-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (b1p (robe-receive-result? (MA-rob MA) (INST-tag i) MA))))
  :hints (("goal" :in-theory (enable step-INST-opener lift-b-ops
				     execute-stg-p
				     step-INST-execute)))
  :rule-classes
  ((:rewrite :corollary
     (implies (and (inv MT MA)
		   (INST-in i MT) (INST-p i)
		   (MAETT-p MT) (MA-state-p MA)
		   (execute-stg-p (INST-stg i))
		   (b1p (robe-receive-result? (MA-rob MA) (INST-tag i) MA)))
	      (complete-stg-p (INST-stg (step-INST i MT MA sigs)))))
   (:rewrite :corollary
     (implies (and (inv MT MA)
		   (INST-in i MT) (INST-p i)
		   (MAETT-p MT) (MA-state-p MA)
		   (execute-stg-p (INST-stg i))
		   (execute-stg-p (INST-stg i))
		   (not (b1p (robe-receive-result? (MA-rob MA)
						   (INST-tag i) MA))))
	      (not (complete-stg-p (INST-stg (step-INST i MT MA sigs))))))))

(encapsulate nil
(local
(defthm not-CDB-ready-for-INST-tag-if-complete-help
    (implies (and (inv MT MA)
		  (complete-stg-p (INST-stg i))
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (CDB-ready? MA)))
	     (not (equal (CDB-tag MA) (INST-tag i))))
  :hints (("goal" :in-theory (enable CDB-tag CDB-ready? lift-b-ops
				     IU-output-def BU-output-def
				     LSU-output-def MU-output-def
				     CDB-def issue-logic-def
				     LSU-field-lemmas MU-field-lemmas
				     BU-RS-field-lemmas IU-RS-field-lemmas)))))

; The CDB is not ready for a completed instruction. (a kind of trivial fact.)
(defthm not-CDB-ready-for-INST-tag-if-complete
    (implies (and (inv MT MA)
		  (complete-stg-p (INST-stg i))
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (CDB-ready-for? (INST-tag i) MA) 0))
  :hints (("goal" :in-theory (enable CDB-ready-for? lift-b-ops
				     bv-eqv-iff-equal equal-b1p-converter))))
)

; If instruction i is in complete-stg, the ROB entry to which i is assigned
; does not receive another instruction.
(defthm not-robe-receive-result-if-complete-stg
    (implies (and (inv MT MA)
		  (complete-stg-p (INST-stg i))
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (robe-receive-result? (MA-rob MA) (INST-tag i) MA) 0))
  :hints (("goal" :in-theory (enable robe-receive-result?
				     lift-b-ops equal-b1p-converter))))

; An important lemma. 
; Instruction invariants for the ROB are preserved for instruction i if
; i stays in an execution stage.
(defthm execute-inst-robe-inv-step-INST-from-execute-stg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (execute-stg-p (INST-stg i))
		  (execute-stg-p (INST-stg (step-INST I MT MA sigs))))
     (execute-inst-robe-inv (step-INST i MT MA sigs)
			    (nth-robe (INST-tag i) (step-ROB MA sigs))))
  :hints (("goal" :in-theory (e/d (lift-b-ops
				   step-robe
				   INST-pc
				   exception-relations
				   INST-excpt-detected-p
				   execute-inst-robe-inv)
				  (ROBE-BRANCH-INST-BRANCH-2)))))

; A landmark lemma
; The instruction-ROB invariants are preserved for instruction i, if
; i is in execute-stg in the next cycle.
; The proof is divided into the proofs of 
;   execute-inst-robe-inv-step-INST-from-DQ-0 
;   execute-inst-robe-inv-step-INST-from-execute-stg
(defthm execute-inst-robe-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS))) 
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (execute-stg-p (INST-stg (step-INST I MT MA sigs))))
     (execute-inst-robe-inv (step-INST i MT MA sigs)
			    (nth-robe (INST-tag (step-INST i MT MA sigs))
				      (step-ROB MA sigs))))
  :hints (("goal" :use (:instance stages-reachable-to-execute)
		  :in-theory (disable nth-robe-step-rob))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; End of the proof of  execute-inst-robe-inv-step-INST
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; A landmark lemma execute-inst-inv-step-INST. 
; The instruction invariants preserved for i if i is in execute-stg in 
; the next cycle.
(defthm execute-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS)))
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (execute-stg-p (INST-stg (step-INST I MT MA sigs))))
	     (execute-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (e/d (execute-inst-inv execute-stg-p)
				  (nth-robe-step-rob)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;   Proof of complete-inst-inv
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; The proof of complete-inst-inv is divided into
;  complete-normal-inst-inv-step-INST
;  complete-wbuf0-inst-inv-step-INST
;  complete-wbuf1-inst-inv-step-INST
; Before proving these lemmas, we also prove
;   complete-inst-robe-inv-step-INST,
; which is used in the proof of all three lemmas above.
(encapsulate nil
(local
 (defthm not-dispatch-no-unit-if-INST-bu
     (implies (and (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (inst-p i) (INST-in i MT)
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (equal (INST-stg i) '(DQ 0))
		   (not (b1p (INST-fetch-error? i)))
		   (b1p (INST-bu? i)))
	      (equal (dispatch-no-unit? MA) 0))
 :hints (("goal" :in-theory (enable dispatch-no-unit? lift-b-ops
				    equal-b1p-converter
				    INST-bu? INST-cntlv
				    INST-DECODE-ERROR-DETECTED-P
				    decode logbit* rdb
				    INST-excpt-detected-p
				    DQ-READY-NO-UNIT?)))))

(local
 (defthm not-dispatch-no-unit-if-INST-write-back
     (implies (and (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (inst-p i) (INST-in i MT)
		   (equal (INST-stg i) '(DQ 0))
		   (not (b1p (inst-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (not (b1p (INST-fetch-error? i)))
		   (not (b1p (INST-decode-error? i)))
		   (INST-writeback-p i))
	      (equal (dispatch-no-unit? MA) 0))
   :hints (("goal" :in-theory (enable INST-writeback-p dispatch-no-unit?
				      equal-b1p-converter
				      DQ-ready-no-unit?
				      INST-cntlv
				      INST-excpt-detected-p
				      INST-opcode
				      lift-b-ops)))))

; The instruction ROB invariants is preserved for instruction i,
; when it advances from (DQ 0) to complete-stg. 
(defthm complete-inst-robe-inv-step-INST-from-DQ0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (equal (INST-stg i) '(DQ 0))
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS))) 
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (complete-stg-p (INST-stg (step-INST I MT MA sigs))))
     (complete-inst-robe-inv (step-INST i MT MA sigs)
			     (nth-robe (INST-tag (step-INST i MT MA sigs))
				       (step-ROB MA sigs))))
  :hints (("goal" :in-theory (enable complete-inst-robe-inv lift-b-ops
				     equal-b1p-converter
				     INST-pc
				     INST-sync?
				     INST-WB-SREG?
				     INST-wb?
				     INST-rfeh?
				     INST-BU?
				     dispatch-inst?
				     dispatch-cntlv
				     step-robe)
		  :cases ((b1p (dispatch-inst? MA))))
	  ("subgoal 1" :cases ((b1p (inst-fetch-error? i))))
	  ("subgoal 1.2" :cases ((b1p (inst-decode-error? i))))))
)

; A help lemma to prove
;  not-complete-stg-step-inst-from-non-LSU-if-CDB-excpt-not-0
(defthm INST-data-accs-error-detected-p-step-INST-if-not-LSU
    (implies (and (inv MT MA)
		  (INST-p i) (INST-in i MT)
		  (or (IU-stg-p (INST-stg i))
		      (BU-stg-p (INST-stg i))
		      (MU-stg-p (INST-stg i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (not (INST-data-accs-error-detected-p
		   (step-inst i MT MA sigs))))
  :hints (("goal" :in-theory (e/d (INST-data-accs-error-detected-p
				     INST-load-accs-error-detected-p
				     INST-store-accs-error-detected-p
				     equal-b1p-converter
				     opcode-inst-type)
				  (INST-IU-IF-IU-STG-P
				   INST-BU-IF-BU-STG-P INST-MU-IF-MU-STG-P))
		  :use ((:instance INST-IU-IF-IU-STG-P)
			(:instance INST-BU-IF-BU-STG-P)
			(:instance INST-MU-IF-MU-STG-P)))))

; The instructions from IU, MU, and BU do not raise exceptions during
; the execution stage.  Thus, the excpt signal on the CDB is
; 0, when an instruction completes from one of them.
(defthm not-complete-stg-step-inst-from-non-LSU-if-CDB-excpt-not-0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (or (IU-stg-p (INST-stg i))
		      (MU-stg-p (INST-stg i))
		      (BU-stg-p (INST-stg i)))
		  (not (equal (CDB-excpt MA) 0)))
	     (not (complete-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :in-theory (enable CDB-excpt step-INST
				     lift-b-ops
				     execute-stg-p
				     issue-logic-def
				     step-INST-execute
				     step-INST-IU
				     step-INST-BU
				     step-INST-MU))))

; If an LSU instruction i completes this cycle,
; no new exception is detected in this cycle. 
(defthm INST-data-accs-error-detected-p-step-INST-if-LSU-complete
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (LSU-stg-p (INST-stg i))
		  (complete-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-data-accs-error-detected-p (step-INST i MT MA sigs))
		    (INST-data-accs-error-detected-p i)))
  :hints (("goal" :in-theory (e/d (INST-data-accs-error-detected-p
				     INST-load-accs-error-detected-p
				     INST-store-accs-error-detected-p
				     LSU-field-lemmas
				     equal-b1p-converter
				     LSU-stg-p)
				  (INST-load-OPCODE-3 INST-STORE-OPCODE-4
			       INST-load-OPCODE-6 INST-STORE-OPCODE-7))
		  :use ((:instance INST-STORE-OPCODE-7)
			(:instance INST-STORE-OPCODE-4)
			(:instance INST-load-OPCODE-3)
			(:instance INST-load-OPCODE-6)))))

(encapsulate nil
(local
(defthm CDB-excpt-INST-excpt-flags-help
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (LSU-stg-p (INST-stg i))
		  (complete-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (CDB-excpt MA)
		    (if (INST-data-accs-error-detected-p i) 6 0)))
  :hints (("goal" :in-theory (enable CDB-excpt INST-data-accs-error-detected-p
				     INST-EXCPT-FLAGS LSU-stg-p
				     CDB-FOR-LSU?)))))

; The exception field of the CDB contains the exception flags for the
; completing instruction.
(defthm CDB-excpt-INST-excpt-flags
    (implies (and (inv MT MA)
		  (execute-stg-p (INST-stg i))
		  (complete-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (equal (INST-excpt-flags (step-INST i MT MA sigs))
		    (CDB-excpt MA)))
    :hints (("goal" :in-theory (enable execute-stg-p INST-excpt-flags))))
)

; The LSB of the output-val signal from the BU is the branch outcome.
; See logcar-cdb-val-INST-branch-taken.
(defthm logcar-bu-output-val-inst-branch-taken
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (BU-stg-p (INST-stg i))
		  (or (b1p (BU-RS0-ISSUE-READY? (MA-BU MA)))
		      (b1p (BU-RS1-ISSUE-READY? (MA-BU MA))))
		  (equal (BU-output-tag (MA-BU MA)) (INST-tag i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (logcar (BU-output-val (MA-BU MA)))
		    (inst-branch-taken? i)))
  :hints (("goal" :in-theory (e/d (BU-output-val CDB-def
				     BU-RS-field-lemmas
				     INST-src-val3
				     lift-b-ops
				     INST-rc
				     BU-stg-p bv-eqv-iff-equal
				     equal-b1p-converter
				     bu-output-def
				     INST-BRANCH-TAKEN?
				     issue-logic-def)
				  ())
		  :use (:instance opcode-2-at-BU-stg-p))))

;  A output-dest signal from the IU outputs the Tomasulo's tag for the
;  completing integer instruction.
(defthm not-IU-output-tag-INST-tag-if-not-IU-stg-p
     (implies (and (inv MT MA)
		   (execute-stg-p (INST-stg i))
		   (not (IU-stg-p (INST-stg i)))
		   (or (b1p (IU-RS0-issue-ready? (MA-IU MA)))
		       (b1p (IU-RS1-issue-ready? (MA-IU MA))))
		   (INST-in i MT) (INST-p i)
		   (MAETT-p MT) (MA-state-p MA))
	      (not (equal (IU-output-tag (MA-IU MA)) (INST-tag I))))
  :hints (("goal" :in-theory (enable IU-output-tag
				     lift-b-ops
				     IU-RS0-ISSUE-READY?
				     IU-RS1-ISSUE-READY?
				     IU-RS-field-lemmas))))

;  A output-dest signal from the BU outputs the Tomasulo's tag for the
;  completing branch instruction.
(defthm not-BU-output-tag-INST-tag-if-not-BU-stg-p
     (implies (and (inv MT MA)
		   (execute-stg-p (INST-stg i))
		   (not (BU-stg-p (INST-stg i)))
		   (or (b1p (BU-RS0-issue-ready? (MA-BU MA)))
		       (b1p (BU-RS1-issue-ready? (MA-BU MA))))
		   (INST-in i MT) (INST-p i)
		   (MAETT-p MT) (MA-state-p MA))
	      (not (equal (BU-output-tag (MA-BU MA)) (INST-tag I))))
    :hints (("goal" :in-theory (enable BU-output-tag
				     lift-b-ops
				     BU-RS0-ISSUE-READY?
				     BU-RS1-ISSUE-READY?
				     BU-RS-field-lemmas))))

; The LSB of the val field of the common data bus is the branch
; outcome, if a branch instruction completes.
(defthm logcar-cdb-val-INST-branch-taken
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (b1p (INST-BU? i))
		  (b1p (CDB-ready-for? (INST-tag i) MA))
		  (execute-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (logcar (CDB-val MA)) (INST-branch-taken? i)))
  :hints (("goal" :in-theory (enable CDB-def lift-b-ops
				     execute-stg-p
				     LSU-field-lemmas
				     BU-RS-field-lemmas
				     IU-RS-field-lemmas
				     MU-field-lemmas))))
     

; An important lemma for the proof of 
;   complete-inst-robe-inv-step-INST
; The Instruction-ROB invariants are preserved for instruction i, if it
; advances from an execute-stg to a complete-stg.
;
; Some of the important lemmas for the proof for this lemmas are
; in section about Lemmas about CDB output.

; Matt K. mod: Proof no longer succeeds.  To fix it may require some reasonably
; deep understanding of this proof effort.
(skip-proofs
(defthm complete-inst-robe-inv-step-INST-from-execute
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (execute-stg-p (INST-stg i))
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (complete-stg-p (INST-stg (step-INST I MT MA sigs))))
     (complete-inst-robe-inv (step-INST i MT MA sigs)
			     (nth-robe (INST-tag i)
				       (step-ROB MA sigs))))
  :hints (("goal" :in-theory (enable complete-inst-robe-inv lift-b-ops
				     INST-excpt-detected-p
				     INST-PC
				     INST-exunit-relations
				     cdb-val-inst-dest-val
				     equal-b1p-converter
				     robe-receive-result? step-robe)
		  :cases ((b1p (CDB-ready-for? (INST-tag i) MA))))))
)

; If i is not at the head of the ROB, and some causes a jump,
; (MT-no-jmp-exintr-before i MT ...) is false.  Intuitively, 
; there is an jump instruction that precedes i.
(defthm MT-no-jmp-exintr-before-complete-if-context-sync
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (complete-stg-p (INST-stg i))
		  (not (equal (inst-of-tag (MT-rob-head MT) MT) i))
		  (or (b1p (commit-jmp? MA))
		      (b1p (leave-excpt? MA))
		      (b1p (enter-excpt? MA)))
		  (MAETT-p MT) (MA-state-p MA) (INST-p i))
	     (not (MT-no-jmp-exintr-before i MT MA sigs)))
  :hints (("goal" :use (:instance MT-jmp-exintr-before-if-inst-cause-jmp
				  (j i)
				  (i (inst-of-tag (MT-rob-head MT) MT))))))

; If flush-all? is on in the MA, and i is not a completed instruction, but
; it does not retire in this cycle, there must be another instruction that
; raises flush-all?.
(defthm MT-JMP-EXINTR-BEFORE-complete-INST-IF-FLUSH-ALL
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (complete-stg-p (INST-stg i))
		  (complete-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (b1p (flush-all? MA sigs))
		  (MAETT-p MT) (MA-state-p MA) (INST-p i) (MA-input-p sigs))
	     (not (MT-no-jmp-exintr-before i MT MA sigs)))
  :hints (("goal" :in-theory (enable flush-all? lift-b-ops)
		  :cases ((equal i (INST-OF-TAG (MT-ROB-HEAD MT) MT))))))

; Suppose i is a completed instruction at the head of the ROB. If commit-inst?
; is on in this cycle, i retires. 
(defthm not-complete-stg-step-inst-if-INST-rob-not-head
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (complete-stg-p (INST-stg i))
		  (b1p (commit-inst? MA))
		  (equal (INST-tag i) (MT-rob-head MT)))
	     (not (complete-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :in-theory (enable step-INST step-INST-complete lift-b-ops
				     INST-commit? bv-eqv-iff-equal))))

; The instruction-ROB invariants are preserved for instruction i,
; if i stays in a complete stage.
(defthm complete-inst-robe-inv-step-INST-from-complete
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (complete-stg-p (INST-stg i))
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (complete-stg-p (INST-stg (step-INST I MT MA sigs))))
     (complete-inst-robe-inv (step-INST i MT MA sigs)
			     (nth-robe (INST-tag i)
				       (step-ROB MA sigs))))
; Matt K. mod: Apparently heuristics have somehow changed.  The proof goes
; through by replacing the original hints with suitable proof-builder
; commands.  I created those :instructions in a very ad-hoc manner, based on
; the :hints.
#|
  :hints (("goal" :in-theory (enable complete-inst-robe-inv
				     INST-EXCPT-DETECTED-P
				     step-robe lift-b-ops
				     INST-pc)
		  :cases ((b1p (INST-fetch-error? i))))
	  ("subgoal 2" :cases ((b1p (INST-decode-error? i))))
	  ("subgoal 2.2" :cases ((b1p (INST-data-access-error? i)))))
|#
  :instructions ((:in-theory (enable complete-inst-robe-inv
                                     inst-excpt-detected-p
                                     step-robe lift-b-ops inst-pc))
                 (:bash ("goal" :cases ((b1p (inst-fetch-error? i)))))
                 (:casesplit (b1p (inst-decode-error? i)))
                 :bash
                 (:casesplit (b1p (inst-data-access-error? i)))
                 :bash :bash
                 (:casesplit (b1p (inst-decode-error? i)))
                 :bash
                 :bash (:casesplit (b1p (inst-data-access-error? i)))
                 :bash :bash)

  )

; An important lemma. 
; The instruction's ROB invariants are preserved for instruction i,
; if i will be in complete-stg in the next cycle.
; 
; The proof needs three important lemmas
;    complete-inst-robe-inv-step-INST-from-DQ0 
;    complete-inst-robe-inv-step-INST-from-execute
;    complete-inst-robe-inv-step-INST-from-complete
(defthm complete-inst-robe-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS))) 
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (complete-stg-p (INST-stg (step-INST I MT MA sigs))))
     (complete-inst-robe-inv (step-INST i MT MA sigs)
			     (nth-robe (INST-tag (step-INST i MT MA sigs))
				       (step-ROB MA sigs))))
  :hints (("goal" :use (:instance stages-reachable-to-complete)
		  :in-theory (disable nth-robe-step-rob))))

; An important lemma for the case where i's next stage is (complete).
; (complete) is reachable from a bunch of execution stages. 
; This lemma derives from complete-inst-robe-inv-step-INST.
(defthm complete-normal-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg (step-INST I MT MA sigs)) '(complete)))
	     (complete-normal-inst-inv (step-INST i MT MA sigs)
				       (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable complete-normal-inst-inv
				     NOT-INST-STORE-IF-COMPLETE
				     LSU-LOAD-IF-AT-LSU-RBUF-LCH)
		  :use ((:instance stages-reachable-to-complete-normal)
			(:instance not-complete-stg-p-step-INST-if-INST-LSU)))))

; Invariants are preserved when i moves from (LSU wbuf0 lch) to
; (complete WBUF0).
(defthm complete-wbuf0-inst-inv-step-INST-LSU-wbuf0-lch
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg i) '(LSU wbuf0 lch))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(complete WBUF0)))
	     (complete-wbuf0-inst-inv (step-INST i MT MA sigs)
				      (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable complete-wbuf0-inst-inv lift-b-ops
				     LSU-STORE-IF-AT-LSU-WBUF
				     update-wbuf0
				     step-LSU step-wbuf0))))

; Invariants are preserved when i moves from (LSU wbuf1 lch) to
; (complete WBUF0).
(defthm complete-wbuf0-inst-inv-step-INST-LSU-wbuf1-lch
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg i) '(LSU wbuf1 lch))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(complete WBUF0)))
	     (complete-wbuf0-inst-inv (step-INST i MT MA sigs)
				      (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable complete-wbuf0-inst-inv lift-b-ops
				     LSU-STORE-IF-AT-LSU-WBUF
				     wbuf1-output update-wbuf0
				     step-LSU step-wbuf0))))

; Invariants are preserved when i moves from (complete wbuf0) to
; (complete WBUF0).
(defthm complete-wbuf0-inst-inv-step-INST-complete-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg i) '(complete wbuf0))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(complete WBUF0)))
	     (complete-wbuf0-inst-inv (step-INST i MT MA sigs)
				      (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable complete-wbuf0-inst-inv lift-b-ops
				     LSU-STORE-IF-AT-LSU-WBUF
				     step-LSU step-wbuf0
				     update-wbuf0
				     INST-COMMIT?))))

; Invariants are preserved when i moves from (complete wbuf1) to
; (complete WBUF0).
(defthm complete-wbuf0-inst-inv-step-INST-complete-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg i) '(complete wbuf1))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(complete WBUF0)))
	     (complete-wbuf0-inst-inv (step-INST i MT MA sigs)
				      (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable complete-wbuf0-inst-inv lift-b-ops
				     LSU-STORE-IF-AT-LSU-WBUF
				     step-LSU step-wbuf0
				     wbuf1-output 
				     INST-COMMIT?))))

; A important lemma for the case where i's next stage is (complete WBUF0).
; (complete WBUF0) is reachable from (complete wbuf1), (complete wbuf0), 
; (LSU wbuf1 lch), and (LSU wbuf0 lch).
; 
; The proof is divided into :
;   complete-wbuf0-inst-inv-step-INST-LSU-wbuf0-lch
;   complete-wbuf0-inst-inv-step-INST-LSU-wbuf1-lch
;   complete-wbuf0-inst-inv-step-INST-complete-wbuf0
;   complete-wbuf0-inst-inv-step-INST-complete-wbuf1
;
; It also uses complete-inst-robe-inv-step-INST.
(defthm complete-wbuf0-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(complete WBUF0)))
	     (complete-wbuf0-inst-inv (step-INST i MT MA sigs)
				      (MA-step MA sigs)))
  :hints (("goal" :use (:instance stages-reachable-to-complete-wbuf0))))

; The case where Instruction i goes from '(LSU WBUF1 lch)
; to '(complete WBUF1)
(defthm complete-wbuf1-inst-inv-step-INST-LSU-wbuf1-lch
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg i) '(LSU WBUF1 lch))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(complete WBUF1)))
	     (complete-wbuf1-inst-inv (step-INST i MT MA sigs)
				      (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable complete-wbuf1-inst-inv lift-b-ops
				     LSU-STORE-IF-AT-LSU-WBUF
				     step-LSU step-wbuf1
				     wbuf1-output update-wbuf1
				     INST-COMMIT?))))

; A case where Instruction goes from '(complete WBUF1) to '(complete WBUF1).
(defthm complete-wbuf1-inst-inv-step-INST-complete-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg i) '(complete WBUF1))
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(complete WBUF1)))
	     (complete-wbuf1-inst-inv (step-INST i MT MA sigs)
				      (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable complete-wbuf1-inst-inv lift-b-ops
				     LSU-STORE-IF-AT-LSU-WBUF
				     step-LSU step-wbuf1
				     wbuf1-output update-wbuf1
				     INST-COMMIT?))))

; A important lemma for the case where i's next stage is (complete WBUF1)
; The instruction invariants are preserved if the next stage is
; (complete WBUF1)
; The stage (complete WBUF1) is reachable from
; '(LSU WBUF1 lch) and '(complete WBUF1).
;
; The proof is divided into two parts:
;   complete-wbuf1-inst-inv-step-INST-LSU-wbuf1-lch
;   complete-wbuf1-inst-inv-step-INST-complete-wbuf1
; It also uses complete-inst-robe-inv-step-INST.
(defthm complete-wbuf1-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (equal (INST-stg (step-INST I MT MA sigs))
			 '(complete WBUF1)))
	     (complete-wbuf1-inst-inv (step-INST i MT MA sigs)
				      (MA-step MA sigs)))
  :hints (("goal" :use (:instance stages-reachable-to-complete-wbuf1))))

; A landmark lemma complete-inst-inv-step-INST. 
; The instruction invariants are preserved for instruction i, if
; i is in complete-stg in the next cycle.
(defthm complete-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (MT-no-jmp-exintr-before i MT MA sigs)
		  (NOT (B1P (INST-EXINTR-NOW? I MA SIGS))) 
		  (complete-stg-p (INST-stg (step-INST I MT MA sigs))))
	     (complete-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (e/d (complete-inst-inv complete-inst-inv
						     complete-stg-p)
				  (nth-robe-step-rob)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;   Proof of commit-inst-inv
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; When an instruction at stage (complete wbuf0) commits, flush-all? is not
; asserted unless an exception is raised for the committed instruction.
; Note: This proof is slightly difficult.  One critical case is
; that the committed instruction is speculatively executed or self-modified.
; In that case, we can't prove the instruction is not a branch instruction,
; which may assert flush-all?.
(encapsulate nil
(local
(defthm not-flush-all-if-not-enter-excpt-help
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (or (equal (INST-stg i) '(complete wbuf0))
		      (equal (INST-stg i) '(complete wbuf1)))
		  (b1p (INST-commit? i MA))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (enter-excpt? MA)))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (b1p (flush-all? MA sigs))))
  :hints (("goal" :in-theory (enable flush-all? lift-b-ops
				     commit-jmp? INST-commit?
				     leave-excpt? ex-intr?)))))

(defthm not-flush-all-if-commit-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (or (equal (INST-stg i) '(complete wbuf0))
		      (equal (INST-stg i) '(complete wbuf1)))
		  (b1p (INST-commit? i MA))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (not (b1p (enter-excpt? MA)))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (b1p (flush-all? MA sigs))))
  :hints (("goal" :cases ((b1p (inst-specultv? i)) (b1p (INST-modified? i)))))
  :rule-classes
  ((:rewrite :corollary
     (implies (and (inv MT MA)
		   (INST-in i MT) (INST-p i)
		   (or (equal (INST-stg i) '(complete wbuf0))
		       (equal (INST-stg i) '(complete wbuf1)))
		   (b1p (flush-all? MA sigs))
		   (not (MT-CMI-p (MT-step MT MA sigs)))
		   (not (b1p (enter-excpt? MA)))
		   (MAETT-p MT) (MA-state-p MA))
	      (equal (INST-commit? i MA) 0))
     :hints (("goal" :in-theory (enable equal-b1p-converter))))))
)

(in-theory (disable not-flush-all-if-commit-INST-in))

(defthm commit-wbuf0-inst-inv-step-INST-complete-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (equal (INST-stg i) '(complete wbuf0))
		  (equal (INST-stg (step-INST I MT MA sigs)) '(commit wbuf0)))
	     (commit-wbuf0-inst-inv (step-INST i MT MA sigs)
				    (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable commit-wbuf0-inst-inv lift-b-ops
				     step-LSU step-wbuf0
				     not-flush-all-if-commit-INST-in
				     LSU-STORE-IF-AT-LSU-WBUF
				     update-wbuf0)
		  :cases ((b1p (inst-specultv? i))
			  (b1p (INST-modified? i))))
	  (when-found (EQUAL (INST-tag I) (MT-ROB-HEAD MT))
		      (:in-theory (enable INST-commit? lift-b-ops)))
	  (when-found (b1p (commit-inst? MA))
		      (:in-theory (enable INST-commit? lift-b-ops)))))

(defthm commit-wbuf0-inst-inv-step-INST-complete-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (equal (INST-stg i) '(complete wbuf1))
		  (equal (INST-stg (step-INST I MT MA sigs)) '(commit wbuf0)))
	     (commit-wbuf0-inst-inv (step-INST i MT MA sigs)
				    (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable commit-wbuf0-inst-inv lift-b-ops
				     step-LSU step-wbuf0
				     not-flush-all-if-commit-INST-in
				     LSU-STORE-IF-AT-LSU-WBUF
				     wbuf1-output)
		  :cases ((b1p (inst-specultv? i))
			  (b1p (INST-modified? i))))
	  (when-found (EQUAL (INST-tag I) (MT-ROB-HEAD MT))
		      (:in-theory (enable INST-commit? lift-b-ops)))
	  (when-found (b1p (commit-inst? MA))
		      (:in-theory (enable INST-commit? lift-b-ops)))))

(defthm commit-wbuf0-inst-inv-step-INST-commit-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (equal (INST-stg i) '(commit wbuf0))
		  (equal (INST-stg (step-INST I MT MA sigs)) '(commit wbuf0)))
	     (commit-wbuf0-inst-inv (step-INST i MT MA sigs)
				    (MA-step MA sigs)))
    :hints (("goal" :in-theory (enable commit-wbuf0-inst-inv lift-b-ops
				     not-flush-all-if-commit-INST-in
				     step-LSU step-wbuf0
				     update-wbuf0
				     LSU-STORE-IF-AT-LSU-WBUF)
		    :cases ((b1p (inst-specultv? i))
			    (b1p (INST-modified? i))))
	  (when-found (EQUAL (INST-tag I) (MT-ROB-HEAD MT))
		      (:in-theory (enable INST-commit? lift-b-ops)))
	  (when-found (b1p (commit-inst? MA))
		      (:in-theory (enable INST-commit? lift-b-ops)))))

(defthm commit-wbuf0-inst-inv-step-INST-commit-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (equal (INST-stg i) '(commit wbuf1))
		  (equal (INST-stg (step-INST I MT MA sigs)) '(commit wbuf0)))
	     (commit-wbuf0-inst-inv (step-INST i MT MA sigs)
				    (MA-step MA sigs)))
      :hints (("goal" :in-theory (enable commit-wbuf0-inst-inv lift-b-ops
				     not-flush-all-if-commit-INST-in
				     step-LSU step-wbuf0
				     wbuf1-output
				     LSU-STORE-IF-AT-LSU-WBUF))
	  (when-found (EQUAL (INST-tag I) (MT-ROB-HEAD MT))
		      (:in-theory (enable INST-commit? lift-b-ops)))
	  (when-found (b1p (commit-inst? MA))
		      (:in-theory (enable INST-commit? lift-b-ops)))))

(defthm commit-wbuf0-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (equal (INST-stg (step-INST I MT MA sigs)) '(commit wbuf0)))
	     (commit-wbuf0-inst-inv (step-INST i MT MA sigs)
				    (MA-step MA sigs)))
  :hints (("goal" :use (:instance stages-reachable-to-commit-wbuf0)
		  :in-theory (enable lift-b-ops))))

(defthm commit-wbuf1-inst-inv-step-INST-complete-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (equal (INST-stg i) '(complete wbuf1))
		  (equal (INST-stg (step-INST I MT MA sigs)) '(commit wbuf1)))
	     (commit-wbuf1-inst-inv (step-INST i MT MA sigs)
				    (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable commit-wbuf1-inst-inv lift-b-ops
				     not-flush-all-if-commit-INST-in
				     step-LSU step-wbuf1
				     update-wbuf1
				     LSU-STORE-IF-AT-LSU-WBUF)
		  :cases ((b1p (inst-specultv? i))
			    (b1p (INST-modified? i))))
	  (when-found (EQUAL (INST-tag I) (MT-ROB-HEAD MT))
	      (:in-theory (enable INST-commit? lift-b-ops)))
	  (when-found (b1p (commit-inst? MA))
		      (:in-theory (enable INST-commit? lift-b-ops)))))

(defthm commit-wbuf1-inst-inv-step-INST-commit-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (equal (INST-stg i) '(commit wbuf1))
		  (equal (INST-stg (step-INST I MT MA sigs)) '(commit wbuf1)))
	     (commit-wbuf1-inst-inv (step-INST i MT MA sigs)
				    (MA-step MA sigs)))
    :hints (("goal" :in-theory (enable commit-wbuf1-inst-inv lift-b-ops
				     not-flush-all-if-commit-INST-in
				     step-LSU step-wbuf1
				     update-wbuf1
				     LSU-STORE-IF-AT-LSU-WBUF))
	  (when-found (EQUAL (INST-tag I) (MT-ROB-HEAD MT))
		      (:in-theory (enable INST-commit? lift-b-ops)))
	  (when-found (b1p (commit-inst? MA))
		      (:in-theory (enable INST-commit? lift-b-ops)))))

(defthm commit-wbuf1-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (equal (INST-stg (step-INST I MT MA sigs)) '(commit wbuf1)))
	     (commit-wbuf1-inst-inv (step-INST i MT MA sigs)
				    (MA-step MA sigs)))
  :hints (("goal" :use (:instance stages-reachable-to-commit-wbuf1)
		  :in-theory (enable lift-b-ops))))

; A landmark lemma commit-inst-inv-step-INST 
(defthm commit-inst-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (INST-inv i MA)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (commit-stg-p (INST-stg (step-INST I MT MA sigs))))
	     (commit-inst-inv (step-INST i MT MA sigs) (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable commit-inst-inv commit-stg-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;   End of the proof of commit-inst-inv
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The final landmark lemma.
; The instruction invariants are preserved for instruction i, regardless
; of the stage of i, if external interrupt does not interrupt i.
(defthm INST-inv-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p i)
		  (INST-in i MT)
		  (not (b1p (INST-exintr-now? i MA sigs)))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (MT-no-jmp-exintr-before i MT MA sigs))
	     (INST-inv (step-INST i MT MA sigs)
		       (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable INST-inv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  End of the proof of INST-inv-step-INST
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  Proof of INST-inv-exintr-INST
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A landmark lemma.
; The instruction invariants are true for (exintr-INST MT init smc).
(defthm INST-inv-exintr-INST
    (implies (and (MAETT-p MT)
		  (MA-state-p MA)
		  (ISA-state-p INIT)
		  (MA-input-p sigs))
	     (INST-inv (exintr-INST MT init smc) (MA-step MA sigs)))
  :hints (("Goal" :in-theory (enable exintr-INST inst-inv-def))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; End of inst-inv
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Proof of MT-INST-inv
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Induction on the list of instructions.
(defthm trace-INST-inv-lemma
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-listp trace)
		  (MA-input-p sigs)
		  (MT-no-jmp-exintr-before-trace trace MT MA sigs)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (subtrace-p trace MT)
		  (trace-INST-inv trace MA))
     (trace-INST-inv (step-trace trace MT MA sigs
				 (ISA-before trace MT)
				 (specultv-before? trace MT)
				 (modified-inst-before? trace MT))
		     (MA-step MA sigs)))
  :hints ((when-found (FETCHED-INST MT (MT-FINAL-ISA MT)
				    (MT-SPECULTV? MT))
		      (:cases ((b1p (MT-SPECULTV? MT)))))))

(encapsulate nil
(local
(defthm MT-INST-inv-preserved-help
    (implies (and (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (inv MT MA)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (MT-INST-inv MT MA))
	     (MT-INST-inv (MT-step MT ma sigs) (MA-step ma sigs)))
  :hints (("goal" :use (:instance trace-INST-inv-lemma
				  (trace (MT-trace MT)))
		  :in-theory (enable MT-INST-inv
				     MT-step)))))
; MT-INST-inv is preserved. 
(defthm MT-INST-inv-preserved
    (implies (and (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (inv MT MA))
	     (MT-INST-inv (MT-step MT ma sigs)
			  (MA-step ma sigs))))
) ; encapsulate
