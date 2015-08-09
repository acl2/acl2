(in-package "ACL2")

(include-book "utils")
(include-book "basic-def")
(include-book "model")

(deflabel begin-table-def)

; The valid pipeline stages in this machine are latch1, latch2 and
; retire.
(defun stage-p (stg)
  (declare (xargs :guard t))
  (or (equal stg 'latch1) (equal stg 'latch2) (equal stg 'retire)))

(in-theory (disable proj flushed? stage-p))

; The definition of MAETT entry which represents an instruction.
; Only a few fields are required for this example.
;  Field	Description
;  stg		The current stage of the represented instruction.
;  pre-ISA	The ISA state before the execution of this instruction.
;  post-ISA	The ISA state after the execution of this instruction.
(defstructure INST
  (stg  (:assert (stage-p stg) :rewrite))
  (pre-ISA (:assert (ISA-state-p pre-ISA) :rewrite))
  (post-ISA (:assert (ISA-state-p post-ISA) :rewrite))
  (:options :guards))

(deflist INST-listp (l)
  (declare (xargs :guard t))
  INST-p)

; Definition of MAETT.  It stores the initial ISA state, init-ISA, and
; a list of MAETT entries, trace.  Each entry of trace represents
; a fetched and executed instruction.   Trace stores the entries in
; the order that the ISA executes the represented instructions.  ISA
; state init-ISA is the ISA state before executing the first
; instruction in trace.
(defstructure MAETT
  (init-ISA (:assert (ISA-state-p init-ISA) :rewrite))
  (trace (:assert (INST-listp trace) :rewrite))
  (:options :guards (:conc-name MT-)))

(deflabel begin-MAETT-def)

; Function init-MT constructs the initial  MAETT table for an
; flushed initial MA state.  Since no instructions are fetched yet,
; trace field contains an empty list.
(defun init-MT (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (MAETT (proj MA) nil))

; The MAETT entry representing a newly fetched instruction.  Argument
; ISA is the pre-ISA state of the newly fetched instruction.  In other
; words, it is the correct ISA state before executing the newly
; fetched instruction.
(defun new-inst (ISA)
  (declare (xargs :guard (ISA-state-p ISA)))
  (INST 'latch1
	ISA
	(ISA-step ISA)))

(defun step-latch1-INST (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))
  (if (b1p (stall-cond? MA))
      i
      (update-INST i :stg 'latch2)))

(defun step-latch2-INST (i)
  (declare (xargs :guard (INST-p i)))
  (update-INST i :stg 'retire))

; Function step-INST updates the MAETT entry to reflect the change of
; the state of the represented instruction.  In this example, we only
; have to update the stage field as the instruction advances through the
; pipeline.
(defun step-INST (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))
  (cond ((equal (INST-stg i) 'latch1)
	 (step-latch1-INST i MA))
	((equal (INST-stg i) 'latch2)
	 (step-latch2-INST i))
	(t i)))

; Function step-trace updates the field, trace, of a MAETT.  If a new
; instruction is fetched, an entry corresponding to the new
; instruction is added at the end of the trace.  The rest of the
; entries are updated with function step-INST.
(defun step-trace (trace MA sig last-ISA)
  (declare (xargs :guard (and (INST-listp trace) (MA-state-p MA)
			      (MA-sig-p sig)
			      (ISA-state-p last-ISA))))
  (if (endp trace)
      (if (b1p (fetch-inst? MA sig))
	  (list (new-inst last-ISA))
	  nil)
      (cons (step-INST (car trace) MA)
	    (step-trace (cdr trace) MA sig (INST-post-ISA (car trace))))))

; Function to update an MAETT.  MT-step takes arguments MA and MT,
; which are the current MA state and the corresponding MAETT, and it
; returns the updated MAETT.  The new MAETT represents the next MA
; state (MA-step MA sig).
(defun MT-step (MT MA sig)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA)
			      (MA-sig-p sig))))
  (MAETT (MT-init-ISA MT)
	 (step-trace (MT-trace MT) MA sig (MT-init-ISA MT))))

(deflabel end-MAETT-def)


; Function to iteratively update a MAETT, MT, for n cycles.  Argument
; MA and MT are the initial MA state and the corresponding MAETT.
(defun MT-stepn (MT MA sig-list n)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA)
			      (MA-sig-listp sig-list)
			      (integerp n) (<= 0 n))
		  :verify-guards nil))
  (if (zp n) MT
      (if (endp sig-list) MT
	  (MT-stepn (MT-step MT MA (car sig-list))
		    (MA-step MA (car sig-list))
		    (cdr sig-list)
		    (1- n)))))

(deftheory MAETT-def
    (non-rec-functions
     (set-difference-theories (function-theory 'end-MAETT-def)
			      (function-theory 'begin-MAETT-def))
     world))

(in-theory (disable MAETT-def))

;; Type proofs
(defthm ISA-state-p-proj
    (implies (MA-state-p MA) (ISA-state-p (proj MA)))
  :hints (("Goal" :in-theory (enable proj))))

(defthm MAETT-p-init-MT
    (implies (MA-state-p MA) (MAETT-p (init-MT MA)))
  :hints (("Goal" :in-theory (enable init-MT))))

(defthm inst-p-new-inst
    (implies (ISA-state-p ISA) (INST-p (new-inst ISA)))
  :hints (("Goal" :in-theory (enable new-inst))))

(defthm INST-p-step-INST
    (implies (INST-p i) (INST-p (step-INST i MA)))
  :Hints (("Goal" :in-theory (enable step-inst step-latch1-inst
				     step-latch2-inst))))

(defthm INST-listp-step-trace
    (implies (and (INST-listp trace) (ISA-state-p ISA))
	     (INST-listp (step-trace trace MA sig ISA))))

(defthm MAETT-p-MT-step
    (implies (and (MAETT-p MT) (MA-state-p MA) (MA-sig-p sig))
	     (MAETT-p (MT-step MT MA sig)))
  :hints (("Goal" :in-theory (enable MT-step))))

(verify-guards MT-step)

(defthm MAETT-p-MT-stepn
    (implies (and (MAETT-p MT) (MA-state-p MA) (MA-sig-listp sig-list)
		  (<= n (len sig-list)))
	     (MAETT-p (MT-stepn MT MA sig-list n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Definition of Instruction Attributes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Various attributes of an instruction are defined as functions which
; take the MAETT entry representing the instruction.  For instance,
; the opcode of an instruction represented by MAETT entry I is defined
; as (INST-op I).  In the following definitions, we define many
; attributes such as instruction word, operand registers, source
; values and result value.
(deflabel begin-INST-attrb)
(defun INST-word (i)
  (declare (xargs :guard (INST-p i)))
  (read-mem (ISA-pc (INST-pre-ISA i)) (ISA-mem (INST-pre-ISA i))))

(defun INST-op (i)
  (declare (xargs :guard (INST-p i)))
  (op-field (INST-word i)))

(defun INST-rc (i)
  (declare (xargs :guard (INST-p i)))
  (rc-field (INST-word i)))

(defun INST-ra (i)
  (declare (xargs :guard (INST-p i)))
  (ra-field (INST-word i)))

(defun INST-rb (i)
  (declare (xargs :guard (INST-p i)))
  (rb-field (INST-word i)))

(defun INST-ra-val (i)
  (declare (xargs :guard (INST-p i)))
  (read-reg (INST-ra i) (ISA-regs (INST-pre-ISA i))))

(defun INST-rb-val (i)
  (declare (xargs :guard (INST-p i)))
  (read-reg (INST-rb i) (ISA-regs (INST-pre-ISA i))))

(defun INST-result (i)
  (declare (xargs :guard (INST-p i)))
  (ALU-output (INST-op i) (INST-ra-val i) (INST-rb-val i)))

(deflabel end-INST-attrb)
(deftheory INST-attrb
    (set-difference-theories (function-theory 'end-INST-attrb)
			     (function-theory 'begin-INST-attrb)))
(in-theory (disable INST-attrb))

(defthm word-p-INST-word
    (implies (INST-p i) (word-p (INST-word i)))
  :hints (("Goal" :in-theory (enable INST-word))))

(defthm opcd-p-INST-op
    (implies (INST-p i) (opcd-p (INST-op i)))
  :hints (("Goal" :in-theory (enable INST-op))))

(defthm rname-p-INST-rc
    (implies (INST-p i) (rname-p (INST-rc i)))
  :hints (("Goal" :in-theory (enable INST-rc))))

(defthm rname-p-INST-ra
    (implies (INST-p i) (rname-p (INST-ra i)))
  :hints (("Goal" :in-theory (enable INST-ra))))

(defthm rname-p-INST-rb
    (implies (INST-p i) (rname-p (INST-rb i)))
  :hints (("Goal" :in-theory (enable INST-rb))))

(defthm word-p-INST-ra-val
    (implies (INST-p i) (word-p (INST-ra-val i)))
  :hints (("Goal" :in-theory (enable INST-ra-val))))

(defthm word-p-INST-rb-val
    (implies (INST-p i) (word-p (INST-rb-val i)))
  :hints (("Goal" :in-theory (enable INST-rb-val))))

(defthm word-p-INST-result
    (implies (INST-p i) (word-p (INST-result i)))
  :hints (("Goal" :in-theory (enable INST-result ALU-output))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Defintion of INST-at
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; INST-at returns the MAETT entry whose represented instruction is at
; a particular stage.
;
; (INST-at stg MT) is nil if there is no instruction at stage stg in
; MAETT MT.  If there is one, it returns the corresponding MAETT entry
; representing the instruction.

(defun trace-inst-at (stg trace)
  (declare (xargs :guard (and (stage-p stg) (INST-listp trace))))
  (if (endp trace) nil
      (if (equal (INST-stg (car trace)) stg)
	  (car trace)
	  (trace-inst-at stg (cdr trace)))))

(defun INST-at (stg MT)
  (declare (xargs :guard (and (stage-p stg) (MAETT-p MT))))
  (trace-inst-at stg (MT-trace MT)))

(in-theory (disable INST-at))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Definition of invariant conditions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Invariant conditions required for the proof of correctness diagram
; are defined here.  We needed seven invariant conditions.
;
;       (pc-match-p MT MA)
;          The program counter holds the correct value.
;       (regs-match-p MT MA)
;          The register file contains correct values.
;       (mem-match-p MT MA)
;          The memory is in the correct state.
;       (ISA-chain-p MT)
;          MAETT records correct ISA execution of instructions.
;       (MT-inst-invariant MT MA)
;          Each instruction in the pipeline satisfies "instruction invariant".
;       (MT-contains-all-insts MT MA)
;          MT contains all instructions currently in the pipeline of MA.
;       (MT-in-order-p MT)))
;          MA pipeline executes instructions in program order.
(deflabel begin-invariant-def)

; Predicate pc-match-p checks whether the program counter in the MA
; holds the correct value.  The reader may ask what the correct value is.
; The answer is that the program counter should point to the
; instruction to be fetched in the next cycle.  MT-pc calculates
; it from a MAETT, by first looking for the most recently fetched
; instruction I, and find the program counter value of (INST-post-ISA I).
; (INST-post-ISA I) is the ISA state after the execution of I,
; and before fetching the next instruction.
(defun trace-pc (trace ISA)
  (declare (xargs :guard (and (INST-listp trace) (ISA-state-p ISA))))
  (if (endp trace)
      (ISA-pc ISA)
      (trace-pc (cdr trace) (INST-post-ISA (car trace)))))

(defun MT-pc (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-pc (MT-trace MT) (MT-init-ISA MT)))

(defun pc-match-p (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (equal (MT-pc MT) (MA-pc MA)))

; Predicate regs-match-p checks whether the register file contains the
; correct values.  MT-regs calculate the correct register file
; state from a MAETT.  It first looks for the earliest non-retired
; instruction I, and returns the register file of (INST-pre-ISA I).
; The register is updated when an instruction retires.  So the
; register file in the MA holds the results of all retired
; instruction, but none of the partially executed instructions,
; including I.
(defun trace-regs (trace ISA)
  (declare (xargs :guard (and (INST-listp trace) (ISA-state-p ISA))))
  (if (endp trace)
      (ISA-regs ISA)
      (if (not (equal (INST-stg (car trace)) 'retire))
	  (ISA-regs ISA)
	  (trace-regs (cdr trace) (INST-post-ISA (car trace))))))

(defun MT-regs (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-regs (MT-trace MT) (MT-init-ISA MT)))

(defun regs-match-p (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (equal (MT-regs MT) (MA-regs MA)))

; Memory state does not change in this model.  The memory of the MA state
; should be equal to that of the initial ISA state.
(defun mem-match-p (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (equal (MA-mem MA) (ISA-mem (MT-init-ISA MT))))

; MAETT represents the sequence of instructions as a list, where each
; element of the list represents an instruction.  Each entry
; has pre-ISA and post-ISA fields, which store the ISA state before
; and after executing the represented instruction.  This ISA
; states form a sort of chain.  Suppose MT has a list of instruction
; entries (I_0 I_1 I_2 ...).  I_0 represents the first instruction to be
; executed, I_1 represents the second and so on.  Then following
; equations hold:
; (ISA-step (INST-pre-ISA I_0)) = (INST-post-ISA I_0)
; (INST-post-ISA I_0) = (INST-pre-ISA I_1)
; (ISA-step (INST-pre-ISA I_1)) = (INST-post-ISA I_1)
; (INST-post-ISA I_1) = (INST-pre-ISA I_2)
;   ....
; This relations are checked by the predicate ISA-chain-p.  In other
; words, ISA-chain-p checks whether the correct sequence of ISA states
; are stored in the MAETT.  Following picture may help the reader to
; understand the relations of pre-ISA and post-ISA.
;
;   (INST-pre-ISA i_0)
;         |  execution of i_0
;         v
;   (INST-post-ISA i_0) = (INST-pre-ISA i_1)
;         |  execution of i_1
;         v
;   (INST-post-ISA i_1) = (INST-pre-ISA i_2)
;         ...
(defun ISA-chain-trace-p (trace ISA)
  (declare (xargs :guard (and (INST-listp trace) (ISA-state-p ISA))))
  (if (endp trace)
      T
      (and (equal (INST-pre-ISA (car trace)) ISA)
	   (equal (ISA-step ISA)
		  (INST-post-ISA (car trace)))
	   (ISA-chain-trace-p (cdr trace) (ISA-step ISA)))))

(defun ISA-chain-p (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (ISA-chain-trace-p (MT-trace MT) (MT-init-ISA MT)))

; Each instruction should satisfy some invariant conditions at each
; stage of the pipeline.  Mostly, these conditions are about the
; intermediate values stored in the pipeline latches.
;
; For instance, field latch1-op of latch latch1 in the MA state hould
; hold the operand of instruction at stage latch1.  If you see the
; definition of inst-latch1-inv, you can find the corresponding
; equation as the second conjunct of the body of the definition.
;
; Predicate inst-invariant checks whether instruction entry i and the
; corresponding MA state satisfies these stage-dependent invariant.
; MT-inst-invariant checks all instructions in the MAETT satisfies
; inst-invariant.

; The condition that instruction should satisfy at state latch1.
(defun inst-latch1-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))
  (and (b1p (latch1-valid? (MA-latch1 MA)))
       (equal (latch1-op (MA-latch1 MA)) (INST-op i))
       (equal (latch1-rc (MA-latch1 MA)) (INST-rc i))
       (equal (latch1-ra (MA-latch1 MA)) (INST-ra i))
       (equal (latch1-rb (MA-latch1 MA)) (INST-rb i))))

; The condition that instruction should satisfy at state latch2.
(defun inst-latch2-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))
  (and (b1p (latch2-valid? (MA-latch2 MA)))
       (equal (latch2-op (MA-latch2 MA))     (INST-op i))
       (equal (latch2-rc (MA-latch2 MA))     (INST-rc i))
       (equal (latch2-ra-val (MA-latch2 MA)) (INST-ra-val i))
       (equal (latch2-rb-val (MA-latch2 MA)) (INST-rb-val i))))

; Instruction invariant that i should satisfy regardless of its stage.
(defun inst-invariant (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))
  (cond ((equal (INST-stg i) 'latch1)
	 (inst-latch1-inv i MA))
	((equal (INST-stg i) 'latch2)
	 (inst-latch2-inv i MA))
	(t t)))

(defun trace-inst-invariant (trace MA)
  (declare (xargs :guard (and (INST-listp trace) (MA-state-p MA))))
  (if (endp trace) t
      (and (inst-invariant (car trace) MA)
	   (trace-inst-invariant (cdr trace) MA))))

(defun MT-inst-invariant (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (trace-inst-invariant (MT-trace MT) MA))

; If field latch1-valid? of an MA state is on, the corresponding MAETT
; contains an entry representing the instruction at latch1.  Similarly
; for latch2.
(defun MT-contains-all-insts (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (and (implies (b1p (latch1-valid? (MA-latch1 MA)))
		(inst-at 'latch1 MT))
       (implies (b1p (latch2-valid? (MA-latch2 MA)))
		(inst-at 'latch2 MT))))

; This pipelined machine executes instructions in program order.
; The instruction at latch1 is younger than the instruction at latch2,
; and the instruction at latch2 is younger than any retired
; instructions.  This fact is checked by MT-in-order-p, assuming that
; instructions are recorded in program order in a MAETT.
(defun trace-in-order-p (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace)
      t
      (if (equal (INST-stg (car trace)) 'latch1)
	  (endp (cdr trace))
	  (if (equal (INST-stg (car trace)) 'latch2)
	      (and (not (trace-inst-at 'latch2 (cdr trace)))
		   (not (trace-inst-at 'retire (cdr trace)))
		   (trace-in-order-p (cdr trace)))
	      (trace-in-order-p (cdr trace))))))

(defun MT-in-order-p (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-in-order-p (MT-trace MT)))

; The definition of invariant.
(defun invariant (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (and (pc-match-p MT MA)
       (regs-match-p MT MA)
       (mem-match-p MT MA)
       (ISA-chain-p MT)
       (MT-inst-invariant MT MA)
       (MT-contains-all-insts MT MA)
       (MT-in-order-p MT)))

(deflabel end-invariant-def)
(deftheory invariant-def
    (set-difference-theories (function-theory 'end-invariant-def)
			     (function-theory 'begin-invariant-def)))

(deftheory non-rec-invariant-def
    (non-rec-functions (theory 'invariant-def) world))

(in-theory (disable non-rec-invariant-def))

