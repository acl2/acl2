(in-package "ACL2")

(include-book "basic-def")

(deflabel begin-model)

; Basic Pipeline Design
; Our example machine is very simple.  It consists of a program counter,
; a register file, the memory, pipeline latches latch1 and latch2.
; The programmer visible components are the program counter, the register
; file and the memory.  It can execute two types of instructions, ADD
; and SUB.  The format of an instruction is as shown here:
;           --------------------------------
;          | op    |  RC   |  RA   |   RB  |
;           --------------------------------
;           15    12 11    8 7     4 3     0
;
; where RC, RA and RB are operand register specifiers.  There are only
; two valid opcodes 0 (ADD) and 1 (SUB).  An instruction without a
; valid opcode is considered as a NOP.  The ADD instruction reads
; registers specified by RA and RB, adds the values and writes the
; result back into the register specified by RC.  The SUB subtracts RB
; from RA.  Every machine cycle the program counter is incremented by
; 1.  No exceptions and no interrupts occur.  There is one external
; input to the machine.  If this input signal is on, the machine may
; fetch a new instruction from the memory.  Pipeline flushing can be
; done by running the machine with 0's as its inputs.
;
; We define this machine at two levels: instruction-set architecture
; and micro-architecture.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; ISA Definition
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Description of ISA
; The ISA state consists of only programmer visible states, that is,
; the program counter, register file and the memory.
; ISA behavior is specified by ISA-step.  Depending on the operand,
; it executes ADD or SUB operation.

; Definition of the ISA state.
;
; Note: For the detail of the definition with defstructure, please
; refer to the public ACL2 book data-structures/structures.lisp.
; Briefly speaking, an expression (ISA-state PC REGS MEM) returns
; an ISA state whose program counter, register file and memory are PC,
; REGS and MEM, respectively.  The pc value of an ISA state, ISA, can
; be obtained by (ISA-pc ISA).
(defstructure ISA-state
  (pc   (:assert (addr-p pc)   :rewrite))
  (regs (:assert (regs-p regs) :rewrite))
  (mem  (:assert (mem-p mem)   :rewrite))
  (:options :guards  (:conc-name ISA-)))

(deflabel begin-ISA-def)

; Definition of the effect of an ADD instruction.
(defun ISA-add (rc ra rb ISA)
  (declare (xargs :guard (and (rname-p rc) (rname-p ra) (rname-p rb)
			      (ISA-state-p ISA))))
  (ISA-state (addr (1+ (ISA-pc ISA)))
	     (write-reg (word (+ (read-reg ra (ISA-regs ISA))
				 (read-reg rb (ISA-regs ISA))))
			rc (ISA-regs ISA))
	     (ISA-mem ISA)))

; Definition of the effect of an SUB instruction.
(defun ISA-sub (rc ra rb ISA)
  (declare (xargs :guard (and (rname-p rc) (rname-p ra) (rname-p rb)
			      (ISA-state-p ISA))))
  (ISA-state (addr (1+ (ISA-pc ISA)))
	     (write-reg (word (- (read-reg ra (ISA-regs ISA))
				 (read-reg rb (ISA-regs ISA))))
			rc (ISA-regs ISA))
	     (ISA-mem ISA)))

; Definition of NOP. It only increments the program counter.
(defun ISA-default (ISA)
  (declare (xargs :guard (ISA-state-p ISA)))
  (ISA-state (addr (1+ (ISA-pc ISA)))
	     (ISA-regs ISA)
	     (ISA-mem ISA)))

; Next ISA state function.  It takes the current ISA state and returns
; the ISA state after executing one instruction.  This function is a
; simple dispatcher of corresponding functions depending on the
; instruction type.
(defun ISA-step (ISA)
  (declare (xargs :guard (ISA-state-p ISA)))
  (let ((inst (read-mem (ISA-pc ISA) (ISA-mem ISA))))
    (let ((op (op-field inst))
	  (rc (rc-field inst))
	  (ra (ra-field inst))
	  (rb (rb-field inst)))
      (case op
	(0 (ISA-add rc ra rb ISA)) ; add
	(1 (ISA-sub rc ra rb ISA)) ; sub
	(otherwise (ISA-default ISA))))))

; N step ISA function.  It returns the ISA state after executing n
; instructions from the initial state, ISA.
(defun ISA-stepn (ISA n)
  (declare (xargs :guard (and (ISA-state-p ISA) (integerp n) (<= 0 n))))
  (if (zp n) ISA (ISA-stepn (ISA-step ISA) (1- n))))

(deflabel end-ISA-def)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; MA Definition
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Definition of MA states
;
; Definition of pipeline latch latch1.
(defstructure latch1
  (valid? (:assert (bitp valid?) :rewrite))
  (op     (:assert (opcd-p op)   :rewrite))
  (rc     (:assert (rname-p rc)  :rewrite))
  (ra     (:assert (rname-p ra)  :rewrite))
  (rb     (:assert (rname-p rb)  :rewrite))
  (:options :guards))

; Definition of pipeline latch latch2.
(defstructure latch2
  (valid?  (:assert (bitp valid?)   :rewrite))
  (op      (:assert (opcd-p op)     :rewrite))
  (rc      (:assert (rname-p rc)    :rewrite))
  (ra-val  (:assert (word-p ra-val) :rewrite))
  (rb-val  (:assert (word-p rb-val) :rewrite))
  (:options :guards))

; Definition of pipelined micro-architecture.
(defstructure MA-state
  (pc     (:assert (addr-p pc)       :rewrite (:rewrite (acl2-numberp pc))))
  (regs   (:assert (regs-p regs)     :rewrite))
  (mem    (:assert (mem-p mem)       :rewrite))
  (latch1 (:assert (latch1-p latch1) :rewrite))
  (latch2 (:assert (latch2-p latch2) :rewrite))
  (:options :guards  (:conc-name MA-)))

; Defines the signal supplied to the micro-architectural behavioral
; function.  We assume that the micro-architecture takes one bit
; input, which turn on and off instruction fetching.
(defun MA-sig-p (sig)
  (declare (xargs :guard t))
  (bitp sig))

; List of sig
(deflist MA-sig-listp (l)
  (declare (xargs :guard t))
  MA-sig-p)

(deflabel begin-MA-def)
; The definition of ALU.  The ALU takes opcode and two operands,
; and outputs the result.
(defun ALU-output (op val1 val2)
  (declare (xargs :guard (and (opcd-p op) (word-p val1) (word-p val2))))
  (cond ((equal op 0) (word (+ val1 val2)))
	((equal op 1) (word (- val1 val2)))
	(t 0)))

; *******************CHANGE********************
; The behavior of the register file.
; *******************CHANGE********************
(defun step-regs (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (MA-regs MA))

; The dependency check.  If there is a true (RAW) dependency
; between the instructions at latch1 and latch2, the instruction at
; latch1 should stall until the instruction at latch2 completes.  We
; check whether the destination register of the instruction at latch2
; is one of the source registers of the instruction at latch1.
(defun dependency? (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (let ((latch1 (MA-latch1 MA))
	(latch2 (MA-latch2 MA)))
    (b-ior (bv-eqv *rname-size* (latch1-ra latch1) (latch2-rc latch2))
	   (bv-eqv *rname-size* (latch1-rb latch1) (latch2-rc latch2)))))

(defthm bitp-dependency
    (bitp (dependency? MA)))

; The stall condition.  If both latch1 and latch2 contain valid
; instructions, and there are dependencies between the two
; instructions, the instruction at latch1 is stalled.
(defun stall-cond? (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (b-and (latch1-valid? (MA-latch1 MA))
	 (b-and (latch2-valid? (MA-latch2 MA))
		(dependency? MA))))

(defthm bitp-stall-cond
    (bitp (stall-cond? MA)))

; *******************CHANGE********************
; Next state function for pipeline latch latch2.  The instruction at
; latch1 advances to latch2 and latch2 is invalidated.
; *******************CHANGE********************
(defun step-latch2 (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (let ((latch1 (MA-latch1 MA)))
    (latch2 0
	    (latch1-op latch1)
	    (latch1-rc latch1)
	    (read-reg (latch1-ra latch1) (MA-regs MA))
	    (read-reg (latch1-rb latch1) (MA-regs MA)))))


; *******************CHANGE********************
; This function defines how latch1 is updated. It is the same as
; Sawada's fuction, except it is always invalid.
; *******************CHANGE********************
(defun step-latch1 (MA sig)
  (declare (xargs :guard (and (MA-state-p MA) (MA-sig-p sig)))
	   (ignore sig))
  (let ((latch1 (MA-latch1 MA))
	(inst (read-mem (MA-pc MA) (MA-mem MA))))
    (latch1 0
	    (b-if (stall-cond? MA) (latch1-op latch1) (op-field inst))
	    (b-if (stall-cond? MA) (latch1-rc latch1) (rc-field inst))
	    (b-if (stall-cond? MA) (latch1-ra latch1) (ra-field inst))
	    (b-if (stall-cond? MA) (latch1-rb latch1) (rb-field inst)))))


; The condition whether a new instruction is fetched.
(defun fetch-inst? (MA sig)
  (declare (xargs :guard (and (MA-state-p MA) (MA-sig-p sig))))
  (b-and sig
	 (b-nand (latch1-valid? (MA-latch1 MA))
		 (b-and (latch2-valid? (MA-latch2 MA))
			(dependency? MA)))))

(defthm bitp-fetch-inst?
    (bitp (fetch-inst? MA sig)))

; *******************CHANGE********************
; Function step-pc defines how the program counter is updated.  In our
; case, it never changes.
; *******************CHANGE********************
(defun step-pc (MA sig)
  (declare (xargs :guard (and (MA-state-p MA) (MA-sig-p sig)))
	   (ignore sig))
  (MA-pc MA))

; MA-step defines how the MA state is updated every clock cycle.  The
; memory does not change in our model.  The behavior of other
; components is specified by the corresponding step functions.
(defun MA-step (MA sig)
  (declare (xargs :guard (and (MA-state-p MA) (MA-sig-p sig))))
  (MA-state (step-pc MA sig)
	    (step-regs MA)
	    (MA-mem MA)
	    (step-latch1 MA sig)
	    (step-latch2 MA)))

; MA-stepn returns the MA state after n clock cycles of MA execution.
; The argument MA is the initial state, and sig-list specifies the
; series of inputs.
(defun MA-stepn (MA sig-list n)
  (declare (xargs :guard (and (MA-state-p MA) (MA-sig-listp sig-list)
			      (integerp n) (<= 0 n)
			      (<= n (len sig-list)))))
  (if (zp n)
      MA
      (MA-stepn (MA-step MA (car sig-list)) (cdr sig-list) (1- n))))

(deflabel end-MA-def)

(deftheory ISA-def
    (set-difference-theories
     (set-difference-theories (function-theory 'end-ISA-def)
			      (function-theory 'begin-ISA-def))
     '(ISA-stepn)))

(deftheory MA-def
    (set-difference-theories
     (set-difference-theories (function-theory 'end-MA-def)
			      (function-theory 'begin-MA-def))
     '(MA-stepn)))

(in-theory (disable ISA-def MA-def MA-sig-p))

;;;;;;;; Type proofs ;;;;;;;;
(defthm ISA-state-p-ISA-step
    (implies (ISA-state-p ISA) (ISA-state-p (ISA-step ISA)))
  :hints (("Goal" :in-theory (enable ISA-step ISA-add ISA-sub ISA-default))))

(defthm ISA-state-p-ISA-stepn
    (implies (ISA-state-p ISA) (ISA-state-p (ISA-stepn ISA n))))

(defthm addr-p-step-pc
    (implies (MA-state-p MA) (addr-p (step-pc MA sig)))
  :hints (("Goal" :in-theory (enable step-pc))))

(defthm word-p-ALU-output
    (implies (and (opcd-p op) (word-p val1) (word-p val2))
	     (word-p (ALU-output op val1 val2)))
  :hints (("Goal" :in-theory (enable ALU-output))))

(defthm regs-p-step-regs
    (implies (MA-state-p MA) (regs-p (step-regs MA)))
  :hints (("Goal" :in-theory (enable step-regs))))

(defthm latch1-p-step-latch1
    (implies (and (MA-state-p MA) (MA-sig-p sig))
	     (latch1-p (step-latch1 MA sig)))
  :hints (("Goal" :in-theory (enable step-latch1 MA-sig-p))))

(defthm latch1-p-step-latch2
    (implies (and (MA-state-p MA) (MA-sig-p sig))
	     (latch2-p (step-latch2 MA)))
  :hints (("Goal" :in-theory (enable step-latch2 MA-sig-p))))

(defthm MA-state-p-MA-step
    (implies (and (MA-state-p MA) (MA-sig-p sig))
	     (MA-state-p (MA-step MA sig)))
  :hints (("Goal" :in-theory (enable MA-step))))

(defthm MA-state-p-MA-stepn
    (implies (and (MA-state-p MA) (MA-sig-listp sig-list)
		  (<= n (len sig-list)))
	     (MA-state-p (MA-stepn MA sig-list n))))

;;;  Predicates for correctness

; The projection function from an MA state to the corresponding ISA
; state. Function proj strips off pipeline latches from the MA state.
(defun proj (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (ISA-state (MA-pc MA) (MA-regs MA) (MA-mem MA)))

; (flushed? MA) is true if the pipeline of MA is flushed.
(defun flushed? (MA)
  (b-nor (latch1-valid? (MA-latch1 MA))
	 (latch2-valid? (MA-latch2 MA))))

#|
We will prove a following lemma for operational correctness:
(defthm correctness
    (implies (and (MA-state-p MA)
		  (MA-sig-listp sig-list)
		  (<= n (len sig-list))
		  (b1p (flushed? MA))
		  (b1p (flushed? (MA-stepn MA sig-list n))))
	     (equal (proj (MA-stepn MA sig-list n))
		    (ISA-stepn (proj MA)
			       (num-insts MA sig-list n)))))

where num-insts calculates the nunber of instructions executed in the
n cycles of MA execution.  We also prove the liveness property with:

(defthm liveness
    (implies (MA-state-p MA)
	     (b1p (flushed? (MA-stepn MA
				      (zeros (flush-cycles MA))
				      (flush-cycles MA)))))).

Function flush-cycles calculates the number of cycles to flush the pipeline.
|#
