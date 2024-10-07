;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; MA2-def.lisp
; Author  Jun Sawada, University of Texas at Austin
;
; This file contains the microarchitectural definition of the FM9801.
; This version deploys the Tomasulo Algorithm with a re-order buffer.
; This is an out-of-order multi-issue machine.  The specification is
; written using the IHS library.  It also requires the book basic-def,
; which defines the register file and the memory.
;
; The next-state function (MA-step MA sigs) returns the next state of
; the pipelined machine.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "ACL2")

(include-book "b-ops-aux-def")
(include-book "basic-def")

;(include-book "multiplier-def")

(deflabel begin-MA2-def)
(defconst *abstract-impl-flag* 'abstract)

(defun take-locals (events)
    (if (endp events)
	nil
	(let ((ev (car events)))
	  (cons (cadr ev) (take-locals (cdr events))))))
	      
(defmacro encapsulate-impl (stubs &rest events)
  `(encapsulate ,stubs
    ,@(if (equal *abstract-impl-flag* 'executable)
	  (take-locals events)
	  events)))

#|
(defun wrap-local (defs)
  (if (endp defs)
      nil
      (cons `(local ,(car defs)) (wrap-local (cdr defs)))))

(defmacro encapsulate-impl (name stubs defs thms)
  (let ((begin-def-label (pack-intern name "BEGIN-DEF-" name))
	(end-def-label (pack-intern name "END-DEF-" name))
	(def-label (pack-intern name "DEF-" name))
	(begin-theory-label (pack-intern name "BEGIN-THEORY-" name))
	(end-theory-label (pack-intern name "END-THEORY-" name))
	(theory-label (pack-intern name "THEORY-" name)))
    (cond ((equal *abstract-impl-flag* 'abstract)
	   `(encapsulate ,stubs
	    ,@(wrap-local defs)
	    (deflabel ,begin-theory-label)
	    ,@thms
	    (deflabel ,end-theory-label)
	    (deftheory ,theory-label
		(set-difference-theories
		 (universal-theory ',end-theory-label)
		 (universal-theory ',begin-theory-label)))))
	 ((equal *abstract-impl-flag* 'executable)
	  `(encapsulate nil
	    (deflabel ,begin-def-label)
	    ,@defs
	    (deflabel ,end-def-label)
	    (deflabel ,begin-theory-label)
	    ,@thms
	    (deflabel ,end-theory-label)
	    (deftheory ,def-label
		(set-difference-theories
		 (universal-theory ',end-def-label)
		 (universal-theory ',begin-def-label)))
	    (deftheory ,theory-label
		(set-difference-theories
		 (universal-theory ',end-theory-label)
		 (universal-theory ',begin-theory-label)))
	    (in-theory (disable ,def-label))))
	 (t
	  (er hard 'encapsulate-impl
	      "*abstract-impl-flag* must be 'abstract or 'executable")))))
|#

(deflabel begin-MA-state)

(defconst *rob-index-size* 3)
(defconst *rob-size* (expt 2 *rob-index-size*))
(defbytetype rob-index *rob-index-size* :unsigned)

(defthm rob-index-p-forward-unsigned-byte
    (implies (rob-index-p idx) (unsigned-byte-p *rob-index-size* idx))
  :hints (("goal" :in-theory (enable rob-index-p)))
  :rule-classes :forward-chaining)

(defthm rob-index-p-bv-eqv-iff-equal
    (implies (and (rob-index-p idx1) (rob-index-p idx2))
	     (equal (b1p (bv-eqv *rob-index-size* idx1 idx2))
		    (equal idx1 idx2)))
  :hints (("goal" :in-theory (enable rob-index-p))))

#|
THE DEFINITION OF CONTROL VECTOR:

The control bits are defined as follows:
 exunit: indicate the selected execution unit.
          exunit bit 0: integer unit
                 bit 1: multiplier
                 bit 2: load-store unit
                 bit 3: branch?
                 bit 4: no execution unit

 operand: indicates the operand format.
          bit 0: dispatcher outputs RA to port val1 and RB to port val2
          bit 1: dispatcher outputs immediate to port val1
          bit 2: dispatcher outputs RC to port val1
          bit 3: dispatcher outputs special register value to port val1
 br-predict?: branch is taken speculatively?
 ld-st?:  load or store when exunit=3.
                 0: load
                 1: store
 wb?:     Whether instruction needs to write back its result.
 wb-sreg?:    whether results should be written back to a special register.
 sync?:   whether the instruction forces synchronization.
 rfeh?:   This bit is set for RFEH instructions.

|#

;; The definition of the control vector. An instruction is decoded
;; into a control vector at the decode stage, and will be passed to
;; the following latches.
;;
;; Access functions to the fields are given by cntlv-<name of field>.
;; For instance, cntlv-exunit is the access function to field exunit.
(defword cntlv-word ((exunit 5 10)
		     (operand 4 6)
		     (br-predict? 1 5)
		     (ld-st? 1 4)
		     (wb? 1 3)
		     (wb-sreg? 1 2)
		     (sync? 1 1)
		     (rfeh? 1 0))
  :conc-name cntlv-)

(defbytetype cntlv 15 :unsigned)

#|
Exception Flags
 raised?:     Exception is raised
 ex-type: Exception type
                 0: Illegal Instruction
                 1: Fetch Error
                 2: Data Access Error
                 3: External Interrupt
|#
(defword excpt-word ((raised? 1 2)
		     (type 2 0))
  :conc-name excpt-)

(defbytetype excpt-flags 3 :unsigned)

;; Microarchitectural specification uses four inputs corresponding to
;; an external interrupt, a fetch unit response, a data unit response,
;; and the oracle to determine the branch prediction.  1 means the
;; corresponding event takes place.  For instance, an external
;; interrupt is requested when exintr is 1.  An instruction fetch can
;; take place when fetch is 1.  We try to model the asynchronous
;; behavior of memory with oracle inputs.  If we keep MA-input-fetch
;; to be 0, we can flush the pipeline.  Field br-predict is an oracle
;; to specify the nondeterministic behavior of the branch predictor.
(defstructure MA-input
  (exintr (:assert (bitp exintr) :rewrite))
  (br-predict (:assert (bitp br-predict) :rewrite))
  (fetch (:assert (bitp fetch) :rewrite))
  (data  (:assert (bitp data) :rewrite))
  (:options :guards))

(deflist MA-input-listp (l)
  (declare (xargs :guard t))
  MA-input-p)

; The instruction fetch unit.  The program counter is considered to
; belong to a different unit.  The instruction fetch unit stores an
; instruction temporarily, and sends it to the dispatching queue if
; there is an empty queue entry.
(defstructure IFU
  (valid? (:assert (bitp valid?) :rewrite))
  (excpt (:assert (excpt-flags-p excpt) :rewrite (:rewrite (integerp excpt))))
  (pc (:assert (addr-p pc) :rewrite (:rewrite (integerp pc))
	       (:rewrite (acl2-numberp pc))))
  (word (:assert (word-p word) :rewrite (:rewrite (integerp word))))
  (:options :guards))

;; Branch predictor state
(defstructure BP
  (seed)
  (:options :guards))

; A dispatch queue entry stores a decoded instruction.
(defstructure dispatch-entry
  (valid? (:assert (bitp valid?) :rewrite))
  (excpt (:assert (excpt-flags-p excpt) :rewrite (:rewrite (integerp excpt))))
  (pc (:assert (addr-p pc) :rewrite (:rewrite (integerp pc))
	       (:rewrite (acl2-numberp pc))))
  (cntlv (:assert (cntlv-p cntlv) :rewrite (:rewrite (integerp cntlv))))
  (rc (:assert (rname-p rc) :rewrite))
  (ra (:assert (rname-p ra) :rewrite))
  (rb (:assert (rname-p rb) :rewrite))
  (im (:assert (immediate-p im) :rewrite))
  (br-target (:assert (addr-p br-target) :rewrite
		      (:rewrite (integerp br-target))))
  (:options :guards (:conc-name DE-)))

; Register Reference Table Entry.
; wait? is 1 iff the register value is not updated, and there are
; instructions in the ROB that modify this register.  Tag is the
; ROB entry that contains the instruction that modifies the corresponding
; register.
(defstructure reg-ref
  (wait? (:assert (bitp wait?) :rewrite))
  (tag (:assert (rob-index-p tag) :rewrite (:rewrite (integerp tag))))
  (:options :guards))

(deflist reg-ref-listp (l)
    (declare (xargs :guard t))
    reg-ref-p)

(defun reg-tbl-p (RF)
  (declare (xargs :guard t))
  (and (reg-ref-listp RF) (equal (len RF) *num-regs*)))

(defun reg-tbl-nth (n tbl)
  (declare (xargs :guard (and (rname-p n) (reg-tbl-p tbl))))
  (nth n tbl))

(defthm reg-ref-p-reg-tbl-nth
    (implies (and (reg-tbl-p tbl) (rname-p n))
	     (reg-ref-p (reg-tbl-nth n tbl))))

(in-theory (disable reg-tbl-p reg-tbl-nth))

(defstructure sreg-tbl
  (sr0 (:assert (reg-ref-p sr0) :rewrite))
  (sr1 (:assert (reg-ref-p sr1) :rewrite))
  (:options :guards))

(defun sreg-tbl-nth (n tbl)
  (declare (xargs :guard (and (rname-p n) (sreg-tbl-p tbl))))
  (b-if (bv-eqv *rname-size* n 0) (sreg-tbl-sr0 tbl)
  (b-if (bv-eqv *rname-size* n 1) (sreg-tbl-sr1 tbl)
	(reg-ref 0 0))))

(defthm sreg-ref-p-sreg-tbl-nth
    (implies (and (sreg-tbl-p tbl) (rname-p n))
	     (reg-ref-p (sreg-tbl-nth n tbl))))
(in-theory (disable sreg-tbl sreg-tbl-nth))

; Dispatch queue has 4 entries. 
(defstructure DQ
  (DE0 (:assert (dispatch-entry-p DE0) :rewrite))
  (DE1 (:assert (dispatch-entry-p DE1) :rewrite))
  (DE2 (:assert (dispatch-entry-p DE2) :rewrite))
  (DE3 (:assert (dispatch-entry-p DE3) :rewrite))
  (reg-tbl (:assert (reg-tbl-p reg-tbl) :rewrite))
  (sreg-tbl (:assert (sreg-tbl-p sreg-tbl) :rewrite))
  (:options :guards))

(defthm len-DQ-reg-tbl
    (implies (DQ-p DQ)
	     (equal (len (DQ-reg-tbl DQ)) *num-regs*))
  :hints (("Goal" :in-theory (enable reg-tbl-p DQ-p))))

; The ROB entry. 
; excpt contains the exception flags.
; val stores the result of the corresponding instruction.
; dest is the destination register file.
; pc is the program counter of the instruction.
; br-predict? and br-actual? contains the branch prediction result and
;   actual outcome, respectively.
; Other fields are control vector fields.
(defstructure ROB-entry
  (valid? (:assert (bitp valid?) :rewrite))
  (complete? (:assert (bitp complete?) :rewrite))
  (excpt (:assert (excpt-flags-p excpt) :rewrite (:rewrite (integerp excpt))))
  (wb? (:assert (bitp wb?) :rewrite))
  (wb-sreg? (:assert (bitp wb-sreg?) :rewrite))
  (sync? (:assert (bitp sync?) :rewrite))
  (branch? (:assert (bitp branch?) :rewrite))
  (rfeh? (:assert (bitp rfeh?) :rewrite))
  (br-predict? (:assert (bitp br-predict?) :rewrite))
  (br-actual? (:assert (bitp br-actual?) :rewrite))
  (pc (:assert (addr-p pc) :rewrite (:rewrite (integerp pc))
	       (:rewrite (acl2-numberp pc))))
  (val (:assert (word-p val) :rewrite (:rewrite (integerp val))))
  (dest (:assert (rname-p dest) :rewrite (:rewrite (integerp dest))))
  (:options :guards (:conc-name ROBE-)))

(deflist ROBE-listp (l)
  (declare (xargs :guard t))
  ROB-entry-p)

(defun ROB-entries-p (l)
  (declare (xargs :guard t))
  (and (ROBE-listp l) (equal (len l) *rob-size*)))

(defthm true-listp-rob-entries
    (implies (ROB-entries-p l) (true-listp l)))

(in-theory (disable ROB-entries-p))

; Reorder buffer contains re-order buffer entries and indices to their
; head and tail. Re-order buffer is a FIFO queue.  Head points to the
; oldest instruction which will be committed next.  Tail points to the
; newest instruction which is dispatched most recently.  It also
; contains the external interrupt flag exintr? and a flag to indicate
; whether head is larger than equal to tail.  This flag is set when
; the tail is wrapped-around to 0, and it is cleared when the head is
; wrapped-around to 0.  If head and tail are equal and flag is off,
; the reorder buffer is empty.  If head and tail are equal and flag is
; on, the reorder buffer is full.
;
;
;        -------	        -------
;      0|       | flg=0       0|  I2   |  flg=1
;      1|       |             1|  I3   |
;      2|-------|	      2|-------|
;      3|   I1  |<- HEAD      3|       |<- TAIL
;      4|   I2  |	      4|       |
;      5|   I3  |             5|       |
;      6|-------|	      6|-------|
;      7|       |<- TAIL      7|  I1   |<- HEAD
;        -------                -------
(defstructure ROB
  (flg (:assert (bitp flg) :rewrite))
  (exintr? (:assert (bitp exintr?) :rewrite))
  (head (:assert (rob-index-p head) :rewrite
		 (:type-prescription (integerp head))))
  (tail (:assert (rob-index-p tail) :rewrite
		 (:type-prescription (integerp tail))))
  (entries (:assert (rob-entries-p entries) :rewrite))
  (:options :guards))

(defthm rob-listp-rob-entries
    (implies (rob-p rob) (robe-listp (rob-entries rob)))
  :hints (("Goal" :in-theory (enable rob-entries-p)
		  :use (defs-rob-assertions))))

(defun nth-ROBE (n ROB)
  (declare (xargs :guard (and (rob-index-p n) (ROB-p ROB))))
  (nth n (ROB-entries ROB)))

(defthm ROB-entry-p-nth-rob-entries
    (implies (and (rob-index-p n) (ROB-entries-p rob-entries))
	     (ROB-entry-p (nth n rob-entries)))
  :hints (("goal" :in-theory (enable rob-index-p rob-entries-p))))

(defthm ROB-entry-p-nth-robe
    (implies (and (rob-index-p n) (ROB-p ROB))
	     (ROB-entry-p (nth-ROBE n ROB))))

(in-theory (disable nth-ROBE))

; The structure of a reservation station.
; Op indicates what type of integer operation should be performed.
; When Op=0, IU returns the sum of two operands. When Op=1, IU returns the
; the first value itself.
(defstructure RS
  (valid? (:assert (bitp valid?) :rewrite))
  (op (:assert (bitp op) :rewrite))
  (tag (:assert (rob-index-p tag) :rewrite))
  (ready1? (:assert (bitp ready1?) :rewrite))
  (ready2? (:assert (bitp ready2?) :rewrite))
  (val1 (:assert (word-p val1) :rewrite (:rewrite (integerp val1))
		 (:rewrite (acl2-numberp val1))))
  (val2 (:assert (word-p val2) :rewrite (:rewrite (integerp val2))
		 (:rewrite (acl2-numberp val2))))
  (src1 (:assert (rob-index-p src1) :rewrite))
  (src2 (:assert (rob-index-p src2) :rewrite))
  (:options :guards))

; The IU unit. It has two reservation stations.
(defstructure integer-unit
  (rs0 (:assert (RS-p rs0) :rewrite))
  (rs1 (:assert (RS-p rs1) :rewrite))
  (:options :guards (:conc-name IU-)))

; Latch of the MU.  tag is the Tomasulo's tag for the instruction in
; the latch. data contains the intermediate value. 
;
; Note:
; The following definition of the multiplier latch is used for the 
; when plugging in the real multiplier in multiplier-def.lisp.
;(defstructure MU-latch1
;  (valid? (:assert (bitp valid?) :rewrite))
;  (tag (:assert (rob-index-p tag) :rewrite))
;  (data (:assert (ML1-data-p data) :rewrite))
;  (:options :guards))

(defun ML1-data-p (x)
  (declare (xargs :guard t))
  (and (consp x) (integerp (car x)) (integerp (cdr x))))

(defun ML2-data-p (x)
  (declare (xargs :guard t))
  (and (consp x) (integerp (car x)) (integerp (cdr x))))

(defstructure MU-latch1
  (valid? (:assert (bitp valid?) :rewrite))
  (tag (:assert (rob-index-p tag) :rewrite))
  (data)
  (:options :guards))

; Note:
; The following definition of the multiplier latch is used for the 
; when plugging in the real multiplier.
;(defstructure MU-latch2
;  (valid? (:assert (bitp valid?) :rewrite))
;  (tag (:assert (rob-index-p tag) :rewrite))
;  (data (:assert (ML2-data-p data) :rewrite))
;  (:options :guards))

(defstructure MU-latch2
  (valid? (:assert (bitp valid?) :rewrite))
  (tag (:assert (rob-index-p tag) :rewrite))
  (data)
  (:options :guards))

; Three stage multiplier unit.
(defstructure mult-unit
  (rs0 (:assert (RS-p rs0) :rewrite))
  (rs1 (:assert (RS-p rs1) :rewrite))
  (lch1 (:assert (MU-latch1-p lch1) :rewrite))
  (lch2 (:assert (MU-latch2-p lch2) :rewrite))
  (:options :guards (:conc-name MU-)))

; The structure of a reservation station for the memory unit.
; Op indicates how to calculate the access address. 0 means the sum of
; RA and RB registers is the access address.  1 means that the immediate
; value is the access address.
(defstructure LSU-RS
  (valid? (:assert (bitp valid?) :rewrite))
  (op (:assert (bitp op) :rewrite))
  (ld-st? (:assert (bitp ld-st?) :rewrite))
  (tag (:assert (rob-index-p tag) :rewrite))
  (rdy3? (:assert (bitp rdy3?) :rewrite))
  (val3 (:assert (word-p val3) :rewrite (:rewrite (integerp val3))))
  (src3 (:assert (rob-index-p src3) :rewrite))
  (rdy1? (:assert (bitp rdy1?) :rewrite))
  (val1 (:assert (word-p val1) :rewrite (:rewrite (integerp val1))
		 (:rewrite (acl2-numberp val1))))
  (src1 (:assert (rob-index-p src1) :rewrite))
  (rdy2? (:assert (bitp rdy2?) :rewrite))
  (val2 (:assert (word-p val2) :rewrite (:rewrite (integerp val2))
		 (:rewrite (acl2-numberp val2))))
  (src2 (:assert (rob-index-p src2) :rewrite))
  (:options :guards))

; Fields of the read buffer.  Fields wbuf0? and wbuf1? records whether
; write buffer 0 and 1 are occupied when the read operation is issued.
; In other words, wbuf0? implies that the instruction at wbuf0
; precedes the read operation in program order.  This is used to check
; whether data dependencies exist between load and store instructions.
; tag is Tomasulo's tag.  Addr is the access address.
(defstructure read-buffer
  (valid? (:assert (bitp valid?) :rewrite))
  (tag (:assert (rob-index-p tag) :rewrite))
  (addr (:assert (addr-p addr) :rewrite (:rewrite (integerp addr))))
  (wbuf0? (:assert (bitp wbuf0?) :rewrite))
  (wbuf1? (:assert (bitp wbuf1?) :rewrite))
  (:options :guards (:conc-name rbuf-)))

; Write buffer entry.  Valid? is 1, whenever it contain a valid
; instruction.  complete? is 1 when the address check is performed.
; commit? is set to 1, when the corresponding instruction commits.
; The write operation is not performed until the commit occurs,
; because there is no way to roll back the memory access when an
; exception occurs.  Tag is Tomasulo's tag.  Addr is the access
; address.  Val is the stored instruction.
(defstructure write-buffer
  (valid? (:assert (bitp valid?) :rewrite))
  (complete? (:assert (bitp complete?) :rewrite))
  (commit? (:assert (bitp commit?) :rewrite))
  (tag (:assert (rob-index-p tag) :rewrite))
  (addr (:assert (addr-p addr) :rewrite (:rewrite (integerp addr))))
  (val (:assert (word-p val) :rewrite (:rewrite (integerp val))))
  (:options :guards (:conc-name wbuf-)))

; The result latch for the LSU.  excpt contains the exception flag. 
; tag is Tomasulo's tag.  val is the load instruction result.
(defstructure LSU-latch
  (valid? (:assert (bitp valid?) :rewrite))
  (excpt (:assert (excpt-flags-p excpt) :rewrite (:rewrite (integerp excpt))))
  (tag (:assert (rob-index-p tag) :rewrite))
  (val (:assert (word-p val) :rewrite (:rewrite (integerp val))))
  (:options :guards))

; The reservation stations for the LSU forms a queue, because the
; memory access order is critical in executing programs.  The head of the
; queue is indicated by the flag rs1-head?.  When rs1-head? is on, RS1 is
; the head of the queue.  Otherwise, RS0 is the head. 
(defstructure load-store-unit
  (rs1-head? (:assert (bitp rs1-head?) :rewrite))
  (rs0 (:assert (LSU-RS-p rs0) :rewrite))
  (rs1 (:assert (LSU-RS-p rs1) :rewrite))
  (rbuf (:assert (read-buffer-p rbuf) :rewrite))
  (wbuf0 (:assert (write-buffer-p wbuf0) :rewrite))
  (wbuf1 (:assert (write-buffer-p wbuf1) :rewrite))
  (lch (:assert (LSU-latch-p lch) :rewrite))
  (:options :guards (:conc-name LSU-)))

; The reservation station for the BU stores the operand RC.  BR
; command checks whether RC is equal to 0, and if so it sets the
; program counter to the sum of the program counter for the BR
; instruction and the relative address obtained from the im field.
; This jump address is calculated in the decode stage.
(defstructure BU-RS
  (valid? (:assert (bitp valid?) :rewrite))
  (tag (:assert (rob-index-p tag) :rewrite))
  (ready? (:assert (bitp ready?) :rewrite))
  (val (:assert (word-p val) :rewrite (:rewrite (integerp val))))
  (src (:assert (rob-index-p src) :rewrite))
  (:options :guards))

; The BU has two reservation stations.
(defstructure branch-unit
  (rs0 (:assert (BU-RS-p rs0) :rewrite))
  (rs1 (:assert (BU-RS-p rs1) :rewrite))
  (:options :guards (:conc-name BU-)))

;; Definition of the pipelined machine states. A machine state
;; contains a program counter, a register file, special register file,
;; instruction fetch unit, dispatch unit, re-order buffer, integer
;; unit, multiplier unit branch unit memory unit and memory.
(defstructure MA-state
  (pc (:assert (addr-p pc) :rewrite (:rewrite (integerp pc))
	       (:rewrite (acl2-numberp pc))))
  (RF (:assert (RF-p RF) :rewrite))
  (SRF (:assert (SRF-p SRF) :rewrite))
  (IFU  (:assert (IFU-p IFU) :rewrite))
  (BP   (:assert (BP-p BP) :rewrite))
  (DQ   (:assert (DQ-p DQ) :rewrite))
  (ROB (:assert (rob-p ROB) :rewrite :type-prescription))
  (IU  (:assert (integer-unit-p IU) :rewrite))
  (MU  (:assert (mult-unit-p MU) :rewrite))
  (BU (:assert (branch-unit-p BU) :rewrite))
  (LSU (:assert (load-store-unit-p LSU) :rewrite))
  (mem (:assert (mem-p mem) :rewrite))
  (:options :guards (:conc-name MA-)))

(deflabel end-MA-state)

(deflabel begin-MA-def)

(defun rand (x seed)
  (declare (xargs :guard (integerp x)))
  (floor (* x (/ (mod (nfix seed) 4294967296) 4294967296)) 1))

(defun genseed (seed)
  (declare (xargs :guard t))
  (let ((n (mod (nfix seed) 4294967296)))
    (+ n (* n 4) (* n 131072) (* n 134217728))))


(defthm integerp-rand
  (implies (integerp x) (integerp (rand x seed))))

(defthm bitp-random-2
  (bitp (rand 2 seed))
  :hints (("goal" :in-theory (enable bitp))))
(in-theory (disable rand))  

; This is the branch prediction function.  We can replace the
; implementation with other realistic ones.
(encapsulate-impl ((branch-predict? (MA) t)
		   (step-bp-seed (MA) t))
(local
 (defun branch-predict? (MA)
   (declare (xargs :guard (MA-state-p MA)))
   (rand 2 (BP-seed (MA-BP MA)))))

(local
 (defun step-bp-seed (MA)
   (declare (xargs :guard (MA-state-p MA)))
   (genseed (BP-seed (MA-BP MA)))))

(defthm bitp-branch-predict?
  (bitp (branch-predict? MA)))
)

; IFU-branch-predict? is set if the decode unit finds a branch instruction
; in IFU and it predicts the branch is taken.  IFU-branch-target should
; post the target address when IFU-branch-predict? is set.
(defun IFU-branch-predict? (IFU MA sigs)
  (declare (xargs :guard (and (IFU-p IFU) (MA-state-p MA) (MA-input-p sigs)))
; Matt K. mod: Added necessary ignorable declaration.
           (ignorable sigs))
  (bs-and (IFU-valid? IFU)
	  (b-not (excpt-raised? (IFU-excpt IFU)))
	  (bv-eqv *opcode-size* (opcode (IFU-word IFU)) 2)
	  (branch-predict? MA)))

(defthm bitp-IFU-branch-predict (bitp (IFU-branch-predict? IFU MA sigs)))

; Generating the branch target address.
(defun IFU-branch-target (IFU)
  (declare (xargs :guard (IFU-p IFU)))
  (addr (+ (IFU-pc IFU)
	   (logextu *addr-size* *immediate-size* (im (IFU-word IFU))))))

(defthm addr-p-IFU-branch-target
    (implies (IFU-p IFU) (addr-p (IFU-branch-target IFU))))
(in-theory (disable IFU-branch-target))

; Instruction fetch is prohibited, if the memory is not readable, and
; the processor is in the user mode. 
(defun IFU-fetch-prohibited? (pc mem su)
  (declare (xargs :guard (and (addr-p pc) (mem-p mem) (bitp su))))
  (b-nor (readable-addr? pc mem) su))

#|

THE DEFINITION OF CONTROL VECTOR:

The control bits are defined as follows:
 exunit: indicate the selected execution unit.
          exunit bit 0: adder
                 bit 1: multiplier
                 bit 2: load-store unit
                 bit 3: branch?
                 bit 4: no execution unit
 operand: indicates the operand format.
          bit 0: dispatcher outputs RA to port val1 and RB to port val2
          bit 1: dispatcher outputs immediate to port val1
          bit 2: dispatcher outputs RC to port val1
          bit 3: dispatcher outputs special register value to port val1
 branch-predict?: branch is taken speculatively?
 ld-st?:  load or store when exunit=3.
                 0: load
                 1: store
 wb?:     Whether instruction needs to write back its result.
 wb-sreg?:    whether results should be written back to a special register.
 sync?:   whether the instruction forces a synchronization.
 rfeh?:   This bit is on for instruction RFEH

We define six opcodes:

 ADD 0		Addition
 MUL 1		Multiplication
 BR  2		Conditional Branch
 LD  3		Load Memory
 ST  4		Store Memory
 SYNC 5		Synchronize
 LD-IM 6        Load from an immediate address
 ST-IM 7        Store at an immediate address
 RFEH  8        Return from Exception Handling (privileged)
 MFSR  9        Move From a Special Register (privileged)
 MTSR  10       Move To a Special Register (privileged)
|#

; Decoder. 
(defun decode (opcd branch-predict?)
  (declare (xargs :guard (and (opcd-p opcd) (bitp branch-predict?))
		  :guard-hints (("Goal" :in-theory (enable opcd-p)))))
  (logcons (bv-eqv *opcode-size* opcd 8) ; rfeh?
  (logcons (b-ior (bv-eqv *opcode-size* opcd 5)
		  (bv-eqv *opcode-size* opcd 8)) ; sync?
  (logcons (bv-eqv *opcode-size* opcd 10) ; wb-sreg?
  (logcons (bs-ior (bv-eqv *opcode-size* opcd 0)
		   (bv-eqv *opcode-size* opcd 1)
		   (bv-eqv *opcode-size* opcd 3)
		   (bv-eqv *opcode-size* opcd 6)
		   (bv-eqv *opcode-size* opcd 9)
		   (bv-eqv *opcode-size* opcd 10)) ; wb?
  (logcons (b-ior (bv-eqv *opcode-size* opcd 4)
		  (bv-eqv *opcode-size* opcd 7)) ; ld-st?
  (logcons branch-predict? ; branch-predict?
  (logcons (bs-ior (bv-eqv *opcode-size* opcd 0)
		   (bv-eqv *opcode-size* opcd 1)
		   (bv-eqv *opcode-size* opcd 3)
		   (bv-eqv *opcode-size* opcd 4)) ; operand:0
  (logcons (b-ior (bv-eqv *opcode-size* opcd 6)
		  (bv-eqv *opcode-size* opcd 7)) ; operand:1
  (logcons (b-ior (bv-eqv *opcode-size* opcd 2)
		  (bv-eqv *opcode-size* opcd 10)) ; operand:2
  (logcons (bv-eqv *opcode-size* opcd 9) ;operand:3
  (logcons (bs-ior (bv-eqv *opcode-size* opcd 0)
		   (bv-eqv *opcode-size* opcd 9)
		   (bv-eqv *opcode-size* opcd 10)) ; exunit:0
  (logcons (bv-eqv *opcode-size* opcd 1) ; exunit:1
  (logcons (bs-ior (bv-eqv *opcode-size* opcd 3)
		   (bv-eqv *opcode-size* opcd 4)
		   (bv-eqv *opcode-size* opcd 6)
		   (bv-eqv *opcode-size* opcd 7))
  (logcons (bv-eqv *opcode-size* opcd 2)
	   (b-ior (bv-eqv *opcode-size* opcd 5)
		  (bv-eqv *opcode-size* opcd 8))))))))))))))))) ; exunit:2

(defthm cntlv-p-decode
    (implies (and (opcd-p opcd) (bitp flg)) (cntlv-p (decode opcd flg)))
  :hints (("Goal" :in-theory (enable cntlv-p unsigned-byte-p*))))

(in-theory (disable decode))

; Whether the decoded instruction is an illegal instruction.
(defun decode-illegal-inst? (opcd su ra)
  (declare (xargs :guard (and (opcd-p opcd) (bitp su) (rname-p ra))
		  :guard-hints (("Goal" :in-theory (enable opcd-p)))))
  (bs-and (b-not (bv-eqv *opcode-size* opcd 0))
	  (b-not (bv-eqv *opcode-size* opcd 1))
	  (b-not (bv-eqv *opcode-size* opcd 2))
	  (b-not (bv-eqv *opcode-size* opcd 3))
	  (b-not (bv-eqv *opcode-size* opcd 4))
	  (b-not (bv-eqv *opcode-size* opcd 5))
	  (b-not (bv-eqv *opcode-size* opcd 6))
	  (b-not (bv-eqv *opcode-size* opcd 7))
	  (b-not (b-and (bv-eqv *opcode-size* opcd 8) su))
	  (b-not (bs-and (bv-eqv *opcode-size* opcd 9)
			 su
			 (b-ior (bv-eqv *rname-size* ra 0)
				(bv-eqv *rname-size* ra 1))))
	  (b-not (bs-and (bv-eqv *opcode-size* opcd 10)
			 su
			 (b-ior (bv-eqv *rname-size* ra 0)
				(bv-eqv *rname-size* ra 1))))))

(defthm bitp-decode-illegal-inst (bitp (decode-illegal-inst? opcd su ra)))

; Output from the decoder. 
(defun decode-output (IFU MA sigs)
  (declare (xargs :guard (and (IFU-p IFU) (MA-state-p MA) (MA-input-p sigs))
		  :verify-guards nil))
  (dispatch-entry (IFU-valid? IFU)
		  (b-if (excpt-raised? (IFU-excpt IFU))
			(IFU-excpt IFU)
			(b-if (decode-illegal-inst?
			       (opcode (IFU-word IFU)) (SRF-su (MA-SRF MA))
			       (ra (IFU-word IFU)))
			      #b100 0))
		  (IFU-pc IFU)
		  (decode (opcode (IFU-word IFU))
			  (IFU-branch-predict? IFU MA sigs))
		  (rc (IFU-word IFU))
		  (ra (IFU-word IFU))
		  (rb (IFU-word IFU))
		  (im (IFU-word IFU))
		  (IFU-branch-target IFU)))

(verify-guards decode-output
    :hints (("Goal" :in-theory (enable opcd-p))))

(defthm dispatch-entry-p-decode-output
    (implies (and (IFU-p IFU) (MA-state-p MA) (MA-input-p sigs))
	     (dispatch-entry-p (decode-output IFU MA sigs))))

(in-theory (disable decode-output))

; The destination register of the dispatched instruction.
(defun DQ-out-dest-reg (DQ)
  (declare (xargs :guard (DQ-p DQ)))
  (let ((DE0 (DQ-DE0 DQ)))
    (b-if (cntlv-wb-sreg? (DE-cntlv DE0))
	  (DE-ra DE0)
	  (DE-rc DE0))))

; Whether the first operand is ready.
(defun DQ-out-ready1? (DQ)
  (declare (xargs :guard (DQ-p DQ)))
  (let ((DE0 (DQ-DE0 DQ))
	(cntlv (DE-cntlv (DQ-DE0 DQ))))
    (b-if (logbit 0 (cntlv-operand cntlv))
	  (b-not (reg-ref-wait? (reg-tbl-nth (DE-ra DE0) (DQ-reg-tbl DQ))))
    (b-if (logbit 1 (cntlv-operand cntlv)) 1
    (b-if (logbit 2 (cntlv-operand cntlv))
	  (b-not (reg-ref-wait? (reg-tbl-nth (DE-rc DE0) (DQ-reg-tbl DQ))))
    (b-if (logbit 3 (cntlv-operand cntlv))
	  (b-not (reg-ref-wait?
		  (sreg-tbl-nth (DE-ra DE0) (DQ-sreg-tbl DQ))))
	  0))))))

(defthm bitp-DQ-out-ready1
    (implies (DQ-p DQ) (bitp (DQ-out-ready1? DQ))))

(in-theory (disable DQ-out-ready1?))

; Tomasulo's tag of the instruction that produces the first operand. 
(defun DQ-out-tag1 (DQ)
  (declare (xargs :guard (DQ-p DQ)))
  (let ((DE0 (DQ-DE0 DQ)) (cntlv (DE-cntlv (DQ-DE0 DQ))))
    (b-if (logbit 0 (cntlv-operand cntlv))
	  (reg-ref-tag (reg-tbl-nth (DE-ra DE0) (DQ-reg-tbl DQ)))
    (b-if (logbit 2 (cntlv-operand cntlv))
	  (reg-ref-tag (reg-tbl-nth (DE-rc DE0) (DQ-reg-tbl DQ)))
    (b-if (logbit 3 (cntlv-operand cntlv))
	  (reg-ref-tag (sreg-tbl-nth (DE-ra DE0) (DQ-sreg-tbl DQ)))
	  0)))))

(defthm rob-index-p-DQ-out-tag1
    (implies (DQ-p DQ) (rob-index-p (DQ-out-tag1 DQ)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (DQ-p DQ) (integerp (DQ-out-tag1 DQ))))))

(in-theory (disable DQ-out-tag1))

; DQ-read-val1 reads the value of the first operand from the corresponding
; dispatch queue entry or register file.
(defun DQ-read-val1 (DQ MA)
  (declare (xargs :guard (and (DQ-p DQ) (MA-state-p MA))))
  (let ((RF (MA-RF MA))
	(SRF (MA-SRF MA))
	(DE0 (DQ-DE0 DQ))
	(cntlv (DE-cntlv (DQ-DE0 DQ))))
    (b-if (logbit 0 (cntlv-operand cntlv)) (read-reg (DE-ra DE0) RF)
    (b-if (logbit 1 (cntlv-operand cntlv)) (word (DE-im DE0))
    (b-if (logbit 2 (cntlv-operand cntlv)) (read-reg (DE-rc DE0) RF)
    (b-if (logbit 3 (cntlv-operand cntlv)) (read-sreg (DE-ra DE0) SRF)
	  0))))))

(defthm word-p-DQ-read-val1
    (implies (and (DQ-p DQ) (MA-state-p MA))
	     (word-p (DQ-read-val1 DQ MA))))
(in-theory (disable DQ-read-val1))

; Whether the second operand value is ready.
(defun DQ-out-ready2? (DQ)
  (declare (xargs :guard (DQ-p DQ)))
  (b-not (reg-ref-wait? (reg-tbl-nth (DE-rb (DQ-DE0 DQ))
				     (DQ-reg-tbl DQ)))))

(defthm bitp-DQ-out-ready2
    (implies (DQ-p DQ) (bitp (DQ-out-ready2? DQ))))

(in-theory (disable DQ-out-ready2?))

; The second operand register designator.
(defun DQ-out-reg2 (DQ)
  (declare (xargs :guard (DQ-p DQ)))
  (DE-rb (DQ-DE0 DQ)))

(defthm rname-p-DQ-out-reg2
    (implies (DQ-p DQ) (rname-p (DQ-out-reg2 DQ))))

(in-theory (disable DQ-out-reg2))

; Tomasulo's tag for the instruction that produces the second operand.
(defun DQ-out-tag2 (DQ)
  (declare (xargs :guard (DQ-p DQ)))
  (reg-ref-tag (reg-tbl-nth (DE-rb (DQ-DE0 DQ)) (DQ-reg-tbl DQ))))

(defthm rob-index-p-DQ-out-tag2
    (implies (DQ-p DQ) (rob-index-p (DQ-out-tag2 DQ)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (DQ-p DQ) (integerp (DQ-out-tag2 DQ))))))

(in-theory (disable DQ-out-tag2))

; Whether the third operand is ready.
(defun DQ-out-ready3? (DQ)
  (declare (xargs :guard (DQ-p DQ)))
  (b-not (reg-ref-wait? (reg-tbl-nth (DE-rc (DQ-DE0 DQ))
				     (DQ-reg-tbl DQ)))))

(defthm bitp-DQ-out-ready3
    (implies (DQ-p DQ) (bitp (DQ-out-ready3? DQ))))

(in-theory (disable DQ-out-ready3?))

; The third operand register designator.
(defun DQ-out-reg3 (DQ)
  (declare (xargs :guard (DQ-p DQ)))
  (DE-rc (DQ-DE0 DQ)))

(defthm rname-p-DQ-out-reg3
    (implies (DQ-p DQ) (rname-p (DQ-out-reg3 DQ))))

(in-theory (disable DQ-out-reg3))

; Tomasulo's tag for the instruction that produces the third operand value.
(defun DQ-out-tag3 (DQ)
  (declare (xargs :guard (DQ-p DQ)))
  (reg-ref-tag (reg-tbl-nth (DE-rc (DQ-DE0 DQ)) (DQ-reg-tbl DQ))))

(defthm rob-index-p-DQ-out-tag3
    (implies (DQ-p DQ) (rob-index-p (DQ-out-tag3 DQ)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (DQ-p DQ) (integerp (DQ-out-tag3 DQ))))))

(in-theory (disable DQ-out-tag3))

; DQ-full? is set when dispatch queue is full.  The fetching is stalled
; until DQ has an available slot.
(defun DQ-full? (DQ)
  (declare (xargs :guard (and (DQ-p DQ))))
  (DE-valid? (DQ-DE3 DQ)))

(defthm bitp-DQ-full? (implies (DQ-p DQ) (bitp (DQ-full? DQ))))
(in-theory (disable DQ-full?))

; Ready to dispatch an instruction that goes directly into the complete
; stage. E.g., an illegal instruction.
(defun DQ-ready-no-unit? (DQ)
  (declare (xargs :guard (DQ-p DQ)))
  (b-and (DE-valid? (DQ-DE0 DQ))
	 (b-ior (logbit 4 (cntlv-exunit (DE-cntlv (DQ-DE0 DQ))))
		(excpt-raised? (DE-excpt (DQ-DE0 DQ))))))

(defthm bitp-DQ-ready-no-unit (bitp (DQ-ready-no-unit? DQ)))

; Ready to dispatch to IU.
(defun DQ-ready-to-IU? (DQ)
  (declare (xargs :guard (DQ-p DQ)))
  (bs-and (DE-valid? (DQ-DE0 DQ))
	  (logbit 0 (cntlv-exunit (DE-cntlv (DQ-DE0 DQ))))
	  (b-not (excpt-raised? (DE-excpt (DQ-DE0 DQ))))))

(defthm bitp-DQ-ready-to-IU (bitp (DQ-ready-to-IU? DQ)))

; Ready to dispatch to MU.
(defun DQ-ready-to-MU? (DQ)
  (declare (xargs :guard (DQ-p DQ)))
  (bs-and (DE-valid? (DQ-DE0 DQ))
	  (logbit 1 (cntlv-exunit (DE-cntlv (DQ-DE0 DQ))))
	  (b-not (excpt-raised? (DE-excpt (DQ-DE0 DQ))))))

(defthm bitp-DQ-ready-to-MU (bitp (DQ-ready-to-MU? DQ)))

; Ready to dispatch to LSU.
(defun DQ-ready-to-LSU? (DQ)
  (declare (xargs :guard (DQ-p DQ)))
  (bs-and (DE-valid? (DQ-DE0 DQ))
	  (logbit 2 (cntlv-exunit (DE-cntlv (DQ-DE0 DQ))))
	  (b-not (excpt-raised? (DE-excpt (DQ-DE0 DQ))))))

(defthm bitp-DQ-ready-to-LSU (bitp (DQ-ready-to-LSU? DQ)))

; Ready to dispatch to BU.
(defun DQ-ready-to-BU? (DQ)
  (declare (xargs :guard (DQ-p DQ)))
  (bs-and (DE-valid? (DQ-DE0 DQ))
	  (logbit 3 (cntlv-exunit (DE-cntlv (DQ-DE0 DQ))))
	  (b-not (excpt-raised? (DE-excpt (DQ-DE0 DQ))))))

(defthm bitp-DQ-ready-to-BU (bitp (DQ-ready-to-BU? DQ)))

; If the ROB-flg is set, and ROB-head and ROB-tail are equal to each other,
; then the reorder buffer is full.
(defun ROB-full? (ROB)
  (declare (xargs :guard (ROB-p ROB)))
  (b-and (ROB-flg ROB)
	 (bv-eqv *rob-index-size* (ROB-head ROB) (ROB-tail ROB))))

(defthm bitp-ROB-full (bitp (ROB-full? ROB)))

; If the ROB-flg is unset, and ROB-head and ROB-tail are equal to each other,
; then the reorder buffer is empty.
(defun ROB-empty? (ROB)
  (declare (xargs :guard (ROB-p ROB)))
  (bs-and (b-not (ROB-flg ROB))
	  (bv-eqv *rob-index-size* (ROB-head ROB) (ROB-tail ROB))))

(defthm bitp-ROB-empty (bitp (ROB-empty? ROB)))

; The ROB entry designated by idx is empty. 
(defun robe-empty? (idx rob)
  (declare (xargs :guard (and (ROB-p ROB) (rob-index-p idx))))
  (b-not (robe-valid? (nth-robe idx rob))))

(defun robe-empty-under? (idx ROB)
  (declare (xargs :guard (and (ROB-p ROB) (integerp idx)
			      (<= 0 idx) (<= idx *rob-size*))
		  :verify-guards nil))
  (if (zp idx)
      1
      (b-and (robe-empty? (1- idx) ROB)
	     (robe-empty-under? (1- idx) ROB))))

(defthm bitp-robe-empty-under
    (bitp (robe-empty-under? idx ROB)))

(verify-guards robe-empty-under?
	       :hints (("goal" :In-theory (enable rob-index-p
						  unsigned-byte-p))))

; The ROB is empty.
(defun ROB-entries-empty? (ROB)
  (declare (xargs :guard (ROB-p ROB)))
  (robe-empty-under? *rob-size* ROB))

; There are pending write operation in the write buffer.
(defun LSU-pending-writes? (LSU)
  (declare (xargs :guard (load-store-unit-p LSU)))
  (let ((wbuf0 (LSU-wbuf0 LSU)) (wbuf1 (LSU-wbuf1 LSU)))
    (b-ior (b-and (wbuf-valid? wbuf0) (wbuf-commit? wbuf0))
	   (b-and (wbuf-valid? wbuf1) (wbuf-commit? wbuf1)))))

(defthm bitp-LSU-pending-writes (bitp (LSU-pending-writes? LSU)))

; This line coming out of ROB is raised if the ROB detects a branch
; misprediction and synchronization.  When entering an exception or leaving
; one, this line may not be raised.
(defun commit-jmp? (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (let ((LSU (MA-LSU MA)) (ROB (MA-ROB MA)))
    (let ((ROBE (nth-ROBE (ROB-head ROB) ROB)))
      (bs-and (ROBE-valid? ROBE)
	      (ROBE-complete? ROBE)
	      (b-ior (b-andc2 (ROBE-sync? ROBE)
			      (LSU-pending-writes? LSU))
		     (bs-and (ROBE-branch? ROBE)
; This line is added to be conservative.  Without it
; we don't know whether the implementation is correct.			     
			     (b-not (excpt-raised? (ROBE-excpt robe)))
			     (b-xor (ROBE-br-predict? ROBE)
				    (ROBE-br-actual? ROBE))))))))

(defthm bitp-commit-jmp (bitp (commit-jmp? MA)))
(in-theory (disable commit-jmp?))

; Enter-excpt? is raised if an internal exception is raised.
(defun enter-excpt? (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (let ((robe (nth-ROBE (ROB-head (MA-ROB MA)) (MA-ROB MA)))
	(LSU (MA-LSU MA)))
    (bs-and (ROBE-valid? robe)
	    (ROBE-complete? robe)
	    (excpt-raised? (ROBE-excpt robe))
	    (b-not (LSU-pending-writes? LSU)))))

(defthm bitp-enter-excpt (bitp (enter-excpt? MA)))
(in-theory (disable enter-excpt?))

; Ex-intr? is raised if the external exception handling starts.
(defun ex-intr? (MA sigs)
  (declare (xargs :guard (and (MA-state-p MA) (MA-input-p sigs))))
  (let ((ROB (MA-ROB MA)) (LSU (MA-LSU MA)))
    (bs-and (ROB-empty? ROB)
	    (b-not (LSU-pending-writes? LSU))
	    (b-ior (ROB-exintr? ROB)
		   (MA-input-exintr sigs)))))

(defthm bitp-ex-intr (bitp (ex-intr? MA sigs)))
(in-theory (disable ex-intr?))

; External interrupt address.
(defun ex-intr-addr (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (let ((DE0 (DQ-DE0 (MA-DQ MA))) (IFU (MA-IFU MA)) (pc (MA-pc MA)))
    (b-if (DE-valid? DE0) (DE-pc DE0)
    (b-if (IFU-valid? IFU) (IFU-pc IFU)
	  pc))))

(defthm addr-ex-intr-addr
    (implies (MA-state-p MA) (addr-p (ex-intr-addr MA)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (MA-state-p MA) (integerp (ex-intr-addr MA))))))
(in-theory (disable ex-intr-addr))

; Return from the exception handling occurs in the current cycle.
; This is true when an RFEH instruction is committed.
(defun leave-excpt? (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (let ((ROBE (nth-ROBE (ROB-head (MA-ROB MA)) (MA-ROB MA))))
    (bs-and (ROBE-valid? ROBE)
	    (ROBE-complete? ROBE)
	    (ROBE-rfeh? ROBE)
	    (b-not (LSU-pending-writes? (MA-LSU MA))))))

(defthm bitp-leave-excpt (bitp (leave-excpt? MA)))
(in-theory (disable leave-excpt?))

; If this line is raised, all entries in the pipeline are nullified.
; Flushing is usually taken when mispredicted branch, synchronization or
; an exception takes place.
(defun flush-all? (MA sigs)
  (declare (xargs :guard (and (MA-state-p MA) (MA-input-p sigs))))
  (bs-ior (commit-jmp? MA)
	  (enter-excpt? MA)
	  (ex-intr? MA sigs)
	  (leave-excpt? MA)))

(defthm bitp-flush-all (bitp (flush-all? MA sigs)))
(in-theory (disable flush-all?))

; ROB-jmp-addr outputs the destination address of a ROB caused jump.
; This is valid when commit-jmp?, enter-excpt? or ex-intr? is raised.
; When leave-excpt? is raised, pc should get its new value from SR0.
; Notice that a conditional branch that is predicted to take place but
; actually does not also cause commit-jmp?.
(defun ROB-jmp-addr (ROB MA sigs)
  (declare (xargs :guard (and (ROB-p ROB) (MA-state-p MA) (MA-input-p sigs))))
  (let ((ROBE (nth-ROBE (ROB-head ROB) ROB)))
    (b-if (ex-intr? MA sigs) #x30
    (b-if (enter-excpt? MA)
	  (logapp 4 0 (excpt-type (ROBE-excpt ROBE)))
    (b-if (bs-and (ROBE-valid? ROBE)
		  (ROBE-complete? ROBE)
		  (b-orc2 (ROBE-sync? ROBE)
			  (ROBE-br-actual? ROBE)))
	  (addr (1+ (ROBE-pc ROBE)))
    (b-if (bs-and (ROBE-valid? ROBE)
		  (ROBE-complete? ROBE)
		  (ROBE-br-actual? ROBE))
 	  (addr (ROBE-val ROBE))
	  0))))))

(defthm addr-p-rob-jmp-addr
    (implies (and (ROB-p ROB) (MA-state-p MA) (MA-input-p sigs))
	     (addr-p (ROB-jmp-addr ROB MA sigs)))
  :hints (("goal" :in-theory (e/d (addr-p logapp* unsigned-byte-p* addr
                                          logcons)
				  ;; (LOGAPP-0) ; Matt K. mod
                                  ()))))
(in-theory (disable ROB-jmp-addr))

; ROB-write-reg? is raised when ROB writes its result into the register file.
(defun ROB-write-reg? (ROB)
  (declare (xargs :guard (ROB-p ROB)))
  (let ((ROBE (nth-ROBE (ROB-head ROB) ROB)))
    (bs-and (ROBE-valid? ROBE)
	    (ROBE-complete? ROBE)
	    (ROBE-wb? ROBE)
	    (b-not (ROBE-wb-sreg? ROBE))
    	    (b-not (excpt-raised? (ROBE-excpt ROBE))))))

; ROB-write-sreg? is raised if ROB writes its result into the
; special register file.
(defun ROB-write-sreg? (ROB)
  (declare (xargs :guard (ROB-p ROB)))
  (let ((ROBE (nth-ROBE (ROB-head ROB) ROB)))
    (bs-and (ROBE-valid? ROBE)
	    (ROBE-complete? ROBE)
	    (ROBE-wb? ROBE)
	    (ROBE-wb-sreg? ROBE)
	    (b-not (excpt-raised? (ROBE-excpt ROBE))))))

; ROB-write-val returns the value to be written to the register file
; or the special register file.  When enter-excpt? is on, this bus is
; used to output the program counter value of the instruction that
; caused the raised exception or the next instruction.
(defun ROB-write-val (ROB MA)
  (declare (xargs :guard (and (ROB-p ROB) (MA-state-p MA))))
  (let ((robe (nth-ROBE (ROB-head ROB) ROB)))
    (b-if (enter-excpt? MA)
	  (b-if (bv-eqv 2 (excpt-type (ROBE-excpt robe)) 0)
		(word (1+ (ROBE-pc robe)))
		(word (ROBE-pc robe)))
	  (ROBE-val robe))))

; ROB-write-rid returns the register id to which the write-back value is
; written into.  If ROB-write-reg? is on, this designates a general register.
; If ROB-write-sreg? is on, this specifies a special register.  We assume
; that these lines are mutually exclusive.
(defun ROB-write-rid (ROB)
  (declare (xargs :guard (ROB-p ROB)))
  (ROBE-dest (nth-ROBE (ROB-head ROB) ROB)))

(defthm rname-p-rob-write-rid
    (implies (MA-state-p MA)
	     (rname-p (rob-write-rid (MA-rob MA))))
  :hints (("goal" :in-theory (enable rob-write-rid))))

(deflabel begin-IU-output-def)
; select-IU-RS0? is set if IU-RS0 is chosen as the open reservation station
; slot for the new instruction to be dispatched.
(defun select-IU-RS0? (iu)
  (declare (xargs :guard (integer-unit-p iu)))
  (b-not (RS-valid? (IU-RS0 IU))))

(defthm bitp-select-IU-rs0 (bitp (select-IU-RS0? IU)))

(defun select-IU-RS1? (iu)
  (declare (xargs :guard (integer-unit-p iu)))
  (b-and (b-not (RS-valid? (IU-RS1 IU)))
	 (RS-valid? (IU-RS0 IU))))

(defthm bitp-select-IU-rs1 (bitp (select-IU-RS1? IU)))

; If there is an available reservation station in IU, this line is raised.
(defun IU-ready? (iu)
  (declare (xargs :guard (integer-unit-p iu)))
  (b-nand (RS-valid? (IU-RS0 IU)) (RS-valid? (IU-RS1 IU))))

(defthm bitp-IU-ready? (bitp (IU-ready? IU)))

; The instruction at IU-RS0 is ready to be issued. 
(defun IU-RS0-issue-ready? (iu)
  (declare (xargs :guard (integer-unit-p iu)))
  (let ((RS0 (IU-RS0 IU)))
    (bs-and (RS-valid? RS0)
	    (RS-ready1? RS0)
	    (b-ior (RS-op RS0) (RS-ready2? RS0)))))

(defthm bitp-IU-rs0-issue-ready? (bitp (IU-RS0-issue-ready? IU)))

; The instruction at IU-RS1 is ready to be issued. 
(defun IU-RS1-issue-ready? (iu)
  (declare (xargs :guard (integer-unit-p iu)))
  (let ((RS1 (IU-RS1 IU)))
    (bs-and (RS-valid? RS1)
	    (RS-ready1? RS1)
	    (b-not (IU-RS0-issue-ready? IU))
	    (b-ior (RS-op RS1) (RS-ready2? RS1)))))

(defthm bitp-IU-rs1-issue-ready? (bitp (IU-RS1-issue-ready? IU)))

; Tomasulo's tag output form the IU.
(defun IU-output-tag (IU)
  (declare (xargs :guard (integer-unit-p IU)))
  (b-if (IU-RS0-issue-ready? IU) (RS-tag (IU-RS0 IU))
        (b-if (IU-RS1-issue-ready? IU) (RS-tag (IU-RS1 IU))
	      0)))

(defthm rob-index-p-IU-output-tag
    (implies (integer-unit-p IU)
	     (rob-index-p (IU-output-tag IU))))

; The output value signal from the integer unit.
(defun IU-output-val (IU)
  (declare (xargs :guard (and (integer-unit-p IU))))
  (let ((RS0 (IU-RS0 IU)) (RS1 (IU-RS1 IU)))
    (b-if (IU-RS0-issue-ready? IU)
	  (b-if (RS-op RS0)
		(RS-val1 RS0)
		(word (+ (RS-val1 RS0) (RS-val2 RS0))))
    (b-if (IU-RS1-issue-ready? IU)
	  (b-if (RS-op RS1)
		(RS-val1 RS1)
		(word (+ (RS-val1 RS1) (RS-val2 RS1))))
	  0))))
(deflabel end-IU-output-def)
(deftheory IU-output-def
    (definition-theory
	(set-difference-theories (universal-theory 'end-IU-output-def)
				 (universal-theory 'begin-IU-output-def))))

(deflabel begin-MU-output-def) 
; select-MU-RS0? is set if MU-RS0 is chosen as the open reservation station
; slot for the new instruction to be dispatched.
(defun select-MU-RS0? (MU)
  (declare (xargs :guard (mult-unit-p MU)))
  (b-not (RS-valid? (MU-RS0 MU))))

(defthm bitp-select-MU-RS0 (bitp (select-MU-RS0? MU)))

; MU-RS1 is selected as a holder for the MU dispatched instruction
(defun select-MU-RS1? (MU)
  (declare (xargs :guard (mult-unit-p MU)))
  (b-and (b-not (RS-valid? (MU-RS1 MU)))
	 (RS-valid? (MU-RS0 MU))))

(defthm bitp-select-MU-RS1 (bitp (select-MU-RS1? MU)))

; IF there is an available reservation station in mult-unit,
; this line is raised.
(defun MU-ready? (MU)
  (declare (xargs :guard (mult-unit-p MU)))
  (b-nand (RS-valid? (MU-RS0 MU)) (RS-valid? (MU-RS1 MU))))

(defthm bitp-MU-ready (bitp (MU-ready? MU)))

; The instruction at MU-RS0 is ready to be issued. 
(defun MU-RS0-issue-ready? (MU)
  (declare (xargs :guard (mult-unit-p MU)))
  (let ((RS0 (MU-RS0 MU)))
    (bs-and (RS-valid? RS0) (RS-ready1? RS0) (RS-ready2? RS0))))

(defthm bitp-MU-RS0-issue-ready (bitp (MU-RS0-issue-ready? MU)))

; The instruction at MU-RS1 is ready to be issued. 
(defun MU-RS1-issue-ready? (MU)
  (declare (xargs :guard (mult-unit-p MU)))
  (let ((RS1 (MU-RS1 MU)))
    (bs-and (RS-valid? RS1) (RS-ready1? RS1) (RS-ready2? RS1)
	    (b-not (MU-RS0-issue-ready? MU)))))

(defthm bitp-MU-RS1-issue-ready (bitp (MU-RS1-issue-ready? MU)))

;; We abstract away the implementation of the multiplier.
;; An actual multiplier is defined in multiplier-def.lisp.
;; We do not need the multiplier definition in the pipeline verification.
(encapsulate-impl 
    ((ML1-output (ra rb) t)
     (ML2-output (data) t)
     (ML3-output (data) t))
(local (defun ML1-output (ra rb)
	 (declare (xargs :guard (and (word-p ra) (word-p rb))))
	 (cons ra rb)))

(local (defun ML2-output (data)
	 (declare (xargs :guard (ML1-data-p data)))
	 data))

(local (defun ML3-output (data)
	 (declare (xargs :guard (ML2-data-p data)))
	 (word (* (car data) (cdr data)))))


(defthm ML-output-correct
    (implies (and (word-p ra) (word-p rb))
	     (equal (ML3-output (ML2-output (ML1-output ra rb)))
		    (word (* ra rb)))))
(defthm ML3-output-correct
    (word-p (ML3-output data)))
)
 
; Alternative definition of the multiplier. 
; We experimentally changed the definition of multiplier.  We plug in 
; the Wallace tree multiplier here.
;  If you want to use a real multiplier implementation, 
;  uncomment the following include-book command at the beginning of the file.
;      (include-book "multiplier-def")
;  

;(encapsulate nil
;(local (include-book "multiplier-proof"))

;(defthm ML-output-correct
;    (implies (and (word-p ra) (word-p rb))
;	     (equal (ML3-output (ML2-output (ML1-output ra rb)))
;		    (word (* ra rb)))))
;(defthm ML3-output-correct
;    (word-p (ML3-output data)))
;)
;(in-theory (disable ML1-output ML2-output ML3-output))

(deflabel end-MU-output-def) 
(deftheory MU-output-def
    (definition-theory
	(set-difference-theories (universal-theory 'end-MU-output-def)
				 (universal-theory 'begin-MU-output-def))))
     

(deflabel begin-bu-output-def)
; select-BU-RS0? is set if BU-RS0 is chosen as the open reservation station
; slot for the new instruction to go into.
(defun select-BU-RS0? (BU)
  (declare (xargs :guard (branch-unit-p BU)))
  (b-not (Bu-RS-valid? (BU-RS0 BU))))

(defthm bitp-select-BU-RS0? (bitp (select-BU-RS0? BU)))

; Choose RS1 of the BU as a possible slot for the dispatched instruction.
(defun select-BU-RS1? (BU)
  (declare (xargs :guard (branch-unit-p BU)))
  (b-and (b-not (BU-RS-valid? (BU-RS1 BU)))
	 (BU-RS-valid? (BU-RS0 BU))))

(defthm bitp-select-BU-RS1? (bitp (select-BU-RS1? BU)))

; IF there is an available reservation station in BU-unit,
; this line is raised.
(defun BU-ready? (BU)
  (declare (xargs :guard (branch-unit-p BU)))
  (b-nand (BU-RS-valid? (BU-RS0 BU)) (BU-RS-valid? (BU-RS1 BU))))

(defthm bitp-BU-ready (bitp (BU-ready? BU)))

; The branch instruction at RS0 is ready to be issued.
(defun BU-RS0-issue-ready? (BU)
  (declare (xargs :guard (branch-unit-p BU)))
  (let ((RS0 (BU-RS0 BU)))
    (b-and (BU-RS-valid? RS0) (BU-RS-ready? RS0))))

(defthm bitp-BU-RS0-issue-ready (bitp (BU-RS0-issue-ready? BU)))

; The branch instruction at RS1 is ready to be issued.
(defun BU-RS1-issue-ready? (BU)
  (declare (xargs :guard (branch-unit-p BU)))
  (let ((RS1 (BU-RS1 BU)))
    (bs-and (BU-RS-valid? RS1) (BU-RS-ready? RS1)
	    (b-not (BU-RS0-issue-ready? BU)))))

(defthm bitp-BU-RS1-issue-ready (bitp (BU-RS1-issue-ready? BU)))

; Tomasulo's tag output from the BU.  When an branch instruction
; is ready to complete, the tag for the instruction is put on the CDB.
(defun BU-output-tag (BU)
  (declare (xargs :guard (and (branch-unit-p BU))))
  (b-if (BU-RS0-issue-ready? BU) (BU-RS-tag (BU-RS0 BU))
        (b-if (BU-RS1-issue-ready? BU) (BU-RS-tag (BU-RS1 BU))
	      0)))

(defthm rob-index-p-BU-output-tag
    (implies (branch-unit-p BU)
	     (rob-index-p (BU-output-tag BU))))

; The output value from the BU is the branch outcome.  If the
; branch is taken, #xFFFF is output on the CDB.  0, otherwise. 
(defun BU-output-val (BU)
  (declare (xargs :guard (branch-unit-p BU)))
  (b-if (BU-RS0-issue-ready? BU)
	(b-if (bv-eqv *word-size* (BU-RS-val (BU-RS0 BU)) 0)
	      #xFFFF 0)
  (b-if (BU-RS1-issue-ready? BU)
	(b-if (bv-eqv *word-size* (BU-RS-val (BU-RS1 BU)) 0)
	      #xFFFF 0)
	0)))

(deflabel end-bu-output-def)
(deftheory BU-output-def
    (definition-theory
	(set-difference-theories (universal-theory 'end-bu-output-def)
				 (universal-theory 'begin-bu-output-def))))
			     

(deflabel begin-LSU-output-def)
; select-LSU-RS0? is set if LSU-RS0 is chosen as the open reservation
; station slot for the new instruction to be dispatched.  This value is
; valid only if LSU-ready? is 1.
(defun select-LSU-RS0? (LSU)
  (declare (xargs :guard (load-store-unit-p LSU)))
  (b-if (LSU-rs1-head? LSU)
	(LSU-RS-valid? (LSU-RS1 LSU))
	(b-not (LSU-RS-valid? (LSU-RS0 LSU)))))

(defthm bitp-select-LSU-RS0?
    (implies (load-store-unit-p LSU) (bitp (select-LSU-RS0? LSU))))
(in-theory (disable select-LSU-RS0?))

; The negation of select-LSU-RS0?.
(defun select-LSU-RS1? (LSU)
  (declare (xargs :guard (load-store-unit-p LSU)))
  (b-if (LSU-rs1-head? LSU)
	(b-not (LSU-RS-valid? (LSU-RS1 LSU)))
	(LSU-RS-valid? (LSU-RS0 LSU))))

(defthm bitp-select-LSU-RS1?
    (implies (load-store-unit-p LSU) (bitp (select-LSU-RS1? LSU))))
(in-theory (disable select-LSU-RS1?))

; If there is an available reservation station in LSU-unit,
; this line is raised.
(defun LSU-ready? (LSU)
  (declare (xargs :guard (load-store-unit-p LSU)))
  (b-if (LSU-rs1-head? LSU)
	(b-not (LSU-RS-valid? (LSU-RS0 LSU)))
	(b-not (LSU-RS-valid? (LSU-RS1 LSU)))))

(defthm bitp-LSU-ready? (bitp (LSU-ready? LSU)))
(in-theory (disable LSU-ready?))

; LSU-RS0-issue-ready? is on when the load store instruction in RS0 is
; ready to be issued.
; RS0 should be a valid and necessary operands must be ready.  Also
; the order of instruction issues are important.  If RS1 contains a
; valid instruction and the next reservation flag points to RS1, it
; means that RS1 contains an earlier instruction than RS0.
(defun LSU-RS0-issue-ready? (LSU)
  (declare (xargs :guard (load-store-unit-p LSU)))
  (let ((RS0 (LSU-RS0 LSU))
	(RS1 (LSU-RS1 LSU)))
    (bs-and (LSU-RS-valid? RS0)
	    (b-orc1 (LSU-RS-ld-st? RS0) (LSU-RS-rdy3? RS0))
	    (LSU-RS-rdy1? RS0)
	    (b-ior (LSU-RS-op RS0) (LSU-RS-rdy2? RS0))
	    (b-nand (LSU-rs1-head? LSU) (LSU-RS-valid? RS1)))))

(defthm bitp-LSU-RS0-issue-ready? (bitp (LSU-RS0-issue-ready? LSU)))
(in-theory (disable LSU-RS0-issue-ready?))

; LSU-RS1-issue-ready? is on when the load store instruction in RS1 is ready
; to be issued.
(defun LSU-RS1-issue-ready? (LSU)
  (declare (xargs :guard (load-store-unit-p LSU)))
  (let ((RS0 (LSU-RS0 LSU))
	(RS1 (LSU-RS1 LSU)))
    (bs-and (LSU-RS-valid? RS1)
	    (b-orc1 (LSU-RS-ld-st? RS1) (LSU-RS-rdy3? RS1))
	    (LSU-RS-rdy1? RS1)
	    (b-ior (LSU-RS-op RS1) (LSU-RS-rdy2? RS1))
	    (b-orc2 (LSU-rs1-head? LSU) (LSU-RS-valid? RS0)))))

(defthm bitp-LSU-RS1-issue-ready? (bitp (LSU-RS1-issue-ready? LSU)))

; If the access addresses for the load instruction in a read buffer
; and the store instruction in a write buffer match, we can use the
; stored value as the result of the load instruction.
; LSU-address-match?  is on if there is a store instruction in the
; write buffer, which has the same access address.  We also check
; rbuf-wbuf0? and rbuf-wbuf1? fields to make sure the instructions in
; the write buffer are earlier instructions.
(defun LSU-address-match? (LSU)
  (declare (xargs :guard (load-store-unit-p LSU)))
  (let ((rbuf (LSU-rbuf LSU))
	(wbuf0 (LSU-wbuf0 LSU))
	(wbuf1 (LSU-wbuf1 LSU)))
    (b-ior (bs-and (bv-eqv *addr-size* (rbuf-addr rbuf) (wbuf-addr wbuf0))
		   (rbuf-valid? rbuf)
		   (rbuf-wbuf0? rbuf)
		   (wbuf-valid? wbuf0))
	   (bs-and (bv-eqv *addr-size* (rbuf-addr rbuf) (wbuf-addr wbuf1))
		   (rbuf-valid? rbuf)
		   (rbuf-wbuf1? rbuf)
		   (wbuf-valid? wbuf1)))))

(defthm bitp-LSU-address-match (bitp (LSU-address-match? LSU)))
(in-theory (disable LSU-address-match?))

; If the addresses of load and store instruction in buffers match, we
; can use the value for the store instruction as the result of the
; load instruction. LSU-forward-wbuf associatively search the write
; buffer for the store instruction entry with a matching address, and
; returns the store value.  If there are more than one matching entry
; the value of the latest completed instruction is returned.
(defun LSU-forward-wbuf (LSU)
  (declare (xargs :guard (load-store-unit-p LSU)))
  (let ((rbuf (LSU-rbuf LSU))
	(wbuf0 (LSU-wbuf0 LSU))
	(wbuf1 (LSU-wbuf1 LSU)))
    (b-if (bs-and (bv-eqv *addr-size* (rbuf-addr rbuf) (wbuf-addr wbuf1))
		  (wbuf-valid? wbuf1)
		  (rbuf-wbuf1? rbuf))
	  (wbuf-val wbuf1)
    (b-if (bs-and (bv-eqv *addr-size* (rbuf-addr rbuf) (wbuf-addr wbuf0))
		  (wbuf-valid? wbuf0)
		  (rbuf-wbuf0? rbuf))
	  (wbuf-val wbuf0)
	  0))))

; A memory stall occurs when the memory system does not respond for some
; reasons.  We don't model cache system or memory controller at all.
; Instead we give a very simplistic view of memory, which does or does
; not respond to the memory access request nondeterministicly.
; LSU-read-stall? can be set only when the LSU-rbuf1 is occupied.
; LSU-read-stall? does not indicate that the read address violates the
; memory protection, or there is an read-write address match with
; a write buffer entry.
(defun LSU-read-stall? (LSU sigs)
  (declare (xargs :guard (and (load-store-unit-p LSU) (MA-input-p sigs))))
  (b-andc2 (rbuf-valid? (LSU-rbuf LSU))
	   (MA-input-data sigs)))

(defthm bitp-LSU-read-stall? (bitp (LSU-read-stall? LSU sigs)))
(in-theory (disable LSU-read-stall?))

; When the read address is prohibited by the memory protection mechanism,
; this line is raised.  If the machine is in the supervisor-mode, the
; error is not raised.
(defun LSU-read-prohibited? (LSU mem su)
  (declare (xargs :guard (and (load-store-unit-p LSU) (mem-p mem)
			      (bitp su))))
  (b-nor (readable-addr? (rbuf-addr (LSU-rbuf LSU)) mem) su))

(defthm bitp-LSU-read-prohibited? (bitp (LSU-read-prohibited? LSU mem su)))
(in-theory (disable LSU-read-prohibited?))

  
; If the write buffer entry at wbuf0 is valid, but not yet completed,
; we may be ready to check its address and complete the instruction.
; The actual memory access takes place after the store instruction commits.
; check-wbuf0? is on when the entry is actually sent to next latch
; to complete.
(defun check-wbuf0? (LSU)
  (declare (xargs :guard (load-store-unit-p LSU)))
  (bs-and (wbuf-valid? (LSU-wbuf0 LSU))
	  (b-not (wbuf-complete? (LSU-wbuf0 LSU)))))

(defthm bitp-check-wbuf0? (bitp (check-wbuf0? LSU)))
(in-theory (disable check-wbuf0?))

(defun check-wbuf1? (LSU)
  (declare (xargs :guard (load-store-unit-p LSU)))
  (bs-and (wbuf-valid? (LSU-wbuf1 LSU))
	  (b-not (wbuf-complete? (LSU-wbuf1 LSU)))
	  (b-not (check-wbuf0? LSU))))

(defthm bitp-check-wbuf1? (bitp (check-wbuf1? LSU)))
(in-theory (disable check-wbuf1?))

; We release the read operation, if no memory permission check is done
; for the write operations during this cycle, and read operation can
; be done during this cycle.  Memory read operation can be completed
; during this cycle if either one of write operation has the same access
; address as the read operation, memory protection is violated by the
; read operation, or memory read can be carried out without stall.
(defun release-rbuf? (LSU MA sigs)
  (declare (xargs :guard (and (load-store-unit-p LSU) (MA-state-p MA)
			      (MA-input-p sigs))))
  (bs-and (rbuf-valid? (LSU-rbuf LSU))
	  (b-not (check-wbuf0? LSU))
	  (b-not (check-wbuf1? LSU))
	  (bs-ior (LSU-address-match? LSU)
		  (LSU-read-prohibited? LSU (MA-mem MA) (SRF-su (MA-SRF MA)))
		  (b-not (LSU-read-stall? LSU sigs)))))
(defthm bitp-release-rbuf?
    (bitp (release-rbuf? LSU MA sigs)))
(in-theory (disable release-rbuf?))

; If the store instruction at the head of the write buffer has committed
; and we are ready to write the value to the memory, release-wbuf0-ready?
; is set.
(defun release-wbuf0-ready? (LSU)
  (declare (xargs :guard (load-store-unit-p LSU)))
  (let ((wbuf0 (LSU-wbuf0 LSU)))
    (b-and (wbuf-valid? wbuf0) (wbuf-commit? wbuf0))))

(defthm bitp-release-wbuf0-ready? (bitp (release-wbuf0-ready? LSU)))
(in-theory (disable release-wbuf0-ready?))

; LSU-write-stall? is set when a write buffer entry tries to write its result
; to the memory and the memory does not respond.  It is only set when
; Release-wbuf0-ready? is on.
(defun LSU-write-stall? (LSU sigs)
  (declare (xargs :guard (and (load-store-unit-p LSU) (MA-input-p sigs))))
  (b-andc2 (release-wbuf0-ready? LSU) (MA-input-data sigs)))

(defthm bitp-LSU-write-stall? (bitp (LSU-write-stall? LSU sigs)))
(in-theory (disable LSU-write-stall?))

; Write operation is performed and the instruction is released.
; Memory operations are done in this priority.
;  1 Write operation memory protection check
;  2 Read operation
;  3 Write operation.
; Thus write operation is done only when no read operation is pending, 
; and the no protection check for any write operation is pending.
; The write operation memory check has a higher priority than
; the read operation.  Using the load-bypassing, a read operation
; may steal a value from a write operation, that may in the future cause
; an exception. 
(defun release-wbuf0? (LSU sigs)
  (declare (xargs :guard (and (load-store-unit-p LSU) (MA-input-p sigs))))
  (bs-and (release-wbuf0-ready? LSU)
	  (b-not (LSU-write-stall? LSU sigs))
	  (b-not (rbuf-valid? (LSU-rbuf LSU)))
	  (b-not (check-wbuf1? LSU))))

(defthm bitp-release-wbuf0? (bitp (release-wbuf0? LSU sigs)))
(in-theory (disable release-wbuf0?))

; If the memory access is prohibited by the memory system,
; LSU-write-prohibited? is raised.  This is valid only when
; check-wbuf0? or check-wbuf1? is on.  The instruction in the corresponding
; write buffer entry causes the write address violation.
(defun LSU-write-prohibited? (LSU mem su)
  (declare (xargs :guard (and (load-store-unit-p LSU) (mem-p mem) (bitp su))))
  (b-if (check-wbuf0? LSU)
	(b-nor (writable-addr? (wbuf-addr (LSU-wbuf0 LSU)) mem) su)
  (b-if (check-wbuf1? LSU)
	(b-nor (writable-addr? (wbuf-addr (LSU-wbuf1 LSU)) mem) su)
	0)))

(defthm bitp-LSU-write-prohibited? (bitp (LSU-write-prohibited? LSU mem su)))
(in-theory (disable LSU-write-prohibited?))
(deflabel end-LSU-output-def)
(deftheory LSU-output-def
    (definition-theory
	(set-difference-theories (universal-theory 'end-LSU-output-def)
				 (universal-theory 'begin-LSU-output-def))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Dispatching of instructions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Dispatching an instruction that completes immediately.
(defun dispatch-no-unit? (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (bs-and (DQ-ready-no-unit? (MA-DQ MA))
	  (b-not (ROB-full? (MA-ROB MA)))
	  (b-not (ROB-exintr? (MA-ROB MA)))))

(defthm bitp-dispatch-no-unit? (bitp (dispatch-no-unit? MA)))
(in-theory (disable dispatch-no-unit?))

; Dispatching an instruction to the IU.
(defun dispatch-to-IU? (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (bs-and (DQ-ready-to-IU? (MA-DQ MA))
	  (b-not (ROB-full? (MA-ROB MA)))
	  (b-not (ROB-exintr? (MA-ROB MA)))
	  (IU-ready? (MA-IU MA))))

(defthm bitp-dispatch-to-IU (bitp (dispatch-to-IU? MA)))
(in-theory (disable dispatch-to-IU?))

; Dispatching an instruction to the MU.
(defun dispatch-to-MU? (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (bs-and (DQ-ready-to-MU? (MA-DQ MA))
	  (b-not (ROB-full? (MA-ROB MA)))
	  (b-not (ROB-exintr? (MA-ROB MA)))
	  (MU-ready? (MA-MU MA))))

(defthm bitp-dispatch-to-MU (bitp (dispatch-to-MU? MA)))
(in-theory (disable dispatch-to-MU?))

; Dispatching an instruction to the LSU.
(defun dispatch-to-LSU? (MA)
  (declare (xargs :guard  (MA-state-p MA)))
  (bs-and (DQ-ready-to-LSU? (MA-DQ MA))
	  (b-not (ROB-full? (MA-ROB MA)))
	  (b-not (ROB-exintr? (MA-ROB MA)))
	  (LSU-ready? (MA-LSU MA))))

(defthm bitp-dispatch-to-LSU? (bitp (dispatch-to-LSU? MA)))
(in-theory (disable dispatch-to-LSU?))

; Dispatching an instruction to the BU.
(defun dispatch-to-BU? (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (bs-and (DQ-ready-to-BU? (MA-DQ MA))
	  (b-not (ROB-full? (MA-ROB MA)))
	  (b-not (ROB-exintr? (MA-ROB MA)))
	  (BU-ready? (MA-BU MA))))

(defthm bitp-dispatch-to-BU (bitp (dispatch-to-BU? MA)))
(in-theory (disable dispatch-to-BU?))

; This line is raised if any instruction is ready to dispatch.
; A dispatch actually takes place if the corresponding execution
; unit has an empty reservation station.
(defun dispatch-inst? (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (bs-ior (dispatch-no-unit? MA)
	  (dispatch-to-IU? MA)
	  (dispatch-to-MU? MA)
	  (dispatch-to-LSU? MA)
	  (dispatch-to-BU? MA)))

(defthm bitp-dispatch-inst? (bitp (dispatch-inst? MA)))
(in-theory (disable dispatch-inst?))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Common Data Bus Arbitration
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deflabel begin-CDB-arb-def)

; The CDB is ready for the output from the LSU.
(defun CDB-for-LSU? (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (LSU-latch-valid? (LSU-lch (MA-LSU MA))))

; The CDB is ready for the output from the MU.
(defun CDB-for-MU? (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (bs-and (b-not (CDB-for-LSU? MA))
	  (MU-latch2-valid? (MU-lch2 (MA-MU MA)))))

; The CDB is ready for the output from the BU.
(defun CDB-for-BU? (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (bs-and (b-not (CDB-for-LSU? MA))
	  (b-not (CDB-for-MU? MA))
	  (b-ior (BU-RS0-issue-ready? (MA-BU MA))
		 (BU-RS1-issue-ready? (MA-BU MA)))))

; The CDB is ready for the output from the IU.
(defun CDB-for-IU? (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (bs-and (b-not (CDB-for-LSU? MA))
	  (b-not (CDB-for-BU? MA))
	  (b-not (CDB-for-MU? MA))
	  (b-ior (IU-RS0-issue-ready? (MA-IU MA))
		 (IU-RS1-issue-ready? (MA-IU MA)))))
(deflabel end-CDB-arb-def)

(defthm bitp-CDB-for-LSU  (implies (MA-state-p MA) (bitp (CDB-for-LSU? MA))))
(defthm bitp-CDB-for-MU  (bitp (CDB-for-MU? MA)))
(defthm bitp-CDB-for-BU  (bitp (CDB-for-BU? MA)))
(defthm bitp-CDB-for-IU  (bitp (CDB-for-IU? MA)))

(deftheory CDB-arb-def
    (set-difference-theories (universal-theory 'end-CDB-arb-def)
			     (universal-theory 'begin-CDB-arb-def)))
(in-theory (disable CDB-arb-def))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Definition of the issues of instructions at each execution unit.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; issue-IU-RS0 and issue-IU-RS1 are set if the instruction in the
; corresponding reservation station is issued to the execution unit.
; Otherwise, cleared.  Notice issue-IU-RS0? is on, RS-valid? for RS0 is on.
; Similarly with RS1.
(deflabel begin-issue-logic-def)
(defun issue-IU-RS0? (iu MA)
  (declare (xargs :guard (and (integer-unit-p iu) (MA-state-p MA))))
  (b-and (IU-RS0-issue-ready? IU) (CDB-for-IU? MA)))

(defthm bitp-issue-IU-RS0  (bitp (issue-IU-RS0? IU MA)))

(defun issue-IU-RS1? (iu MA)
  (declare (xargs :guard (and (integer-unit-p iu) (MA-state-p MA))))
  (bs-and (IU-RS1-issue-ready? IU) (CDB-for-IU? MA)))

(defthm bitp-issue-IU-RS1 (bitp (issue-IU-RS1? IU MA)))

(defun issue-MU-RS0? (MU MA)
  (declare (xargs :guard (and (mult-unit-p MU) (MA-state-p MA))))
  (b-and (MU-RS0-issue-ready? MU)
	 (bs-ior (CDB-for-MU? MA)
		 (b-not (MU-latch1-valid? (MU-lch1 MU)))
		 (b-not (MU-latch2-valid? (MU-lch2 MU))))))

(defthm bitp-issue-MU-RS0 (bitp (issue-MU-RS0? MU MA)))

(defun issue-MU-RS1? (MU MA)
  (declare (xargs :guard (and (mult-unit-p MU) (MA-state-p MA))))
  (bs-and (MU-RS1-issue-ready? MU)
	  (bs-ior (CDB-for-MU? MA)
		  (b-not (MU-latch1-valid? (MU-lch1 MU)))
		  (b-not (MU-latch2-valid? (MU-lch2 MU))))))

(defthm bitp-issue-MU-RS1 (bitp (issue-MU-RS1? MU MA)))

(defun issue-BU-RS0? (BU MA)
  (declare (xargs :guard (and (branch-unit-p BU) (MA-state-p MA))))
  (b-and (BU-RS0-issue-ready? BU) (CDB-for-BU? MA)))

(defthm bitp-issue-BU-RS0? (bitp (issue-BU-RS0? BU MA)))

(defun issue-BU-RS1? (BU MA)
  (declare (xargs :guard (and (branch-unit-p BU) (MA-state-p MA))))
  (b-and (BU-RS1-issue-ready? BU) (CDB-for-BU? MA)))

(defthm bitp-issue-BU-RS1 (bitp (issue-BU-RS1? BU MA)))

(defun issue-LSU-RS0? (LSU MA sigs)
  (declare (xargs :guard (and (load-store-unit-p LSU) (MA-state-p MA)
			      (MA-input-p sigs))))
  (bs-and (LSU-RS0-issue-ready? LSU)
	  (b-if (LSU-RS-ld-st? (LSU-RS0 LSU))
		(b-ior (b-not (wbuf-valid? (LSU-wbuf1 LSU)))
		       (release-wbuf0? LSU sigs))
		(bs-ior (b-not (rbuf-valid? (LSU-rbuf LSU)))
			(release-rbuf? LSU MA sigs)))))

(defthm bitp-issue-LSU-RS0? (bitp (issue-LSU-RS0? LSU MA sigs)))
(in-theory (disable issue-LSU-RS0?))

(defun issue-LSU-RS1? (LSU MA sigs)
  (declare (xargs :guard (and (load-store-unit-p LSU)
			      (MA-state-p MA) (MA-input-p sigs))))
  (bs-and (LSU-RS1-issue-ready? LSU)
	  (b-if (LSU-RS-ld-st? (LSU-RS1 LSU))
		(b-ior (b-not (wbuf-valid? (LSU-wbuf1 LSU)))
		       (release-wbuf0? LSU sigs))
		(bs-ior (b-not (rbuf-valid? (LSU-rbuf LSU)))
			(release-rbuf? LSU MA sigs)))))

(defthm bitp-issue-LSU-RS1? (bitp (issue-LSU-RS1? LSU MA sigs)))
(in-theory (disable issue-LSU-RS1?))

(deflabel end-issue-logic-def)

(deftheory issue-logic-def
    (definition-theory
	(set-difference-theories (universal-theory 'end-issue-logic-def)
				 (universal-theory 'begin-issue-logic-def))))

(deflabel begin-CDB-out-def)
; Common Data Bus should raise ready? flag when a datum is ready.
; CDB-tag posts the destination ROB entry index (or what we call Tomasulo's
; tag), while CDB-val is the result of the executed instruction.
(defun CDB-ready? (MA)
  (declare (xargs :guard  (MA-state-p MA)))
  (bs-ior (LSU-latch-valid? (LSU-lch (MA-LSU MA)))
	  (MU-latch2-valid? (MU-lch2 (MA-MU MA)))
	  (BU-RS0-issue-ready? (MA-BU MA))
	  (BU-RS1-issue-ready? (MA-BU MA))
	  (IU-RS0-issue-ready? (MA-IU MA))
	  (IU-RS1-issue-ready? (MA-IU MA))))

(defthm bitp-CDB-ready   (bitp (CDB-ready? MA)))
(in-theory (disable CDB-ready?))

; Tomasulo's tag, i.e., the index to the ROB entry to which the completing
; instruction is assigned to is put on the tag signal of the CDB.
(defun CDB-tag (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (b-if (CDB-for-IU? MA)
	(IU-output-tag (MA-IU MA))
  (b-if (CDB-for-BU? MA)
	(BU-output-tag (MA-BU MA))
  (b-if (CDB-for-MU? MA)
	(MU-latch2-tag (MU-lch2 (MA-MU MA)))
  (b-if (CDB-for-LSU? MA)
	(LSU-latch-tag (LSU-lch (MA-LSU MA)))
	0)))))

(defthm rob-index-p-CDB-tag
    (implies (MA-state-p MA) (rob-index-p (CDB-tag MA)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (MA-state-p MA) (integerp (CDB-tag MA))))))

(in-theory (disable CDB-tag))

; The exception flag for the completing instruction is put on the CDB.
(defun CDB-excpt (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (b-if (CDB-for-LSU? MA) (LSU-latch-excpt (LSU-lch (MA-LSU MA))) 0))

(defthm excpt-flags-p-CDB-excpt
    (implies (MA-state-p MA) (excpt-flags-p (CDB-excpt MA))))
(in-theory (disable CDB-excpt))

; The result of the completing instruction is put on the val signal of the
; CDB.  For branch instructions, see BU-output-val.
(defun CDB-val (MA)
  (declare (xargs :guard  (MA-state-p MA)))
  (b-if (CDB-for-IU? MA)
	(IU-output-val (MA-IU MA))
  (b-if (CDB-for-BU? MA)
	(BU-output-val (MA-BU MA))
  (b-if (CDB-for-MU? MA)
	(ML3-output (MU-latch2-data (MU-lch2 (MA-MU MA))))
  (b-if (CDB-for-LSU? MA)
	(LSU-latch-val (LSU-lch (MA-LSU MA)))
	0)))))

(defthm word-p-CDB-val
    (implies (MA-state-p MA) (word-p (CDB-val MA)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (MA-state-p MA) (integerp (CDB-val MA)))
	     :hints (("Goal" :in-theory (enable word-p))))))
(in-theory (disable CDB-val))

; The CDB is ready for the instruction which is assigned to the ROB entry
; idx.
(defun CDB-ready-for? (idx MA)
  (declare (xargs :guard (and (rob-index-p idx) (MA-state-p MA))))
  (b-and (CDB-ready? MA)
	 (bv-eqv *rob-index-size* idx (CDB-tag MA))))

(defthm bitp-CDB-ready-for (bitp (CDB-ready-for? idx MA)))
(in-theory (disable CDB-ready-for?))

(deflabel end-CDB-out-def)
(deftheory CDB-out-def
    (definition-theory
	(set-difference-theories (universal-theory 'end-CDB-out-def)
				 (universal-theory 'begin-CDB-out-def))))

(deftheory CDB-def
    (union-theories (theory 'CDB-out-def)
		    (theory 'CDB-arb-def)))

; The control vector of the dispatched instruction.
(defun dispatch-cntlv (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (DE-cntlv (DQ-DE0 (MA-DQ MA))))

(defthm cntlv-p-dispatch-cntlv
    (implies (MA-state-p MA) (cntlv-p (dispatch-cntlv MA)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (MA-state-p MA) (integerp (dispatch-cntlv MA)))
	     :hints (("Goal" :in-theory (enable cntlv-p))))))
(in-theory (disable dispatch-cntlv))

; Destination register of the dispatched instruction. 
(defun dispatch-dest-reg (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (DQ-out-dest-reg (MA-DQ MA)))

(defthm rname-p-dispatch-dest-reg
    (implies (MA-state-p MA) (rname-p (dispatch-dest-reg MA)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (MA-state-p MA) (integerp (dispatch-dest-reg MA)))
	     :hints (("Goal" :in-theory (enable rname-p))))))
(in-theory (disable dispatch-dest-reg))

; The exception condition of the dispatched instruction.
(defun dispatch-excpt (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (DE-excpt (DQ-DE0 (MA-DQ MA))))

(defthm excpt-flags-p-dispatch-excpt
    (implies (MA-state-p MA) (excpt-flags-p (dispatch-excpt MA))))
(in-theory (disable dispatch-excpt))

; The program counter of the dispatched instruction.
(defun dispatch-pc (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (DE-pc (DQ-DE0 (MA-DQ MA))))

(defthm addr-p-dispatch-pc
    (implies (MA-state-p MA) (addr-p (dispatch-pc MA))))
(in-theory (disable dispatch-pc))

; Source value 1 is ready for the dispatched instruction.
(defun dispatch-ready1? (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (bs-ior (DQ-out-ready1? (MA-DQ MA))
	  (ROBE-complete? (nth-ROBE (DQ-out-tag1 (MA-DQ MA)) (MA-ROB MA)))
	  (CDB-ready-for? (DQ-out-tag1 (MA-DQ MA)) MA)))

(defthm bitp-dispatch-ready1? (bitp (dispatch-ready1? MA)))
(in-theory (disable dispatch-ready1?))

; The source operand for a dispatched instruction come from three possible
; sources: the register file, ROB and CDB.  If DQ-out-ready2 line is
; on, the value stored in the register file is the correct value.  If
; the complete? flag of the corresponding ROB entry is on, the correct
; value is redirected from the ROB entry.  If the CDB outputs the result
; of an instruction on which the dispatched instruction truly
; depends, the value on CDB is read.  Otherwise, the source operand is not
; ready.
(defun dispatch-val1 (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (b-if (DQ-out-ready1? (MA-DQ MA))
	(DQ-read-val1 (MA-DQ MA) MA)
	(b-if (ROBE-complete? (nth-ROBE (DQ-out-tag1 (MA-DQ MA)) (MA-ROB MA)))
	      (ROBE-val (nth-ROBE (DQ-out-tag1 (MA-DQ MA)) (MA-ROB MA)))
	      (b-if (CDB-ready-for? (DQ-out-tag1 (MA-DQ MA)) MA)
		    (CDB-val MA)
		    0))))

(defthm word-p-dispatch-val1
    (implies (MA-state-p MA) (word-p (dispatch-val1 MA))))
(in-theory (disable dispatch-val1))

;  Tomasulo's tag for the producer instruction of the source operand 1.
(defun dispatch-src1 (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (DQ-out-tag1 (MA-DQ MA)))

(defthm rob-index-p-dispatch-src1
    (implies (MA-state-p MA) (rob-index-p (dispatch-src1 MA))))
(in-theory (disable dispatch-src1))

; Source operand 2 is ready.
(defun dispatch-ready2? (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (bs-ior (DQ-out-ready2? (MA-DQ MA))
	  (ROBE-complete? (nth-ROBE (DQ-out-tag2 (MA-DQ MA)) (MA-ROB MA)))
	  (CDB-ready-for? (DQ-out-tag2 (MA-DQ MA)) MA)))

(defthm bitp-dispatch-ready2  (bitp (dispatch-ready2? MA)))
(in-theory (disable dispatch-ready2?))

; The value for a dispatched instruction come from three possible sources:
; the register file, ROB and CDB.  If DQ-out-ready2 line is on, the value
; stored in the register file is the correct value.  Otherwise, we have to
; get the value from the ROB entry or the CDB.  See dispatch-val1.
(defun dispatch-val2 (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (b-if (DQ-out-ready2? (MA-DQ MA))
	(read-reg (DQ-out-reg2 (MA-DQ MA)) (MA-RF MA))
	(b-if (ROBE-complete? (nth-ROBE (DQ-out-tag2 (MA-DQ MA)) (MA-ROB MA)))
	      (ROBE-val (nth-ROBE (DQ-out-tag2 (MA-DQ MA)) (MA-ROB MA)))
	      (b-if (CDB-ready-for? (DQ-out-tag2 (MA-DQ MA)) MA)
		    (CDB-val MA)
		    0))))

(defthm word-p-dispatch-val2
    (implies (MA-state-p MA) (word-p (dispatch-val2 MA))))
(in-theory (disable dispatch-val2))

; Tomasulo's tag for the producer instruction for the source operand 2.
(defun dispatch-src2 (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (DQ-out-tag2 (MA-DQ MA)))

(defthm rob-index-p-dispatch-src2
    (implies (MA-state-p MA) (rob-index-p (dispatch-src2 MA))))
(in-theory (disable dispatch-src2))

; Source operand 3 is ready.
(defun dispatch-ready3? (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (bs-ior (DQ-out-ready3? (MA-DQ MA))
	  (ROBE-complete? (nth-ROBE (DQ-out-tag3 (MA-DQ MA)) (MA-ROB MA)))
	  (CDB-ready-for? (DQ-out-tag3 (MA-DQ MA)) MA)))

(defthm bitp-dispatch-ready3 (bitp (dispatch-ready3? MA)))
(in-theory (disable dispatch-ready3?))

; Source operand 3 for the dispatched instruction, if ready.  See
; dispatch-val1.
(defun dispatch-val3 (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (b-if (DQ-out-ready3? (MA-DQ MA))
	(read-reg (DQ-out-reg3 (MA-DQ MA)) (MA-RF MA))
	(b-if (ROBE-complete? (nth-ROBE (DQ-out-tag3 (MA-DQ MA)) (MA-ROB MA)))
	      (ROBE-val (nth-ROBE (DQ-out-tag3 (MA-DQ MA)) (MA-ROB MA)))
        (b-if (CDB-ready-for? (DQ-out-tag3 (MA-DQ MA)) MA)
	      (CDB-val MA)
	      0))))

(defthm word-p-dispatch-val3
    (implies (MA-state-p MA) (word-p (dispatch-val3 MA))))
(in-theory (disable dispatch-val3))

; Tomasulo's tag for the producer instruction for the source operand 3.
(defun dispatch-src3 (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (DQ-out-tag3 (MA-DQ MA)))

(defthm rob-index-p-dispatch-src3
    (implies (MA-state-p MA) (rob-index-p (dispatch-src3 MA))))
(in-theory (disable dispatch-src3))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  Step functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deflabel begin-MA-step-functions)
; The next state of pc.
(defun step-pc (MA sigs)
  (declare (xargs :guard (and (MA-state-p MA) (MA-input-p sigs))))
  (b-if (b-ior (enter-excpt? MA)
	       (ex-intr? MA sigs))
	(rob-jmp-addr (MA-ROB MA) MA sigs)
  (b-if (leave-excpt? MA) (addr (SRF-sr0 (MA-SRF MA)))
  (b-if	(commit-jmp? MA) (rob-jmp-addr (MA-ROB MA) MA sigs)
  (b-if (b-andc2 (IFU-branch-predict? (MA-IFU MA) MA sigs)
		 (DQ-full? (MA-DQ MA)))
	(IFU-branch-target (MA-IFU MA))
  (b-if (b-and (b-nand (IFU-valid? (MA-IFU MA)) (DQ-full? (MA-DQ MA)))
	       (MA-input-fetch sigs))
	(addr (1+ (MA-pc MA)))
	(MA-pc MA)))))))

(defthm addr-p-step-pc
    (implies (and (MA-state-p MA) (MA-input-p sigs))
	     (addr-p (step-pc MA sigs))))
(in-theory (disable step-pc))

; The next state of register file.
(defun step-RF (MA)
  (declare (xargs :guard (and (MA-state-p MA))))
  (b-if (ROB-write-reg? (MA-ROB MA))
	(write-reg (ROB-write-val (MA-ROB MA) MA)
		   (ROB-write-rid (MA-ROB MA))
		   (MA-RF MA))
	(MA-RF MA)))

(defthm RF-p-step-RF
    (implies (MA-state-p MA)
	     (RF-p (step-RF MA))))
(in-theory (disable step-RF))

; The next state of the special register.
(defun step-SRF (MA sigs)
  (declare (xargs :guard (and (MA-state-p MA) (MA-input-p sigs))))
  (b-if (ex-intr? MA sigs)
	(SRF 1 (word (ex-intr-addr MA)) (word (SRF-su (MA-SRF MA))))
  (b-if (enter-excpt? MA)
	(SRF 1 (ROB-write-val (MA-ROB MA) MA)
	       (word (SRF-su (MA-SRF MA))))
  (b-if (leave-excpt? MA)
	(update-SRF (MA-SRF MA) :su (logcar (SRF-sr1 (MA-SRF MA))))
  (b-if (ROB-write-sreg? (MA-ROB MA))
	(write-sreg (ROB-write-val (MA-ROB MA) MA)
		    (ROB-write-rid (MA-ROB MA))
		    (MA-SRF MA))
	(MA-SRF MA))))))

(defthm SRF-p-step-SRF
    (implies (and (MA-state-p MA) (MA-input-p sigs))
	     (SRF-p (step-SRF MA sigs))))
(in-theory (disable step-SRF))

; The next state of the IFU.
(defun step-IFU (MA sigs)
  (declare (xargs :guard (and (MA-state-p MA) (MA-input-p sigs))))
  ; If the IFU and DQ are full, the instruction at IFU stalls. 
  (b-if (b-and (IFU-valid? (MA-IFU MA)) (DQ-full? (MA-DQ MA)))
	(update-IFU (MA-IFU MA)
		    :valid? (b-not (flush-all? MA sigs)))
  ; If instruction fetch error occurs, an instruction word is 0.
  ; This instruction will eventually raise a fetch error exception.
  (b-if (IFU-fetch-prohibited? (MA-pc MA) (MA-mem MA) (SRF-su (MA-SRF MA)))
	(IFU (b-nor (IFU-branch-predict? (MA-IFU MA) MA sigs)
		    (flush-all? MA sigs))
	     #b101 (MA-pc MA) 0)
  ; If the memory does respond, we fetch an instruction.	
  (b-if (MA-input-fetch sigs)
	(IFU (b-nor (IFU-branch-predict? (MA-IFU MA) MA sigs)
		    (flush-all? MA sigs))
	     0 (MA-pc MA) (read-mem (MA-pc MA) (MA-mem MA)))
  ; If no memory response returns, we don't fetch an instruction.	
	(IFU 0 0 0 0)))))

(defthm IFU-p-step-IFU
    (implies (and (MA-state-p MA) (MA-input-p sigs))
	     (IFU-p (step-IFU MA sigs))))
(in-theory (disable step-IFU))

(defun step-BP (MA sigs)
  (declare (xargs :guard (and (MA-state-p MA) (MA-input-p sigs)))
; Matt K. mod: Added necessary ignorable declaration.
           (ignorable sigs))
  (BP (step-BP-seed MA)))

;  The definition of step-DQ.
;   The dispatch queue is a FIFO buffer.  Unlike the ROB, we tried to
;   implemented like a systolic buffer.  (I am not sure whether this
;   word applies.)  An entry passes to the next entry when an instruction
;   is dispatched.  For instance, the content of DE3 is passed to DE2,
;   the content of DE2 is passed to DE1.  DE?-out is the value passed to the
;   next entry.
(defun DE3-out (DQ MA sigs)
  (declare (xargs :guard (and (DQ-p DQ) (MA-state-p MA) (MA-input-p sigs))))
  (b-if (DE-valid? (DQ-DE3 DQ))
	(DQ-DE3 DQ)
	(decode-output (MA-IFU MA) MA sigs)))

(defthm dispatch-entry-p-DE3-out
    (implies (and (DQ-p DQ) (MA-state-p MA) (MA-input-p sigs))
	     (dispatch-entry-p (DE3-out DQ MA sigs))))

(in-theory (disable DE3-out))

(defun DE2-out (DQ MA sigs)
  (declare (xargs :guard (and (DQ-p DQ) (MA-state-p MA) (MA-input-p sigs))))
  (b-if (DE-valid? (DQ-DE2 DQ))
	(DQ-DE2 DQ)
	(DE3-out DQ MA sigs)))

(defthm dispatch-entry-p-DE2-out
    (implies (and (DQ-p DQ) (MA-state-p MA) (MA-input-p sigs))
	     (dispatch-entry-p (DE2-out DQ MA sigs))))

(in-theory (disable DE2-out))

(defun DE1-out (DQ MA sigs)
  (declare (xargs :guard (and (DQ-p DQ) (MA-state-p MA) (MA-input-p sigs))))
  (b-if (DE-valid? (DQ-DE1 DQ))
	(DQ-DE1 DQ)
	(DE2-out DQ MA sigs)))

(defthm dispatch-entry-p-DE1-out
    (implies (and (DQ-p DQ) (MA-state-p MA) (MA-input-p sigs))
	     (dispatch-entry-p (DE1-out DQ MA sigs))))

(in-theory (disable DE1-out))

; The next state of the DE0.
(defun step-DE0 (DQ MA sigs)
  (declare (xargs :guard (and (DQ-p DQ) (MA-state-p MA) (MA-input-p sigs))))
  (b-if (b-orc1 (DE-valid? (DQ-DE0 DQ)) (dispatch-inst? MA))
	(update-dispatch-entry (DE1-out DQ MA sigs)
		   :valid? (b-andc2 (DE-valid? (DE1-out DQ MA sigs))
				    (flush-all? MA sigs)))
	(update-dispatch-entry (DQ-DE0 DQ)
		   :valid? (b-andc2 (DE-valid? (DQ-DE0 DQ))
				    (flush-all? MA sigs)))))

; The next state of the DE1.
(defun step-DE1 (DQ MA sigs)
  (declare (xargs :guard (and (DQ-p DQ) (MA-state-p MA) (MA-input-p sigs))))
  (b-if (b-ior (b-and (DE-valid? (DQ-DE1 DQ)) (dispatch-inst? MA))
	       (bs-and (b-not (DE-valid? (DQ-DE1 DQ)))
		       (DE-valid? (DQ-DE0 DQ))
		       (b-not (dispatch-inst? MA))))
	(update-dispatch-entry (DE2-out DQ MA sigs)
		   :valid? (b-andc2 (DE-valid? (DE2-out DQ MA sigs))
				    (flush-all? MA sigs)))
	(update-dispatch-entry (DQ-DE1 DQ)
		   :valid? (b-andc2 (DE-valid? (DQ-DE1 DQ))
				    (flush-all? MA sigs)))))

; The next state of the DE2.
(defun step-DE2 (DQ MA sigs)
  (declare (xargs :guard (and (DQ-p DQ) (MA-state-p MA) (MA-input-p sigs))))
  (b-if (b-ior (b-and (DE-valid? (DQ-DE2 DQ)) (dispatch-inst? MA))
	       (bs-and (b-not (DE-valid? (DQ-DE2 DQ)))
		       (DE-valid? (DQ-DE1 DQ))
		       (b-not (dispatch-inst? MA))))
	(update-dispatch-entry (DE3-out DQ MA sigs)
		   :valid? (b-andc2 (DE-valid? (DE3-out DQ MA sigs))
				    (flush-all? MA sigs)))
	(update-dispatch-entry (DQ-DE2 DQ)
		   :valid? (b-andc2 (DE-valid? (DQ-DE2 DQ))
				    (flush-all? MA sigs)))))

; The next state of the DE3.
(defun step-DE3 (DQ MA sigs)
  (declare (xargs :guard (and (DQ-p DQ) (MA-state-p MA) (MA-input-p sigs))))
  (b-if (b-and (DE-valid? (DQ-DE3 DQ)) (dispatch-inst? MA))
	(dispatch-entry 0 0 0 0 0 0 0 0 0)
  (b-if (bs-and (b-not (DE-valid? (DQ-DE3 DQ)))
		(DE-valid? (DQ-DE2 DQ))
		(b-not (dispatch-inst? MA)))
	(update-dispatch-entry (decode-output (MA-IFU MA) MA sigs)
	   :valid? (b-andc2 (DE-valid? (decode-output (MA-IFU MA) MA sigs))
			    (flush-all? MA sigs)))
	(update-dispatch-entry (DQ-DE3 DQ)
		   :valid? (b-andc2 (DE-valid? (DQ-DE3 DQ))
				    (flush-all? MA sigs))))))

; The next state of a register reference table entry. 
(defun step-reg-ref (reg-ref idx MA sigs)
  (declare (xargs :guard (and (reg-ref-p reg-ref)
			      (rname-p idx)
			      (MA-state-p MA) (MA-input-p sigs))))
  (reg-ref (b-if (flush-all? MA sigs)
		 0
		 (b-if (bs-and (dispatch-inst? MA)
			       (cntlv-wb? (dispatch-cntlv MA))
			       (b-not (cntlv-wb-sreg? (dispatch-cntlv MA)))
			       (bv-eqv *rname-size*
				       (dispatch-dest-reg MA)
				       idx))
		       1
		       (b-if (bs-and (ROB-write-reg? (MA-ROB MA))
				     (bv-eqv *rname-size*
					     (ROB-write-rid (MA-ROB MA))
					     idx)
				     (bv-eqv *rob-index-size*
					     (ROB-head (MA-ROB MA))
					     (reg-ref-tag reg-ref)))
			     0 (reg-ref-wait? reg-ref))))
	   (b-if (bs-and (dispatch-inst? MA)
			 (cntlv-wb? (dispatch-cntlv MA))
			 (b-not (cntlv-wb-sreg? (dispatch-cntlv MA)))
			 (bv-eqv *rname-size*
				 (dispatch-dest-reg MA)
				 idx))
		 (ROB-tail (MA-ROB MA))
		 (reg-ref-tag reg-ref))))

(defun step-reg-list (r-list idx MA sigs)
  (declare (xargs :guard (and (reg-ref-listp r-list)
			      (rname-p idx)
			      (MA-state-p MA)
			      (MA-input-p sigs))))
  (if (endp r-list)
      nil
      (cons (step-reg-ref (car r-list) idx MA sigs)
	    (step-reg-list (cdr r-list) (rname (1+ idx)) MA sigs))))

; The next state of the register reference table.
(defun step-reg-tbl  (r-list MA sigs)
  (declare (xargs :guard (and (reg-tbl-p r-list)
			      (MA-state-p MA)
			      (MA-input-p sigs))
		  :guard-hints (("Goal" :in-theory (enable reg-tbl-p)))))
  (step-reg-list r-list 0 MA sigs))

(defthm reg-ref-listp-step-reg-list
    (implies (and (reg-ref-listp reg-tbl) (MA-state-p MA) (MA-input-p sigs))
	     (reg-ref-listp (step-reg-list reg-tbl idx MA sigs))))

(defthm len-step-reg-list
    (equal (len (step-reg-list reg-tbl idx MA sigs))
	   (len reg-tbl)))

(defthm reg-tbl-p-step-reg-tbl
    (implies (and (reg-tbl-p reg-tbl)
		  (MA-state-p MA) (MA-input-p sigs))
	     (reg-tbl-p (step-reg-tbl reg-tbl MA sigs)))
  :hints (("goal" :in-theory (enable reg-tbl-p))))

(in-theory (disable step-reg-tbl))

; The next state of a special register reference table entry.
(defun step-sreg-ref (sreg-ref idx MA sigs)
  (declare (xargs :guard (and (reg-ref-p sreg-ref)
			      (rname-p idx)
			      (MA-state-p MA)
			      (MA-input-p sigs))))
  (reg-ref (b-if (flush-all? MA sigs) 0
		 (b-if (bs-and (dispatch-inst? MA)
			       (cntlv-wb? (dispatch-cntlv MA))
			       (cntlv-wb-sreg? (dispatch-cntlv MA))
			       (bv-eqv *rname-size*
				       (dispatch-dest-reg MA)
				       idx))
		       1
		       (b-if (bs-and (ROB-write-sreg? (MA-ROB MA))
				     (bv-eqv *rname-size*
					     (ROB-write-rid (MA-ROB MA))
					     idx)
				     (bv-eqv *rob-index-size*
					     (ROB-head (MA-ROB MA))
					     (reg-ref-tag sreg-ref)))
			     0
			     (reg-ref-wait? sreg-ref))))
	   (b-if (bs-and (dispatch-inst? MA)
			 (cntlv-wb? (dispatch-cntlv MA))
			 (cntlv-wb-sreg? (dispatch-cntlv MA))
			 (bv-eqv *rname-size*
				 (dispatch-dest-reg MA)
				 idx))
		 (ROB-tail (MA-ROB MA))
		 (reg-ref-tag sreg-ref))))

; The next state of special register reference table. 
(defun step-sreg-tbl (sreg-tbl MA sigs)
  (declare (xargs :guard (and (sreg-tbl-p sreg-tbl) (MA-state-p MA)
			      (MA-input-p sigs))))
  (sreg-tbl (step-sreg-ref (sreg-tbl-sr0 sreg-tbl) 0 MA sigs)
	    (step-sreg-ref (sreg-tbl-sr1 sreg-tbl) 1 MA sigs)))

; The next state of DQ
(defun step-DQ (MA sigs)
  (declare (xargs :guard (and (MA-state-p MA) (MA-input-p sigs))))
  (DQ (step-DE0 (MA-DQ MA) MA sigs)
      (step-DE1 (MA-DQ MA) MA sigs)
      (step-DE2 (MA-DQ MA) MA sigs)
      (step-DE3 (MA-DQ MA) MA sigs)
      (step-reg-tbl (DQ-reg-tbl (MA-DQ MA)) MA sigs)
      (step-sreg-tbl (DQ-sreg-tbl (MA-DQ MA)) MA sigs)))

(defthm DQ-p-step-DQ
    (implies (and (MA-state-p MA) (MA-input-p sigs))
	     (DQ-p (step-DQ MA sigs))))
(in-theory (disable step-DQ))

;Commit-inst? is on when the instruction at the head of the ROB commits.
; If the instruction at the head of the ROB is an exception causing
; instruction or synchronizing instruction, we check whether there are
; pending writes in the write buffer before allowing it to commit.
(defun commit-inst? (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (let ((ROB (MA-ROB MA))
	(LSU (MA-LSU MA)))
    (let ((robe (nth-robe (ROB-head ROB) ROB)))
      (bs-and (ROBE-valid? robe)
	      (ROBE-complete? robe)
	      (b-nand (b-ior (excpt-raised? (ROBE-excpt robe))
			     (ROBE-sync? robe))
		      (LSU-pending-writes? LSU))))))

(defthm bitp-commit-inst? (bitp (commit-inst? MA)))
(in-theory (disable commit-inst?))

; This value is 1 when the ROB entry designated by index should hold
; the instruction dispatched in the current cycle.
(defun ROBE-receive-inst? (ROB index MA)
  (declare (xargs :guard (and (ROB-p rob)
			      (rob-index-p index) (MA-state-p MA))))
  (b-and (dispatch-inst? MA)
	 (bv-eqv *rob-index-size* (ROB-tail ROB) index)))

(defthm bitp-ROBE-receive-inst?
    (bitp (ROBE-receive-inst? ROB index MA)))
(in-theory (disable ROBE-receive-inst?))

; This value is 1 when the ROB entry designated by index should
; read the result of an instruction put on the CDB.
(defun ROBE-receive-result? (ROB index MA)
  (declare (xargs :guard (and (ROB-p rob) (rob-index-p index)
			      (MA-state-p MA))))
  (bs-and (ROBE-valid? (nth-ROBE index ROB))
	  (CDB-ready-for? index MA)))

(defthm bitp-ROBE-receive-result?
    (bitp (ROBE-receive-result? ROB index MA)))
(in-theory (disable ROBE-receive-result?))

; The next state of an ROB entry designated by idx.
(defun step-ROBE (robe idx ROB MA sigs)
  (declare (xargs :guard (and (ROB-entry-p robe)
			      (rob-index-p idx)
			      (ROB-p ROB) (MA-state-p MA) (MA-input-p sigs))))
  (ROB-entry (b-if (b-ior (b-and (commit-inst? MA)
				 (bv-eqv *rob-index-size* (ROB-head ROB) idx))
			  (flush-all? MA sigs))
		   0
		   (b-if (robe-receive-inst? ROB idx MA)
			 1
			 (ROBE-valid? robe))) ; valid?
	     (b-if (robe-receive-inst? ROB idx MA)
		   (dispatch-no-unit? MA)
		   (b-ior (ROBE-complete? robe)
			  (robe-receive-result? rob idx MA))) ;complete?
	     (b-if (robe-receive-inst? rob idx MA)
		   (dispatch-excpt MA)
		   (b-if (robe-receive-result? rob idx MA)
			 (CDB-excpt MA)
			 (ROBE-excpt robe))) ;excpt
	     (b-if (robe-receive-inst? rob idx MA)
		   (cntlv-wb? (dispatch-cntlv MA))
		   (ROBE-wb? robe))
	     (b-if (robe-receive-inst? ROB idx MA)
		   (cntlv-wb-sreg? (dispatch-cntlv MA))
		   (ROBE-wb-sreg? robe))
	     (b-if (robe-receive-inst? ROB idx MA)
		   (cntlv-sync? (dispatch-cntlv MA))
		   (ROBE-sync? robe))
	     (b-if (robe-receive-inst? ROB idx MA)
		   (logbit 3 (cntlv-exunit (dispatch-cntlv MA)))
		   (ROBE-branch? robe))
	     (b-if (robe-receive-inst? ROB idx MA)
		   (cntlv-rfeh? (dispatch-cntlv MA))
		   (ROBE-rfeh? robe))
	     (b-if (robe-receive-inst? ROB idx MA)
		   (cntlv-br-predict? (dispatch-cntlv MA))
		   (ROBE-br-predict? robe))
	     (b-if (b-and (robe-receive-result? rob idx MA)
			  (ROBE-branch? robe))
		   (logcar (CDB-val MA))
		   (ROBE-br-actual? robe))
	     (b-if (robe-receive-inst? ROB idx MA)
		   (dispatch-pc MA)
		   (ROBE-pc robe))
	     (b-if (robe-receive-inst? ROB idx MA)
		   (word (DE-br-target (DQ-DE0 (MA-DQ MA))))
		   (b-if (b-andc2 (robe-receive-result? rob idx MA)
				  (ROBE-branch? robe))
			 (CDB-val MA)
			 (ROBE-val robe)))
	     (b-if (robe-receive-inst? ROB idx MA)
		   (dispatch-dest-reg MA)
		   (ROBE-dest robe))))

(defthm ROBE-p-step-robe
    (implies (and (ROB-entry-p robe)
		  (ROB-p ROB)
		  (MA-state-p MA)
		  (MA-input-p sigs))
	     (ROB-entry-p (step-robe robe index ROB MA sigs))))
(in-theory (disable step-robe))

(defun step-ROBE-list (entries index ROB MA sigs)
  (declare (xargs :guard (and (ROBE-listp entries)
			      (rob-index-p index)
			      (ROB-p ROB) (MA-state-p MA) (MA-input-p sigs))))
  (if (endp entries)
      nil
      (cons (step-ROBE (car entries) index ROB MA sigs)
	    (step-ROBE-list (cdr entries) (rob-index (1+ index))
			    ROB MA sigs))))

(defun step-ROB-entries (entries ROB MA sigs)
  (declare (xargs :guard (and (ROB-entries-p entries)
			      (ROB-p ROB) (MA-state-p MA) (MA-input-p sigs))
		  :guard-hints (("Goal" :in-theory (enable ROB-entries-p)))))
  (step-ROBE-list entries 0 ROB MA sigs))

(defthm robe-lisp-step-robe-list
    (implies (and (robe-listp entries)
		  (rob-p rob)
		  (MA-state-p MA)
		  (MA-input-p sigs))
	     (ROBE-listp (step-robe-list entries index rob MA sigs))))

(defthm len-step-ROBE-list
    (equal (len (step-ROBE-list entries index ROB MA sigs))
	   (len entries)))

(defthm ROB-entries-p-step-ROB-entries
    (implies (and (ROB-entries-p entries)
		  (ROB-p ROB)
		  (MA-state-p MA)
		  (MA-input-p sigs))
	     (ROB-entries-p (step-ROB-entries entries ROB MA sigs)))
  :hints (("Goal" :in-theory (enable rob-entries-p))))
(in-theory (disable step-ROB-entries))

; The next state of the ROB.
(defun step-ROB (MA sigs)
  (declare (xargs :guard (and (MA-state-p MA) (MA-input-p sigs))))
  (ROB (b-if (flush-all? MA sigs) 0
	     (b-xor (ROB-flg (MA-ROB MA))
		    (b-xor (b-and (commit-inst? MA)
				  (logbit *rob-index-size*
					  (+ 1 (ROB-head (MA-ROB MA)))))
			   (b-and (dispatch-inst? MA)
				  (logbit *rob-index-size*
					  (+ 1 (ROB-tail (MA-ROB MA))))))))
       (b-if (b-ior (enter-excpt? MA) (ex-intr? MA sigs)) 0
	     (b-ior (MA-input-exintr sigs)
		    (ROB-exintr? (MA-ROB MA))))
       (b-if (flush-all? MA sigs) 0
	     (b-if (commit-inst? MA)
		   (rob-index (+ 1 (ROB-head (MA-ROB MA))))
		   (ROB-head (MA-ROB MA))))
       (b-if (flush-all? MA sigs) 0
	     (b-if (dispatch-inst? MA)
		   (rob-index (+ 1 (ROB-tail (MA-ROB MA))))
		   (ROB-tail (MA-ROB MA))))
       (step-ROB-entries (ROB-entries (MA-ROB MA)) (MA-ROB MA) MA sigs)))

(defthm ROB-p-step-ROB
    (implies (and (MA-state-p MA) (MA-input-p sigs))
	     (ROB-p (step-ROB MA sigs))))
(in-theory (disable step-ROB))

; The next state of IU-RS0.
(defun step-IU-RS0 (iu MA sigs)
  (declare (xargs :guard (and (integer-unit-p IU)
			      (MA-state-p MA) (MA-input-p sigs))))
  (let ((RS0 (IU-RS0 iu)))
    (RS (b-andc1 (flush-all? MA sigs)
		 (b-if (RS-valid? rs0)
		       (b-not (issue-IU-RS0? iu MA))
		       (b-and (dispatch-to-IU? MA) (select-IU-RS0? iu))))
	(b-if (b-and (dispatch-to-IU? MA) (select-IU-RS0? iu))
	      (b-not (logbit 0 (cntlv-operand (dispatch-cntlv MA))))
	      (RS-op RS0))
	(b-if (b-and (dispatch-to-IU? MA) (select-IU-RS0? iu))
	      (ROB-tail (MA-ROB MA))
	      (RS-tag RS0))
	(b-if (b-and (dispatch-to-IU? MA) (select-IU-RS0? iu))
	      (dispatch-ready1? MA)
	      (b-ior (RS-ready1? RS0)
		     (CDB-ready-for? (RS-src1 RS0) MA)))
	(b-if (b-and (dispatch-to-IU? MA) (select-IU-RS0? iu))
	      (dispatch-ready2? MA)
	      (b-ior (RS-ready2? RS0)
		     (CDB-ready-for? (RS-src2 RS0) MA)))
	(b-if (b-and (dispatch-to-IU? MA) (select-IU-RS0? iu))
	      (dispatch-val1 MA)
	      (b-if (b-andc1 (RS-ready1? RS0)
			     (CDB-ready-for? (RS-src1 RS0) MA))
		    (CDB-val MA)
		    (RS-val1 RS0)))
	(b-if (b-and (dispatch-to-IU? MA) (select-IU-RS0? iu))
	      (dispatch-val2 MA)
	      (b-if (b-andc1 (RS-ready2? RS0)
			     (CDB-ready-for? (RS-src2 RS0) MA))
		    (CDB-val MA)
		    (RS-val2 RS0)))
	(b-if (b-and (dispatch-to-IU? MA) (select-IU-RS0? iu))
	      (dispatch-src1 MA)
	      (RS-src1 RS0))
	(b-if (b-and (dispatch-to-IU? MA) (select-IU-RS0? iu))
	      (dispatch-src2 MA)
	      (RS-src2 RS0)))))

(defthm RS-p-step-IU-RS0
    (implies (and (integer-unit-p IU) (MA-state-p MA) (MA-input-p sigs))
	     (RS-p (step-IU-RS0 IU MA sigs))))
(in-theory (disable step-IU-RS0))

; The next state of IU-RS1.
(defun step-IU-RS1 (iu MA sigs)
  (declare (xargs :guard (and (integer-unit-p IU)
			      (MA-state-p MA) (MA-input-p sigs))))
  (let ((RS1 (IU-RS1 iu)))
    (RS (b-andc1 (flush-all? MA sigs)
		 (b-if (RS-valid? rs1)
		       (b-not (issue-IU-RS1? iu MA))
		       (b-and (dispatch-to-IU? MA) (select-IU-RS1? iu))))
	(b-if (b-and (dispatch-to-IU? MA) (select-IU-RS1? iu))
	      (b-not (logbit 0 (cntlv-operand (dispatch-cntlv MA))))
	      (RS-op RS1))
	(b-if (b-and (dispatch-to-IU? MA) (select-IU-RS1? iu))
	      (ROB-tail (MA-ROB MA))
	      (RS-tag RS1))
	(b-if (b-and (dispatch-to-IU? MA) (select-IU-RS1? iu))
	      (dispatch-ready1? MA)
	      (b-ior (RS-ready1? RS1)
		     (CDB-ready-for? (RS-src1 RS1) MA)))
	(b-if (b-and (dispatch-to-IU? MA) (select-IU-RS1? iu))
	      (dispatch-ready2? MA)
	      (b-ior (RS-ready2? RS1)
		     (CDB-ready-for? (RS-src2 RS1) MA)))
	(b-if (b-and (dispatch-to-IU? MA) (select-IU-RS1? iu))
	      (dispatch-val1 MA)
	      (b-if (b-andc1 (RS-ready1? RS1)
			     (CDB-ready-for? (RS-src1 RS1) MA))
		    (CDB-val MA)
		    (RS-val1 RS1)))
	(b-if (b-and (dispatch-to-IU? MA) (select-IU-RS1? iu))
	      (dispatch-val2 MA)
	      (b-if (b-andc1 (RS-ready2? RS1)
			     (CDB-ready-for? (RS-src2 RS1) MA))
		    (CDB-val MA)
		    (RS-val2 RS1)))
	(b-if (b-and (dispatch-to-IU? MA) (select-IU-RS1? iu))
	      (dispatch-src1 MA)
	      (RS-src1 RS1))
	(b-if (b-and (dispatch-to-IU? MA) (select-IU-RS1? iu))
	      (dispatch-src2 MA)
	      (RS-src2 RS1)))))

(defthm RS-p-step-IU-RS1
    (implies (and (integer-unit-p IU) (MA-state-p MA) (MA-input-p sigs))
	     (RS-p (step-IU-RS1 IU MA sigs))))
(in-theory (disable step-IU-RS1))

; The next state of IU.
(defun step-IU (MA sigs)
  (declare (xargs :guard (and (MA-state-p MA) (MA-input-p sigs))))
  (integer-unit (step-IU-RS0 (MA-IU MA) MA sigs)
		(step-IU-RS1 (MA-IU MA) MA sigs)))

(defthm integer-unit-p-step-IU
    (implies (and (MA-state-p MA) (MA-input-p sigs))
	     (integer-unit-p (step-IU MA sigs))))
(in-theory (disable step-IU))

; The next state of reservation station MU-RS0.
(defun step-MU-RS0 (MU MA sigs)
  (declare (xargs :guard (and (mult-unit-p MU)
			      (MA-state-p MA) (MA-input-p sigs))))
  (let ((RS0 (MU-RS0 MU)))
    (RS (b-andc1 (flush-all? MA sigs)
		 (b-if (RS-valid? rs0)
		       (b-not (issue-MU-RS0? MU MA))
		       (b-and (dispatch-to-MU? MA)
			      (select-MU-RS0? MU))))
	0
	(b-if (b-and (dispatch-to-MU? MA) (select-MU-RS0? MU))
	      (ROB-tail (MA-ROB MA))
	      (RS-tag RS0))
	(b-if (b-and (dispatch-to-MU? MA) (select-MU-RS0? MU))
	      (dispatch-ready1? MA)
	      (b-ior (RS-ready1? RS0)
		     (CDB-ready-for? (RS-src1 RS0) MA)))
	(b-if (b-and (dispatch-to-MU? MA) (select-MU-RS0? MU))
	      (dispatch-ready2? MA)
	      (b-ior (RS-ready2? RS0)
		     (CDB-ready-for? (RS-src2 RS0) MA)))
	(b-if (b-and (dispatch-to-MU? MA) (select-MU-RS0? MU))
	      (dispatch-val1 MA)
	      (b-if (b-andc1 (RS-ready1? RS0)
			     (CDB-ready-for? (RS-src1 RS0) MA))
		    (CDB-val MA)
		    (RS-val1 RS0)))
	(b-if (b-and (dispatch-to-MU? MA) (select-MU-RS0? MU))
	      (dispatch-val2 MA)
	      (b-if (b-andc1 (RS-ready2? RS0)
			     (CDB-ready-for? (RS-src2 RS0) MA))
		    (CDB-val MA)
		    (RS-val2 RS0)))
	(b-if (b-and (dispatch-to-MU? MA) (select-MU-RS0? MU))
	      (dispatch-src1 MA)
	      (RS-src1 RS0))
	(b-if (b-and (dispatch-to-MU? MA) (select-MU-RS0? MU))
	      (dispatch-src2 MA)
	      (RS-src2 RS0)))))

; The next state of reservation station MU-RS1.
(defun step-MU-RS1 (MU MA sigs)
  (declare (xargs :guard (and (mult-unit-p MU)
			      (MA-state-p MA) (MA-input-p sigs))))
  (let ((RS1 (MU-RS1 MU)))
    (RS (b-andc1 (flush-all? MA sigs)
		 (b-if (RS-valid? rs1)
		       (b-not (issue-MU-RS1? MU MA))
		       (b-and (dispatch-to-MU? MA)
			      (select-MU-RS1? MU))))
	0
	(b-if (b-and (dispatch-to-MU? MA) (select-MU-RS1? MU))
	      (ROB-tail (MA-ROB MA))
	      (RS-tag RS1))
	(b-if (b-and (dispatch-to-MU? MA) (select-MU-RS1? MU))
	      (dispatch-ready1? MA)
	      (b-ior (RS-ready1? RS1)
		     (CDB-ready-for? (RS-src1 RS1) MA)))
	(b-if (b-and (dispatch-to-MU? MA) (select-MU-RS1? MU))
	      (dispatch-ready2? MA)
	      (b-ior (RS-ready2? RS1)
		     (CDB-ready-for? (RS-src2 RS1) MA)))
	(b-if (b-and (dispatch-to-MU? MA) (select-MU-RS1? MU))
	      (dispatch-val1 MA)
	      (b-if (b-andc1 (RS-ready1? RS1)
			     (CDB-ready-for? (RS-src1 RS1) MA))
		    (CDB-val MA)
		    (RS-val1 RS1)))
	(b-if (b-and (dispatch-to-MU? MA) (select-MU-RS1? MU))
	      (dispatch-val2 MA)
	      (b-if (b-andc1 (RS-ready2? RS1)
			     (CDB-ready-for? (RS-src2 RS1) MA))
		    (CDB-val MA)
		    (RS-val2 RS1)))
	(b-if (b-and (dispatch-to-MU? MA) (select-MU-RS1? MU))
	      (dispatch-src1 MA)
	      (RS-src1 RS1))
	(b-if (b-and (dispatch-to-MU? MA) (select-MU-RS1? MU))
	      (dispatch-src2 MA)
	      (RS-src2 RS1)))))

; The next state of latch MU-lch1.
(defun step-MU-lch1 (MU MA sigs)
  (declare (xargs :guard (and (mult-unit-p MU)
			      (MA-state-p MA) (MA-input-p sigs))))
  (b-if (bs-ior (CDB-for-MU? MA)
		(b-not (MU-latch1-valid? (MU-lch1 MU)))
		(b-not (MU-latch2-valid? (MU-lch2 MU))))
	(b-if (issue-MU-RS0? MU MA)
	      (MU-latch1 (b-not (flush-all? MA sigs))
			 (RS-tag (MU-RS0 MU))
			 (ML1-output (RS-val1 (MU-RS0 MU))
				     (RS-val2 (MU-RS0 MU))))
	      (b-if (issue-MU-RS1? MU MA)
		    (MU-latch1 (b-not (flush-all? MA sigs))
			       (RS-tag (MU-RS1 MU))
			       (ML1-output (RS-val1 (MU-RS1 MU))
					   (RS-val2 (MU-RS1 MU))))
		    (MU-latch1 0 0 (ML1-output (RS-val1 (MU-RS1 MU))
					       (RS-val2 (MU-RS1 MU))))))
	(update-MU-latch1 (MU-lch1 MU)
			  :valid? (b-andc1 (flush-all? MA sigs)
					   (MU-latch1-valid? (MU-lch1 MU))))))

; The next state of latch MU-lch2.
(defun step-MU-lch2 (MU MA sigs)
  (declare (xargs :guard (and (mult-unit-p MU)
			      (MA-state-p MA) (MA-input-p sigs))))
  (b-if (b-orc2 (CDB-for-MU? MA)
		(MU-latch2-valid? (MU-lch2 MU)))
	(MU-latch2 (b-and (MU-latch1-valid? (MU-lch1 MU))
			  (b-not (flush-all? MA sigs)))
		   (MU-latch1-tag (MU-lch1 MU))
		   (ML2-output (MU-latch1-data (MU-lch1 MU))))
	(update-MU-latch2 (MU-lch2 MU)
			  :valid? (b-andc1 (flush-all? MA sigs)
					   (MU-latch2-valid? (MU-lch2 MU))))))

; The next state of the MU.
(defun step-MU (MA sigs)
  (declare (xargs :guard (and (MA-state-p MA) (MA-input-p sigs))))
  (mult-unit (step-MU-RS0 (MA-MU MA) MA sigs)
	     (step-MU-RS1 (MA-MU MA) MA sigs)
	     (step-MU-lch1 (MA-MU MA) MA sigs)
	     (step-MU-lch2 (MA-MU MA) MA sigs)))

(defthm mult-unit-p-step-MU
    (implies (and (MA-state-p MA) (MA-input-p sigs))
	     (mult-unit-p (step-MU MA sigs))))
(in-theory (disable step-MU))

; The next state of reservation station BU-RS0.
(defun step-BU-RS0 (BU MA sigs)
  (declare (xargs :guard (and (branch-unit-p BU)
			      (MA-state-p MA) (MA-input-p sigs))))
  (let ((RS0 (BU-RS0 BU)))
    (BU-RS (b-and (b-not (flush-all? MA sigs))
		  (b-if (BU-RS-valid? RS0)
			(b-not (issue-BU-RS0? BU MA))
			(b-and (dispatch-to-BU? MA) (select-BU-RS0? BU))))
	   (b-if (b-and (dispatch-to-BU? MA) (select-BU-RS0? BU))
		 (ROB-tail (MA-ROB MA))
		 (BU-RS-tag RS0))
	   (b-if (b-and (dispatch-to-BU? MA) (select-BU-RS0? BU))
		 (dispatch-ready3? MA)
		 (b-ior (BU-RS-ready? RS0)
			(CDB-ready-for? (BU-RS-src RS0) MA)))
	   (b-if (b-and (dispatch-to-BU? MA) (select-BU-RS0? BU))
		 (dispatch-val3 MA)
		 (b-if (b-andc1 (BU-RS-ready? RS0)
				(CDB-ready-for? (BU-RS-src RS0) MA))
		       (CDB-val MA)
		       (BU-RS-val RS0)))
	   (b-if (b-and (dispatch-to-BU? MA) (select-BU-RS0? BU))
		 (dispatch-src3 MA)
		 (BU-RS-src RS0)))))

; The next state of reservation station BU-RS1.
(defun step-BU-RS1 (BU MA sigs)
  (declare (xargs :guard (and (branch-unit-p BU)
			      (MA-state-p MA) (MA-input-p sigs))))
  (let ((RS1 (BU-RS1 BU)))
    (BU-RS (b-and (b-not (flush-all? MA sigs))
		  (b-if (BU-RS-valid? RS1)
			(b-not (issue-BU-RS1? BU MA))
			(b-and (dispatch-to-BU? MA) (select-BU-RS1? BU))))
	   (b-if (b-and (dispatch-to-BU? MA) (select-BU-RS1? BU))
		 (ROB-tail (MA-ROB MA))
		 (BU-RS-tag RS1))
	   (b-if (b-and (dispatch-to-BU? MA) (select-BU-RS1? BU))
		 (dispatch-ready3? MA)
		 (b-ior (BU-RS-ready? RS1)
			(CDB-ready-for? (BU-RS-src RS1) MA)))
	   (b-if (b-and (dispatch-to-BU? MA) (select-BU-RS1? BU))
		 (dispatch-val3 MA)
		 (b-if (b-andc1 (BU-RS-ready? RS1)
				(CDB-ready-for? (BU-RS-src RS1) MA))
		       (CDB-val MA)
		       (BU-RS-val RS1)))
	   (b-if (b-and (dispatch-to-BU? MA) (select-BU-RS1? BU))
		 (dispatch-src3 MA)
		 (BU-RS-src RS1)))))

; The next state of the BU.
(defun step-BU (MA sigs)
  (declare (xargs :guard (and (MA-state-p MA) (MA-input-p sigs))))
  (branch-unit (step-BU-RS0 (MA-BU MA) MA sigs)
	       (step-BU-RS1 (MA-BU MA) MA sigs)))

(defthm branch-unit-p-step-BU
    (implies (and (MA-state-p MA) (MA-input-p sigs))
	     (branch-unit-p (step-BU MA sigs))))
(in-theory (disable step-BU))

; The next state of the rs1-head?, which is a flag in the LSU to determine
; which reservation station contains the first load-store instruction.
; The order of load-store instruction is important, as the Tomasulo's
; algorithm does not guarantee the correctness of the execution.
(defun step-rs1-head? (LSU MA sigs)
  (declare (xargs :guard (and (load-store-unit-p LSU)
			      (MA-state-p MA) (MA-input-p sigs))))
  (b-if (issue-LSU-RS0? LSU MA sigs) 1
  (b-if (issue-LSU-RS1? LSU MA sigs) 0
	(LSU-rs1-head? LSU))))

(defthm bitp-step-rs1-head?
    (implies (and (load-store-unit-p LSU)
		  (MA-state-p MA) (MA-input-p sigs))
	     (bitp (step-rs1-head? LSU MA sigs))))
(in-theory (disable step-rs1-head?))

; The next state of reservation station LSU-RS0.  Remember reservation
; stations for the LSU forms a queue as our machine needs to know the
; exact order of memory accesses.  RS0 is the head of the queue.
(defun step-LSU-RS0 (LSU MA sigs)
  (declare (xargs :guard (and (load-store-unit-p LSU)
			      (MA-state-p MA) (MA-input-p sigs))))
  (let ((RS0 (LSU-RS0 LSU)))
    (LSU-RS (b-and (b-not (flush-all? MA sigs))
		   (b-if (LSU-RS-valid? RS0)
			 (b-not (issue-LSU-RS0? LSU MA sigs))
			 (b-and (dispatch-to-LSU? MA)
				(select-LSU-RS0? LSU))))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS0? LSU))
		  (logbit 1 (cntlv-operand (dispatch-cntlv MA)))
		  (LSU-RS-op RS0))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS0? LSU))
		  (cntlv-ld-st? (dispatch-cntlv MA))
		  (LSU-RS-ld-st? RS0))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS0? LSU))
		  (ROB-tail (MA-ROB MA))
		  (LSU-RS-tag RS0))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS0? LSU))
		  (dispatch-ready3? MA)
		  (b-ior (LSU-RS-rdy3? RS0)
			 (CDB-ready-for? (LSU-RS-src3 RS0) MA)))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS0? LSU))
		  (dispatch-val3 MA)
		  (b-if (b-andc1 (LSU-RS-rdy3? RS0)
				 (CDB-ready-for? (LSU-RS-src3 RS0) MA))
			(CDB-val MA)
			(LSU-RS-val3 RS0)))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS0? LSU))
		  (dispatch-src3 MA)
		  (LSU-RS-src3 RS0))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS0? LSU))
		  (dispatch-ready1? MA)
		  (b-ior (LSU-RS-rdy1? RS0)
			 (CDB-ready-for? (LSU-RS-src1 RS0) MA)))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS0? LSU))
		  (dispatch-val1 MA)
		  (b-if (b-andc1 (LSU-RS-rdy1? RS0)
				 (CDB-ready-for? (LSU-RS-src1 RS0) MA))
			(CDB-val MA)
			(LSU-RS-val1 RS0)))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS0? LSU))
		  (dispatch-src1 MA)
		  (LSU-RS-src1 RS0))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS0? LSU))
		  (dispatch-ready2? MA)
		  (bs-ior (LSU-RS-rdy2? RS0)
			  (CDB-ready-for? (LSU-RS-src2 RS0) MA)))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS0? LSU))
		  (dispatch-val2 MA)
		  (b-if (b-andc1 (LSU-RS-rdy2? RS0)
				 (CDB-ready-for? (LSU-RS-src2 RS0) MA))
			(CDB-val MA)
			(LSU-RS-val2 RS0)))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS0? LSU))
		  (dispatch-src2 MA)
		  (LSU-RS-src2 RS0)))))

(defthm LSU-RS-p-step-LSU-RS0
    (implies (and (load-store-unit-p LSU)
		  (MA-state-p MA)
		  (MA-input-p sigs))
	     (LSU-RS-p (step-LSU-RS0 LSU MA sigs))))
(in-theory (disable step-LSU-RS0))

; The next state of reservation station LSU-RS1.
(defun step-LSU-RS1 (LSU MA sigs)
  (declare (xargs :guard (and (load-store-unit-p LSU)
			      (MA-state-p MA) (MA-input-p sigs))))
  (let ((RS1 (LSU-RS1 LSU)))
    (LSU-RS (b-and (b-not (flush-all? MA sigs))
		   (b-if (LSU-RS-valid? RS1)
			 (b-not (issue-LSU-RS1? LSU MA sigs))
			 (b-and (dispatch-to-LSU? MA)
				(select-LSU-RS1? LSU))))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS1? LSU))
		  (logbit 1 (cntlv-operand (dispatch-cntlv MA)))
		  (LSU-RS-op RS1))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS1? LSU))
		  (cntlv-ld-st? (dispatch-cntlv MA))
		  (LSU-RS-ld-st? RS1))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS1? LSU))
		  (ROB-tail (MA-ROB MA))
		  (LSU-RS-tag RS1))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS1? LSU))
		  (dispatch-ready3? MA)
		  (b-ior (LSU-RS-rdy3? RS1)
			 (CDB-ready-for? (LSU-RS-src3 RS1) MA)))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS1? LSU))
		  (dispatch-val3 MA)
		  (b-if (b-andc1 (LSU-RS-rdy3? RS1)
				 (CDB-ready-for? (LSU-RS-src3 RS1) MA))
			(CDB-val MA)
			(LSU-RS-val3 RS1)))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS1? LSU))
		  (dispatch-src3 MA)
		  (LSU-RS-src3 RS1))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS1? LSU))
		  (dispatch-ready1? MA)
		  (b-ior (LSU-RS-rdy1? RS1)
			 (CDB-ready-for? (LSU-RS-src1 RS1) MA)))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS1? LSU))
		  (dispatch-val1 MA)
		  (b-if (b-andc1 (LSU-RS-rdy1? RS1)
				 (CDB-ready-for? (LSU-RS-src1 RS1) MA))
			(CDB-val MA)
			(LSU-RS-val1 RS1)))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS1? LSU))
		  (dispatch-src1 MA)
		  (LSU-RS-src1 RS1))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS1? LSU))
		  (dispatch-ready2? MA)
		  (b-ior (LSU-RS-rdy2? RS1)
			 (CDB-ready-for? (LSU-RS-src2 RS1) MA)))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS1? LSU))
		  (dispatch-val2 MA)
		  (b-if (b-andc1 (LSU-RS-rdy2? RS1)
				 (CDB-ready-for? (LSU-RS-src2 RS1) MA))
			(CDB-val MA)
			(LSU-RS-val2 RS1)))
	    (b-if (b-and (dispatch-to-LSU? MA) (select-LSU-RS1? LSU))
		  (dispatch-src2 MA)
		  (LSU-RS-src2 RS1)))))

(defthm LSU-RS-p-step-LSU-RS1
    (implies (and (load-store-unit-p LSU)
		  (MA-state-p MA)
		  (MA-input-p sigs))
	     (LSU-RS-p (step-LSU-RS1 LSU MA sigs))))
(in-theory (disable step-LSU-RS1))

; The next state of read buffer.
(defun step-rbuf (LSU MA sigs)
  (declare (xargs :guard (and (load-store-unit-p LSU)
			      (MA-state-p MA) (MA-input-p sigs))))
  (let ((RS0 (LSU-RS0 LSU)) (RS1 (LSU-RS1 LSU)))
    (b-if (b-andc2 (rbuf-valid? (LSU-rbuf LSU))
		   (release-rbuf? LSU MA sigs))
	  (update-read-buffer (LSU-rbuf LSU)
			      :valid? (b-not (flush-all? MA sigs)))
	  (b-if (b-andc2 (issue-LSU-RS0? LSU MA sigs)
			 (LSU-RS-ld-st? RS0))
		(read-buffer (b-not (flush-all? MA sigs))
			     (LSU-RS-tag RS0)
			     (b-if (LSU-RS-op RS0)
				   (addr (LSU-RS-val1 RS0))
				   (addr (+ (LSU-RS-val1 RS0)
					    (LSU-RS-val2 RS0))))
			     (b-if (release-wbuf0? LSU sigs)
				   (wbuf-valid? (LSU-wbuf1 LSU))
				   (wbuf-valid? (LSU-wbuf0 LSU)))
			     (b-if (release-wbuf0? LSU sigs)
				   0
				   (wbuf-valid? (LSU-wbuf1 LSU))))
		(b-if (b-andc2 (issue-LSU-RS1? LSU MA sigs)
			       (LSU-RS-ld-st? RS1))
		      (read-buffer (b-not (flush-all? MA sigs))
				   (LSU-RS-tag RS1)
				   (b-if (LSU-RS-op RS1)
					 (addr (LSU-RS-val1 RS1))
					 (addr (+ (LSU-RS-val1 RS1)
						  (LSU-RS-val2 RS1))))
				   (b-if (release-wbuf0? LSU sigs)
					 (wbuf-valid? (LSU-wbuf1 LSU))
					 (wbuf-valid? (LSU-wbuf0 LSU)))
				   (b-if (release-wbuf0? LSU sigs)
					 0
					 (wbuf-valid? (LSU-wbuf1 LSU))))
		      (read-buffer 0 0 0 0 0))))))

(defthm read-buffer-p-step-rbuf
    (implies (and (load-store-unit-p LSU)
		  (MA-state-p MA)
		  (MA-input-p sigs))
	     (read-buffer-p (step-rbuf LSU MA sigs))))
(in-theory (disable step-rbuf))

; The next state of the result latch of the LSU.
(defun step-LSU-lch (LSU MA sigs)
  (declare (xargs :guard (and (load-store-unit-p LSU)
			      (MA-state-p MA) (MA-input-p sigs))))
  (LSU-latch (b-and (b-not (flush-all? MA sigs))
		    (bs-ior (release-rbuf? LSU MA sigs)
			    (check-wbuf0? LSU)
			    (check-wbuf1? LSU)))
	     (b-if (b-ior (b-and (release-rbuf? LSU MA sigs)
				 (LSU-read-prohibited? LSU (MA-mem MA)
						       (SRF-su (MA-SRF MA))))
			  (b-and (b-ior (check-wbuf0? LSU)
					(check-wbuf1? LSU))
				 (LSU-write-prohibited? LSU (MA-mem MA)
							(SRF-su (MA-SRF MA)))))
		   #b110 0)
	     (b-if (release-rbuf? LSU MA sigs)
		   (rbuf-tag (LSU-rbuf LSU))
		   (b-if (check-wbuf0? LSU) (wbuf-tag (LSU-wbuf0 LSU))
			 (b-if (check-wbuf1? LSU) (wbuf-tag (LSU-wbuf1 LSU))
			       0)))
	     (b-if (b-and (rbuf-valid? (LSU-rbuf LSU))
			  (LSU-address-match? LSU))
		   (LSU-forward-wbuf LSU)
		   (b-if (bs-and (rbuf-valid? (LSU-rbuf LSU))
				 (b-not (LSU-read-prohibited?
					 LSU (MA-mem MA)
					 (SRF-su (MA-SRF MA))))
				 (b-not (LSU-read-stall? LSU sigs)))
			 (read-mem (rbuf-addr (LSU-rbuf LSU)) (MA-mem MA))
			 0))))

(defthm LSU-latch-p-step-LSU-lch
    (implies (and (load-store-unit-p LSU)
		  (MA-state-p MA)
		  (MA-input-p sigs))
	     (LSU-latch-p (step-LSU-lch LSU MA sigs))))
(in-theory (disable step-LSU-lch))

; The new write buffer entry value.  This represents the instruction
; issued from one of the reservation stations attached to the LSU.
(defun issued-write (LSU MA sigs)
  (declare (xargs :guard (and (load-store-unit-p LSU)
			      (MA-state-p MA) (MA-input-p sigs))))
  (let ((RS0 (LSU-RS0 LSU)) (RS1 (LSU-RS1 LSU)))
    (b-if (issue-LSU-RS0? LSU MA sigs)
	  (write-buffer (b-andc2 (LSU-RS-ld-st? RS0)
				 (flush-all? MA sigs))
			0 0 (LSU-RS-tag RS0)
			(b-if (LSU-RS-op RS0)
			      (addr (LSU-RS-val1 RS0))
			      (addr (+ (LSU-RS-val1 RS0) (LSU-RS-val2 RS0))))
			(LSU-RS-val3 RS0))
    (b-if (issue-LSU-RS1? LSU MA sigs)
	  (write-buffer (b-andc2 (LSU-RS-ld-st? RS1)
				 (flush-all? MA sigs))
			0 0 (LSU-RS-tag RS1)
			(b-if (LSU-RS-op RS1)
			      (addr (LSU-RS-val1 RS1))
			      (addr (+ (LSU-RS-val1 RS1) (LSU-RS-val2 RS1))))
			(LSU-RS-val3 RS1))
	  (write-buffer 0 0 0 0 0 0)))))

(defthm write-buffer-p-issued-write
    (implies (and (load-store-unit-p LSU)
		  (MA-state-p MA)
		  (MA-input-p sigs))
	     (write-buffer-p (issued-write LSU MA sigs))))
(in-theory (disable issued-write))

; Write buffer is designed in the same way as DQ is designed. 
; The content of the wbuf1 is passed to the write buffer 0.  Wbuf1-output
; represents the trickle-down value from wbuf1 to wbuf0.
(defun wbuf1-output (LSU MA sigs)
  (declare (xargs :guard (and (load-store-unit-p LSU)
			      (MA-state-p MA) (MA-input-p sigs))))
  (let ((wbuf1 (LSU-wbuf1 LSU)))
    (b-if (wbuf-valid? wbuf1)
	  (write-buffer
	   (b-andc2 (wbuf-valid? wbuf1)
		    (b-andc2 (flush-all? MA sigs) (wbuf-commit? wbuf1)))
	   (wbuf-complete? wbuf1)
	   (b-ior (wbuf-commit? wbuf1)
		  (b-and (commit-inst? MA)
			 (bv-eqv *rob-index-size*
				 (ROB-head (MA-ROB MA)) (wbuf-tag wbuf1))))
	   (wbuf-tag wbuf1)
	   (wbuf-addr wbuf1)
	   (wbuf-val wbuf1))
	  (issued-write LSU MA sigs))))

(defthm write-buffer-p-wbuf1-output
    (implies (and (load-store-unit-p LSU)
		  (MA-state-p MA)
		  (MA-input-p sigs))
	     (write-buffer-p (wbuf1-output LSU MA sigs))))
(in-theory (disable write-buffer-p))

; The updated wbuf0 entry when the stored write is not released. 
(defun update-wbuf0 (LSU MA sigs)
  (declare (xargs :guard (and (load-store-unit-p LSU)
			      (MA-state-p MA) (MA-input-p sigs))))
  (let ((wbuf0 (LSU-wbuf0 LSU)))
    (write-buffer (b-andc2 (wbuf-valid? wbuf0)
			   (b-andc2 (flush-all? MA sigs) (wbuf-commit? wbuf0)))
		  (b-ior (wbuf-complete? wbuf0) (check-wbuf0? LSU))
		  (b-ior (wbuf-commit? wbuf0)
			 (b-and (commit-inst? MA)
				(bv-eqv *rob-index-size*
					(ROB-head (MA-ROB MA))
					(wbuf-tag wbuf0))))
		  (wbuf-tag wbuf0)
		  (wbuf-addr wbuf0)
		  (wbuf-val wbuf0))))

(defthm write-buffer-p-update-wbuf0
    (implies (and (load-store-unit-p LSU)
		  (MA-state-p MA)
		  (MA-input-p sigs))
	     (write-buffer-p (update-wbuf0 LSU MA sigs))))
(in-theory (disable update-wbuf0))

; The updated wbuf1 entry when the stored write instruction is not
; passed to wbuf0.
(defun update-wbuf1 (LSU MA sigs)
  (declare (xargs :guard (and (load-store-unit-p LSU)
			      (MA-state-p MA) (MA-input-p sigs))))
  (let ((wbuf1 (LSU-wbuf1 LSU)))
    (write-buffer (b-andc2 (wbuf-valid? wbuf1)
			   (b-andc2 (flush-all? MA sigs) (wbuf-commit? wbuf1)))
		  (b-ior (wbuf-complete? wbuf1) (check-wbuf1? LSU))
		  (b-ior (wbuf-commit? wbuf1)
			 (b-and (commit-inst? MA)
				(bv-eqv *rob-index-size*
					(ROB-head (MA-ROB MA))
					(wbuf-tag wbuf1))))
		  (wbuf-tag wbuf1)
		  (wbuf-addr wbuf1)
		  (wbuf-val wbuf1))))

(defthm write-buffer-p-update-wbuf1
    (implies (and (load-store-unit-p LSU)
		  (MA-state-p MA)
		  (MA-input-p sigs))
	     (write-buffer-p (update-wbuf1 LSU MA sigs))))
(in-theory (disable update-wbuf1))

; The next state of write buffer 0.  If write buffer 0 is empty or
; a write operation is released in this cycle, write buffer 0 receives
; the trickle-down request from write buffer 1, represented by wbuf1-output.
; Otherwise, it keeps the original request stored in write buffer 0.
(defun step-wbuf0 (LSU MA sigs)
  (declare (xargs :guard (and (load-store-unit-p LSU)
			      (MA-state-p MA) (MA-input-p sigs))))
  (b-if (b-orc1 (wbuf-valid? (LSU-wbuf0 LSU)) (release-wbuf0? LSU sigs))
	(wbuf1-output LSU MA sigs)
	(update-wbuf0 LSU MA sigs)))

(defthm write-buffer-p-step-wbuf0
    (implies (and (load-store-unit-p LSU)
		  (MA-state-p MA)
		  (MA-input-p sigs))
	     (write-buffer-p (step-wbuf0 LSU MA sigs))))
(in-theory (disable step-wbuf0))

; The next state of write buffer 1.  There are two cases where write
; buffer 1 accepts a new write request; One case is that the write
; buffer is full, a write is released this cycle and a new write is
; issued.  The other case is write buffer 0 contains a write request
; which is not released in this cycle, and a new write is issued.
(defun step-wbuf1 (LSU MA sigs)
  (declare (xargs :guard (and (load-store-unit-p LSU)
			      (MA-state-p MA) (MA-input-p sigs))))
  (let ((wbuf0 (LSU-wbuf0 LSU)) (wbuf1 (LSU-wbuf1 LSU)))
    (b-if (b-ior (b-and (wbuf-valid? wbuf1) (release-wbuf0? LSU sigs))
		 (bs-and (b-not (wbuf-valid? wbuf1))
			 (wbuf-valid? wbuf0)
			 (b-not (release-wbuf0? LSU sigs))))
	  (issued-write LSU MA sigs)
	  (update-wbuf1 LSU MA sigs))))

(defthm write-buffer-p-step-wbuf1
    (implies (and (load-store-unit-p LSU)
		  (MA-state-p MA)
		  (MA-input-p sigs))
	     (write-buffer-p (step-wbuf1 LSU MA sigs))))
(in-theory (disable step-wbuf1))

; The next state of the LSU.
(defun step-LSU (MA sigs)
  (declare (xargs :guard (and (MA-state-p MA) (MA-input-p sigs))))
  (let ((LSU (MA-LSU MA)))
    (load-store-unit (step-rs1-head? LSU MA sigs)
		     (step-LSU-RS0 LSU MA sigs)
		     (step-LSU-RS1 LSU MA sigs)
		     (step-rbuf LSU MA sigs)
		     (step-wbuf0 LSU MA sigs)
		     (step-wbuf1 LSU MA sigs)
		     (step-LSU-lch LSU MA sigs))))

(defthm LSU-p-step-LSU
    (implies (and (MA-state-p MA) (MA-input-p sigs))
	     (load-store-unit-p (step-LSU MA sigs))))
(in-theory (disable step-LSU))

; The next state of the memory.
(defun step-mem (MA sigs)
  (declare (xargs :guard (and (MA-state-p MA) (MA-input-p sigs))))
  (let ((mem (MA-mem MA)) (LSU (MA-LSU MA)))
    (b-if (release-wbuf0? LSU sigs)
	  (write-mem (wbuf-val (LSU-wbuf0 LSU))
		     (wbuf-addr (LSU-wbuf0 LSU))
		     mem)
	  mem)))

(defthm mem-p-step-mem
    (implies (and (MA-state-p MA) (MA-input-p sigs))
	     (mem-p (step-mem MA sigs))))
(in-theory (disable step-mem))

(deflabel end-MA-step-functions)

;; The next state function of the pipelined machine.
;; It takes a pipeline state and returns the state one clock cycle later.
(defun MA-step (MA sigs)
  (declare (xargs :guard (and (MA-state-p MA) (MA-input-p sigs))))
  (MA-state (step-pc MA sigs)
	    (step-RF MA)
	    (step-SRF MA sigs)
	    (step-IFU MA sigs)
	    (step-BP MA sigs)
	    (step-DQ MA sigs)
	    (step-ROB MA sigs)
	    (step-IU MA sigs)
	    (step-MU MA sigs)
	    (step-BU MA sigs)
	    (step-LSU MA sigs)
	    (step-mem MA sigs)))

(defthm MA-state-p-MA-step
    (implies (and (MA-state-p MA) (MA-input-p sigs))
	     (MA-state-p (MA-step MA sigs))))

(in-theory (disable MA-step))

;; MA-stepn runs the pipelined machine n cycles from the initial
;; state MA.
(defun MA-stepn (MA sigs-lst n)
  (declare (xargs :guard (and (MA-state-p MA) (integerp n) (>= n 0)
			      (MA-input-listp sigs-lst)
			      (<= n (len sigs-lst)))
		  :verify-guards nil))
  (if (zp n)
      MA
      (MA-stepn (MA-step MA (car sigs-lst)) (cdr sigs-lst) (1- n))))

(verify-guards MA-stepn)
(defthm MA-state-p-MA-stepn
    (implies (and (MA-state-p MA) (MA-input-listp sigs-lst)
		  (<= n (len sigs-lst)))
	     (MA-state-p (MA-stepn MA sigs-lst n))))

(deflabel end-MA-def)

(deflabel begin-MA-flushed-def)
; The definition of a flushed state.  We consider the pipeline
; is flushed, when all latches contain no busy flag, and no external
; interrupt is on pending.
(defun IFU-empty? (IFU)
  (declare (xargs :guard (IFU-p IFU)))
  (b-not (IFU-valid? IFU)))

(defun reg-ref-empty? (idx DQ)
  (declare (xargs :guard (and (DQ-p DQ) (rname-p idx))))
  (b-not (reg-ref-wait? (reg-tbl-nth idx (DQ-reg-tbl DQ)))))

(defun reg-tbl-empty-under? (idx DQ)
  (declare (xargs :guard (and (DQ-p DQ) (integerp idx)
			      (<= 0 idx) (<= idx *num-regs*))
		  :verify-guards nil))
  (if (zp idx)
      1
      (b-and (reg-ref-empty? (1- idx) DQ)
	     (reg-tbl-empty-under? (1- idx) DQ))))

(defthm bitp-reg-tbl-empty-under
    (bitp (reg-tbl-empty-under? idx DQ)))

(verify-guards reg-tbl-empty-under?
	       :hints (("goal" :in-theory (enable rname-p
						  unsigned-byte-p))))

(defun reg-tbl-empty? (DQ)
  (declare (xargs :guard (DQ-p DQ)))
  (reg-tbl-empty-under? *num-regs* DQ))

(defun sreg-ref-empty? (idx DQ)
  (declare (xargs :guard (and (srname-p idx) (DQ-p DQ))
		  :guard-hints (("goal" :in-theory (enable SRNAME-P)))))
  (b-not (reg-ref-wait? (sreg-tbl-nth idx (DQ-sreg-tbl DQ)))))

(defun sreg-tbl-empty? (DQ)
  (declare (xargs :guard (DQ-p DQ)))
  (b-and (sreg-ref-empty? 0 DQ) (sreg-ref-empty? 1 DQ)))

(defun DQ-empty? (DQ)
  (declare (xargs :guard (DQ-p DQ)))
  (bs-and (b-not (DE-valid? (DQ-DE0 DQ)))
	  (b-not (DE-valid? (DQ-DE1 DQ)))
	  (b-not (DE-valid? (DQ-DE2 DQ)))
	  (b-not (DE-valid? (DQ-DE3 DQ)))
	  (reg-tbl-empty? DQ)
	  (sreg-tbl-empty? DQ)))

(defun IU-empty? (IU)
  (declare (xargs :guard (integer-unit-p IU)))
  (bs-and (b-not (RS-valid? (IU-rs0 IU)))
	  (b-not (RS-valid? (IU-rs1 IU)))))

(defun MU-empty? (MU)
  (declare (xargs :guard (mult-unit-p MU)))
  (bs-and (b-not (RS-valid? (MU-rs0 MU)))
	  (b-not (RS-valid? (MU-rs1 MU)))
	  (b-not (MU-latch1-valid? (MU-lch1 MU)))
	  (b-not (MU-latch2-valid? (MU-lch2 MU)))))

(defun BU-empty? (BU)
  (declare (xargs :guard (branch-unit-p BU)))
  (bs-and (b-not (BU-RS-valid? (BU-rs0 BU)))
	  (b-not (BU-RS-valid? (BU-rs1 BU)))))

(defun LSU-empty? (LSU)
  (declare (xargs :guard (load-store-unit-p LSU)))
  (bs-and (b-not (LSU-RS-valid? (LSU-rs0 LSU)))
	  (b-not (LSU-RS-valid? (LSU-rs1 LSU)))
	  (b-not (LSU-latch-valid? (LSU-lch LSU)))
	  (b-not (wbuf-valid? (LSU-wbuf0 LSU)))
	  (b-not (wbuf-valid? (LSU-wbuf1 LSU)))
	  (b-not (rbuf-valid? (LSU-rbuf LSU)))))

(defun exintr-flag? (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (ROB-exintr? (MA-ROB MA)))

; The flushed state of the pipelined design.
(defun MA-flushed? (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (bs-and (IFU-empty? (MA-IFU MA))
	  (DQ-empty? (MA-DQ MA))
	  (ROB-empty? (MA-ROB MA))
	  (ROB-entries-empty? (MA-ROB MA))
	  (IU-empty? (MA-IU MA))
	  (MU-empty? (MA-MU MA))
	  (BU-empty? (MA-BU MA))
	  (LSU-empty? (MA-LSU MA))
	  (b-not (exintr-flag? MA))))

(defthm bitp-MA-flushed? (bitp (MA-flushed? MA)))

(defun flushed-p (MA) (b1p (MA-flushed? MA)))

(deflabel end-MA-flushed-def)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  Number of Commits
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun num-commits (MA sigs-lst n)
  (declare (xargs :guard (and (MA-state-p MA) (MA-input-listp sigs-lst)
			      (integerp n) (<= 0 n))
		  :measure (nfix n)))
  (if (or (zp n) (endp sigs-lst))
      0
      (b-if (b-ior (commit-inst? MA)
		   (ex-intr? MA (car sigs-lst)))
	    (1+ (num-commits (MA-step MA (car sigs-lst))
			     (cdr sigs-lst) (1- n)))
	    (num-commits (MA-step MA (car sigs-lst)) (cdr sigs-lst) (1- n)))))

(deftheory MA-state-def
    (set-difference-theories (function-theory 'end-MA-state)
			     (function-theory 'begin-MA-state)))
(deftheory MA-step-functions
    (set-difference-theories (function-theory 'end-MA-step-functions)
			     (function-theory 'begin-MA-step-functions)))

(deftheory MA-def
    (set-difference-theories (function-theory 'end-MA-def)
			     (function-theory 'begin-MA-def)))

(deftheory low-level-MA-def
    (set-difference-theories (theory 'MA-def) '(ma-step MA-stepn)))

(deftheory MA-def-all
    (union-theories (theory 'MA-def)
		    (theory 'MA-state-def)))

(deftheory MA-flushed-def
    (set-difference-theories (universal-theory 'end-MA-flushed-def)
			     (universal-theory 'begin-MA-flushed-def)))

(in-theory (disable MA-flushed? IFU-empty? DQ-empty? IU-empty?
		    MU-empty? BU-empty? LSU-empty? exintr-flag?
		    reg-tbl-empty? sreg-tbl-empty? reg-ref-empty?))

(in-theory (disable MA-def))

#|

Here is a simple example program for our pipelined machine.

Our program calculates the factorial of the number at address #x800 and stores
it at address #x801.

Initial memory setting:

#x0: ST R0,(#x50)
#x1: LD R0,(#x3)
#x2: BZ R0, 0
#x3: 0

#x10: ST R0,(#x50)
#x11: LD R0,(#x13)
#x12: BZ R0, 0
#x13: 0

#x20: ST R0,(#x50)
#x21: LD R0,(#x23)
#x22: BZ R0, 0
#x23: 0

#x30: ST R0,(#x50)
#x31: LD R0,(#x33)
#x32: BZ R0, 0
#x33: 0

#x60: 0
#x61: 1
#x62: 2
#x63: -1

#x70: #x400
#x71: #x800

#x100: LD R15,(#x70) ; program base
#x101: LD R14,(#x71) ; data base
#x102: LD R0, (#x60) ; 0
#x103: LD R1, (#x61) ; 1
#x104: LD R2, (#x62) ; 2
#x105: LD R3, (#x63) ; -1
#x106: MTSR SR0,R15
#x107: MTSR SR1,R0
#x108: RFEH

Initial memory image:
#x400     LD R5,(R14+R0) ; R5 holds counter
#x401     ADD R6, R0, R1     ; R6 holds factorial. Initially 1.
Loop:
#x402:    Mul R6, R6, R5  ; counter * fact -> fact
#x403:    ADD R5, R5, R3  ; decrement fact
#x404:    BZ  R5, Exit; if counter is zero, exit
#x405:    BZ  R0, Loop ; always jump to loop
EXIT:
#x406: ST  R6, (R14+R1)
#x407: SYNC
#x408: Trap

#x800: 5
#x801: 0
#x802: 5 ; Offset to Loop
#x803: 9 ; Offset to Exit
|#

; How to run the program:
; 1. certify and compile all the proof scripts.
;    (You may skip this, but the execution will be slow.)
; 2. Run ACL2.
; 3. Type command '(ld "MA-def.lisp")'.
; 4  Evaluate expressions below and set initial state MA.
; 5. You can run the MA machine for one cycle by
;    (MA-step (@ MA) (MA-input-p 0 1 1)).
;    You can also run the machine for multiple cycles with MA-stepn.
;    For instance, if you want to run the machine 15 cycles, type:
;      (assign sigs-list (make-list 15 :initial-element (MA-input 0 1 1)))
;      (MA-stepn (@ MA) 15 sigs-list).
; 
; 6  Following macro may be useful to evaluate "expr" and set it to variable
;    MA, without printing the state of memory.
; 
; ; Evaluate expression expr and set the result to MA.
; (defmacro eval-set-print-MA (MA expr)
;   `(pprogn (f-put-global ',MA ,expr state)
;            (mv nil
; 	     (list (MA-pc (f-get-global ',MA state))
;  	           (MA-RF (f-get-global ',MA state))
; 	           (MA-SRF (f-get-global ',MA state))
;     	           (MA-DQ (f-get-global ',MA state))
;     	           (MA-ROB (f-get-global ',MA state))
; 	           (MA-IU (f-get-global ',MA state))
; 	           (MA-MU (f-get-global ',MA state))
; 	           (MA-BU (f-get-global ',MA state))
;     	           (MA-LSU (f-get-global ',MA state)))
; 	      state)))

#|
; Function to be used in MA-step-seq
(defun make-MA-step-seq (sigs seq)
  (if (endp seq) nil
      (if (endp (cdr seq)) nil
	  (cons `(f-put-global ',(cadr seq) (MA-step (@ ,(car seq)) ,sigs)
		             state)
		(make-MA-step-seq sigs (cdr seq))))))

; Given an MA inputs and sequence of symbols, and execute MA-step one
; at a time and assigns its result to the symbol in the sequence.  For
; instance, (MA-step-seq (@ sigs) MA0 MA1 MA2 MA3) assigns the result
; of applying MA-step to MA0 to MA1, the result of applying MA-step to
; MA1 to MA2, and so on.
(defmacro MA-step-seq (sigs &rest seq)
  (if (endp seq) nil
      `(pprogn
	,@(make-MA-step-seq sigs seq)
	(mv nil
	 (list (MA-pc (f-get-global ',(car (last seq)) state))
	  (MA-RF (f-get-global ',(car (last seq)) state))
	  (MA-SRF (f-get-global ',(car (last seq)) state))
	  (MA-ROB (f-get-global ',(car (last seq)) state)))
	  state))))

(defmacro pr-MA (MA)
  `(list (MA-pc (@ ,MA)) (MA-RF (@ ,MA)) (MA-SRF (@ ,MA))
    (MA-IFU (@ ,MA)) (MA-DQ (@ ,MA)) (MA-ROB (@ ,MA)) (MA-IU (@ ,MA))
    (MA-MU (@ ,MA)) (MA-BU (@ ,MA)) (MA-LSU (@ ,MA))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Initial State Setting
(progn
(assign RF '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
(assign SRF (SRF 1 0 0))

(assign IFU (IFU 0 0 0 0))
(assign DE (dispatch-entry 0 0 0 0 0 0 0 0 0))
(assign reg-MA (reg-ref 0 0))
(assign reg-tbl (make-list *num-regs* :initial-element (@ reg-MA)))
(assign sreg-tbl (sreg-tbl (@ reg-MA) (@ reg-MA)))
(assign DQ (DQ (@ DE) (@ DE) (@ DE) (@ DE) (@ reg-tbl) (@ sreg-tbl)))

(assign ROBE (ROB-entry 0 0 0 0 0 0 0 0 0 0 0 0 0))
(assign entries (make-list *rob-size* :initial-element (@ ROBE)))
(assign ROB (ROB 0 0 0 0 (@ entries)))

(assign IU (integer-unit (RS 0 0 0 0 0 0 0 0 0) (RS 0 0 0 0 0 0 0 0 0)))
(assign MU (mult-unit (RS 0 0 0 0 0 0 0 0 0) (RS 0 0 0 0 0 0 0 0 0)
		      (MU-latch1 0 0 0) (MU-latch2 0 0 0)))
(assign BU (branch-unit (BU-RS 0 0 0 0 0) (BU-RS 0 0 0 0 0)))
(assign LSU (load-store-unit 0
			     (LSU-RS 0 0 0 0  0 0 0 0 0 0 0 0 0)
			     (LSU-RS 0 0 0 0  0 0 0 0 0 0 0 0 0)
			     (read-buffer 0 0 0 0 0)
			     (write-buffer 0 0 0 0 0 0)
			     (write-buffer 0 0 0 0 0 0)
			     (LSU-latch 0 0 0 0)))
(assign mem-alist '(
; Exception Handler
(#x0 . #x7050) ; ST R0,(#x50)
(#x1 . #x6003) ; LD R0,(#x3)
(#x2 . #x2000) ; BZ R0, 0
(#x3 . 0)
; Exception Handler
(#x10 . #x7050) ; ST R0,(#x50)
(#x11 . #x6013) ; LD R0,(#x13)
(#x12 . #x2000) ; BZ R0, 0
(#x13 . 0)
; Exception Handler
(#x20 . #x7050) ; ST R0,(#x50)
(#x21 . #x6023) ; LD R0,(#x23)
(#x22 . #x2000) ; BZ R0, 0
(#x23 . 0)

; Exception Handler
(#x30 . #x7050) ; ST R0,(#x50)
(#x31 . #x6033) ; LD R0,(#x33)
(#x32 . #x2000) ; BZ R0, 0
(#x33 . 0)

; Kernel Data Section
(#x60 .  0)
(#x61 . 1)
(#x62 . 2)
(#x63 . #xFFFF) ; -1
(#x70 . #x400)
(#x71 . #x800)
; Kernel Dispatching code
(#x100 . #x6F70) ; LD R15,(#x70) ; program base
(#x101 . #x6E71) ;  LD R14,(#x71) ; data base
(#x102 . #x6060) ;  LD R0, (#x60) ; 0
(#x103 . #x6161) ;  LD R1, (#x61) ; 1
(#x104 . #x6262) ; LD R2, (#x62) ; 2
(#x105 . #x6363) ; LD R3, (#x63) ; -1
(#x106 . #xAF00) ;  MTSR SR0,R15
(#x107 . #xA010) ;  MTSR SR1,R0
(#x108 . #x8000) ; #x103: RFEH
; Program
(#x400 . #x35E0) ;  LD R5,(R14+R0) ; R5 holds counter
(#x401 . #x0601) ;  ADD R6, R0, R1     ; R6 holds factorial. Initially 1.
; Loop:
(#x402 . #x1665) ;  Mul R6, R6, R5  ; counter * fact -> fact
(#x403 . #x0553) ;  ADD R5, R5, R3  ; decrement fact
(#x404 . #x2502) ;  BZ  R5, Exit; if counter is zero, exit
(#x405 . #x20FD) ;  BZ  R0, Loop ; always jump to loop
; EXIT:
(#x406 . #x46E1) ; ST  R6, (R14+R1)
(#x407 . #x5000) ; SYNC
(#x408 . #xB000) ; Trap

; Data Section
(#x800 . 5)
(#x801 . 0)
(#x802 . 5) ; Offset to Loop
(#x803 . 9) ; Offset to Exit
))

(assign mem (set-page-mode *read-only* 1 (compress1 'mem *init-mem*)))
(assign mem (set-page-mode *read-write* 2 (@ mem)))
(assign mem (compress1 'mem (load-mem-alist (@ mem-alist) (@ mem))))
(assign MA (MA-state #x100 (@ RF) (@ SRF) (@ IFU) (@ DQ) (@ ROB)
		    (@ IU) (@ MU) (@ BU) (@ LSU) (@ mem)))

)
|#
