;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; MAETT-def.lisp:
; Author  Jun Sawada, University of Texas at Austin
;
;  This book defines the MAETT for our microarchitectural design.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "ACL2")

(include-book "ISA-def")
(include-book "MA2-def")
(include-book "utils")


(deflabel begin-MAETT-def)

;; Defining projection from MA states to ISA states.
(defun proj (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (ISA-state (MA-pc MA)
	     (MA-RF MA)
	     (MA-SRF MA)
	     (MA-mem MA)))

(defthm ISA-state-p-proj
    (implies (MA-state-p MA) (ISA-state-p (proj MA))))

(defthm ISA-pc-proj
    (implies (MA-state-p MA) (equal (ISA-pc (proj MA)) (MA-pc MA))))

(defthm ISA-mem-proj
    (implies (MA-state-p MA)
	     (equal (ISA-mem (proj MA)) (MA-mem MA))))

(defthm ISA-RF-proj
    (implies (MA-state-p MA)
	     (equal (ISA-RF (proj MA)) (MA-RF MA))))

(defthm ISA-SRF-proj
    (implies (MA-state-p MA)
	     (equal (ISA-SRF (proj MA)) (MA-SRF MA))))

(in-theory (disable proj))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Here begins the definition of MAETT
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deflabel begin-MA-stg-def)

(defun IFU-stg-p (stg)
  (declare (xargs :guard t))
  (equal stg '(IFU)))

(defun DQ-stg-p (stg)
  (declare (xargs :guard t))
  (or (equal stg '(DQ 0))
      (equal stg '(DQ 1))
      (equal stg '(DQ 2))
      (equal stg '(DQ 3))))

(defun DQ-stg-idx (stg)
  (declare (xargs :guard (DQ-stg-p stg)))
  (cadr stg))

(defthm type-DQ-stg
    (implies (DQ-stg-p stg)
	     (and (integerp (DQ-stg-idx stg))
		  (<= 0 (DQ-stg-idx stg))))
  :rule-classes ((:type-prescription)
		 (:rewrite :corollary
			   (implies (DQ-stg-p stg)
				    (integerp (DQ-stg-idx stg))))
		 (:linear :corollary
			  (implies (DQ-stg-p stg)
				   (<= 0 (DQ-stg-idx stg))))))

(defun IU-stg-p (stg)
  (declare (xargs :guard t))
  (or (equal stg '(IU RS0))
      (equal stg '(IU RS1))))

(defun BU-stg-p (stg)
  (declare (xargs :guard t))
  (or (equal stg '(BU RS0))
      (equal stg '(BU RS1))))

(defun MU-stg-p (stg)
  (declare (xargs :guard t))
  (or (equal stg '(MU RS0))
      (equal stg '(MU RS1))
      (equal stg '(MU lch1))
      (equal stg '(MU lch2))))

; Check if the stg represents a stage of an instruction in LSU.
; (LSU wbuf0) and (LSU wbuf1) represent a write at the write buffer with
; flag valid? on, but complete? and commit? off.  Then a write
; proceeds to a stage where it occupies both an write buffer entry and
; output latch.  These stages are represented by (LSU wbuf0 lch) or
; (LSU wbuf1 lch).
(defun LSU-stg-p (stg)
  (declare (xargs :guard t))
  (or (equal stg '(LSU RS0))
      (equal stg '(LSU RS1))
      (equal stg '(LSU rbuf))
      (equal stg '(LSU lch))
      (equal stg '(LSU wbuf0))
      (equal stg '(LSU wbuf1))
      (equal stg '(LSU wbuf0 lch))
      (equal stg '(LSU wbuf1 lch))))

; Execution stage.
(defun execute-stg-p (stg)
  (declare (xargs :guard t))
  (or (IU-stg-p stg)
      (MU-stg-p stg)
      (BU-stg-p stg)
      (LSU-stg-p stg)))

; An instruction has completed its execution and is waiting to be
; committed in the re-order buffer.  A memory write operation is not
; performed until the corresponding instruction commits.  Meanwhile
; the write buffer contains the corresponding write request. The stage
; of a store instruction which is at the complete stage is either
; (complete wbuf0) or (complete wbuf1) depending on the write buffer
; entry storing the corresponding write request.
(defun complete-stg-p (stg)
  (declare (xargs :guard t))
  (or (equal stg '(complete))
      (equal stg '(complete wbuf0))
      (equal stg '(complete wbuf1))))

; Commit stage only happens for a store instruction.  An instruction 
; at this stage does not have a corresponding ROB entry anymore.
; The write is waiting to be completed in the write buffer.
(defun commit-stg-p (stg)
  (declare (xargs :guard t))
  (or (equal stg '(commit wbuf0))
      (equal stg '(commit wbuf1))))

; Retired.  Everything is over.
(defun retire-stg-p (stg)
  (declare (xargs :guard t))
  (equal stg '(RETIRE)))

(defun stage-p (stg)
  (declare (xargs :guard t))
  (or (IFU-stg-p stg)
      (DQ-stg-p stg)
      (execute-stg-p stg)
      (complete-stg-p stg)
      (commit-stg-p stg)
      (retire-stg-p stg)))

(defun RS-stg-p (stg)
  (or (equal stg '(IU RS0))
      (equal stg '(IU RS1))
      (equal stg '(BU RS0))
      (equal stg '(BU RS1))
      (equal stg '(MU RS0))
      (equal stg '(MU RS1))
      (equal stg '(LSU RS0))
      (equal stg '(LSU RS1))))

(defun wbuf-stg-p (stg)
  (declare (xargs :guard t))
  (or (equal stg '(LSU wbuf0))
      (equal stg '(LSU wbuf1))
      (equal stg '(LSU wbuf0 lch))
      (equal stg '(LSU wbuf1 lch))
      (equal stg '(complete wbuf0))
      (equal stg '(complete wbuf1))
      (equal stg '(commit wbuf0))      
      (equal stg '(commit wbuf1))))

(defun wbuf0-stg-p (stg)
  (declare (xargs :guard t))
  (or (equal stg '(LSU wbuf0))
      (equal stg '(LSU wbuf0 lch))
      (equal stg '(complete wbuf0))
      (equal stg '(commit wbuf0))))

(defun wbuf1-stg-p (stg)
  (declare (xargs :guard t))
  (or (equal stg '(LSU wbuf1))
      (equal stg '(LSU wbuf1 lch))
      (equal stg '(complete wbuf1))
      (equal stg '(commit wbuf1))))

(deflabel end-MA-stg-def)

#|
Following is the definition of INST record.

ID:  Identity of i
modify?:  Whether i is modified by earlier STORE 
          instructions.  In a well-formed MAETT, this flag
	  is sticky in the sense that modify? flag of i is 1 if that
	  of the preceding instruction is 1.
specultv?: Whether the instruction is speculatively executed. This
	  flag is also sticky.
br-predict?: If i is a branch instruction, this field records the output of
	  branch prediction invoked by i.
exintr?: Record whether the i is interrupted by an external interrupt.
stg: The current pipeline stage of i.
tag: The index to the ROB entry in which i is stored.
     The same value is used for the tag of the instruction.
pre-ISA: The correct ISA state before executing i.
post-ISA: The correct ISA state after executing i.
|#

(defstructure INST
  (ID (:assert (naturalp ID) :type-prescription))
  (modified? (:assert (bitp modified?) :rewrite))
  (specultv? (:assert (bitp specultv?) :rewrite))
  (first-modified? (:assert (bitp first-modified?) :rewrite))
  (br-predict? (:assert (bitp br-predict?) :rewrite))
  (exintr? (:assert (bitp exintr?) :rewrite))
  (stg (:assert (stage-p stg) :rewrite))
  (tag (:assert (rob-index-p tag) :rewrite
		(:type-prescription (and (integerp tag) (<= 0 tag)))
		(:rewrite (acl2-numberp tag))))
  (pre-ISA (:assert (ISA-state-p pre-ISA) :rewrite))
  (post-ISA (:assert (ISA-state-p post-ISA) :rewrite))
  (:options :guards))

(deflist INST-listp (l)
  (declare (xargs :guard t))
  INST-p)

; Micro-architectural Execution Trace consists of several data items
; init-ISA:  the ISA state corresponding to the initial state of MA
; new-ID:  An ID which is incremented every cycle.
; dq-len: The number of valid entries in the dispatch queue.
; wb-len: The number of valid entries in the write buffer.
; rob-flg: The flag used to implement a circular buffer for ROB.
; rob-head: The ROB index to the first instruction in ROB.
; rob-tail: The ROB index to the last instruction in ROB.
; trace: The list of traced instructions.
(defstructure MAETT
  (init-ISA (:assert (ISA-state-p init-ISA) :rewrite))
  (new-ID (:assert (naturalp new-ID) :type-prescription))
  (dq-len (:assert (naturalp dq-len) :type-prescription))
  (wb-len (:assert (naturalp wb-len) :type-prescription))
  (rob-flg (:assert (bitp rob-flg) :rewrite))
  (rob-head (:assert (rob-index-p rob-head) :rewrite
		     (:type-prescription (integerp rob-head))))
  (rob-tail (:assert (rob-index-p rob-tail) :rewrite
		     (:type-prescription (integerp rob-tail))))
  (trace (:assert (INST-listp trace) :rewrite))
  (:options :guards (:conc-name MT-)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Definition of INST functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun dispatched-p (i)
  (declare (xargs :guard (inst-p i)))
  (or (execute-stg-p (INST-stg i)) (complete-stg-p (INST-stg i))
      (commit-stg-p (INST-stg i)) (retire-stg-p (INST-stg i))))

(defun committed-p (i)
  (declare (xargs :guard (inst-p i)))
  (or (commit-stg-p (INST-stg i)) (retire-stg-p (INST-stg i))))

(deflabel begin-of-MT-def)

(deflabel begin-INST-function-def)

(defun INST-pc (i)
  (declare (xargs :guard (INST-p i)))
  (ISA-pc (INST-pre-ISA i)))

(defthm addr-INST-pc
    (implies (INST-p i) (addr-p (INST-pc i))))

(defun INST-RF (i)
  (declare (xargs :guard (INST-p i)))
  (ISA-RF (INST-pre-ISA i)))

(defthm RF-p-INST-RF
    (implies (INST-p i) (RF-p (INST-RF i))))

(defun INST-SRF (i)
  (declare (xargs :guard (INST-p i)))
  (ISA-SRF (INST-pre-ISA i)))

(defthm SRF-p-INST-SRF
    (implies (INST-p i) (SRF-p (INST-SRF i))))

(defun INST-mem (i)
  (declare (xargs :guard (INST-p i)))
  (ISA-mem (INST-pre-ISA i)))

(defthm mem-p-INST-mem
    (implies (INST-p i) (mem-p (INST-mem i))))

(defun INST-su (i)
  (declare (xargs :guard (INST-p i)))
  (SRF-su (ISA-SRF (INST-pre-ISA i))))

(defthm bitp-INST-su
    (implies (INST-p i) (bitp (INST-su i))))

(defun INST-word (i)
  (declare (xargs :guard (INST-p i)))
  (read-mem (INST-pc i) (INST-mem i)))

(defthm word-p-INST-word
    (implies (INST-p i) (word-p (INST-word i))))

(defthm integerp-INST-word
    (implies (INST-p i) (integerp (INST-word i)))
  :rule-classes :type-prescription)

(defun INST-opcode (i)
  (declare (xargs :guard (INST-p i)))
  (opcode (INST-word i)))

(defthm opcd-p-INST-opcode
    (opcd-p (INST-opcode i)))

(defun INST-ra (i)
  (declare (xargs :guard (INST-p i)))
  (ra (INST-word i)))

(defthm rname-p-INST-ra
    (rname-p (INST-ra i)))
    
(defun INST-rb (i)
  (declare (xargs :guard (INST-p i)))
  (rb (INST-word i)))
  
(defthm rname-p-INST-rb
    (rname-p (INST-rb i)))

(defun INST-rc (i)
  (declare (xargs :guard (INST-p i)))
  (rc (INST-word i)))

(defthm rname-p-INST-rc
    (rname-p (INST-rc i)))

(defun INST-im (i)
  (declare (xargs :guard (INST-p i)))
  (im (INST-word i)))

(defthm immediate-p-INST-im
    (immediate-p (INST-im i)))

(defun INST-fetch-error? (i)
  (declare (xargs :guard (INST-p i)))
  (let ((s (INST-pre-ISA i)))  
    (read-error? (ISA-pc s) (ISA-mem s) (SRF-su (ISA-SRF s)))))

(defthm bitp-INST-fetch-error? (bitp (INST-fetch-error? i)))

(defun INST-decode-error? (i)
  (declare (xargs :guard (INST-p i)))
  (let ((s (INST-pre-ISA i)))  
    (decode-illegal-inst? (opcode (INST-word i))
			  (SRF-su (ISA-SRF s))
			  (INST-ra i))))

(defthm bitp-INST-decode-error? (bitp (INST-decode-error? i)))

(defun INST-load-error? (i)
  (declare (xargs :guard (INST-p i)))
  (let ((s (INST-pre-ISA i))
	(inst (INST-word i)))
    (let ((su (SRF-su (ISA-SRF s)))
	  (mem (ISA-mem s))
	  (RF (ISA-RF s)))
      (b-if (bv-eqv *opcode-size* (opcode inst) 6)
	    (read-error? (addr (im inst)) mem su)
      (b-if (bv-eqv *opcode-size* (opcode inst) 3)
	    (read-error? (addr (+ (read-reg (ra inst) RF)
				  (read-reg (rb inst) RF)))
			 mem su)
	    0)))))

(defthm bitp-INST-load-error? (bitp (INST-load-error? i)))
(in-theory (disable INST-load-error?))

(defun INST-store-error? (i)
  (declare (xargs :guard (INST-p i)))
  (let ((s (INST-pre-ISA i))
	(inst (INST-word i)))
    (let ((su (SRF-su (ISA-SRF s)))
	  (mem (ISA-mem s))
	  (RF (ISA-RF s)))
      (b-if (bv-eqv *opcode-size* (opcode inst) 7)
	    (write-error? (addr (im inst)) mem su)
      (b-if (bv-eqv *opcode-size* (opcode inst) 4)
	    (write-error? (addr (+ (read-reg (ra inst) RF)
				  (read-reg (rb inst) RF)))
			  mem su)
	    0)))))

(defthm bitp-INST-store-error? (bitp (INST-store-error? i)))
(in-theory (disable INST-store-error?))

(defun INST-data-access-error? (i)
  (declare (xargs :guard (INST-p i)))
  (b-ior (INST-load-error? i)
	 (INST-store-error? i)))

(defthm bitp-INST-data-access-error? (bitp (INST-data-access-error? i)))

(defun INST-excpt? (i)
  (declare (xargs :guard (INST-p i)))
  (bs-ior (INST-fetch-error? i)
	  (INST-decode-error? i)
	  (INST-data-access-error? i)))

(defthm bitp-INST-excpt (bitp (INST-excpt? i)))

(defun INST-fetch-error-detected-p (i)
  (declare (xargs :guard (INST-p i)))
  (let ((s (INST-pre-ISA i)))
    (b1p (read-error? (ISA-pc s) (ISA-mem s) (SRF-su (ISA-SRF s))))))

(defun INST-cntlv (i)
  (declare (xargs :guard (INST-p i)))
  (decode (INST-opcode i) (INST-br-predict? i)))

(defthm cntlv-p-INST-cntlv
    (implies (INST-p i) (cntlv-p (INST-cntlv i))))

(defun inst-br-target (i)
  (declare (xargs :guard (INST-p i)))
  (addr (+ (INST-pc i)
	   (logextu *addr-size* *immediate-size* (im (INST-word i))))))

(defthm addr-p-inst-br-target
    (addr-p (inst-br-target i)))

(defun INST-load-addr (i)
  (declare (xargs :guard (INST-p i)))
  (cond ((equal (INST-opcode i) 3)
	 (addr (+ (read-reg (INST-ra i) (ISA-RF (INST-pre-ISA i)))
		  (read-reg (INST-rb i) (ISA-RF (INST-pre-ISA i))))))
	((equal (INST-opcode i) 6) (addr (INST-im i)))
	(t 0)))

(defthm addr-p-INST-load-addr
    (addr-p (INST-load-addr i)))

(defun INST-store-addr (i)
  (declare (xargs :guard (INST-p i)))
  (cond ((equal (INST-opcode i) 4)
	 (addr (+ (read-reg (INST-ra i) (ISA-RF (INST-pre-ISA i)))
		  (read-reg (INST-rb i) (ISA-RF (INST-pre-ISA i))))))
	((equal (INST-opcode i) 7) (addr (INST-im i)))
	(t 0)))

(defthm addr-p-INST-store-addr
    (addr-p (INST-store-addr i)))

(defun INST-src-val1 (i)
  (declare (xargs :guard (INST-p i)))
  (let ((op (INST-opcode i))
	(ra (INST-ra i))
	(rc (INST-rc i))
	(im (INST-im i))
	(RF (ISA-RF (INST-pre-ISA i)))
	(SRF (ISA-SRF (INST-pre-ISA i))))
    (cond ((or (equal op 0) (equal op 1) (equal op 3) (equal op 4))
	   (read-reg ra RF))
	  ((or (equal op 6) (equal op 7))
	   (word im))
	  ((or (equal op 2) (equal op 10))
	   (read-reg rc RF))
	  ((equal op 9)
	   (read-sreg ra SRF))
	  (t 0))))

(defthm word-p-INST-src-val1
    (implies (INST-p i) (word-p (INST-src-val1 i))))
    
(defun INST-src-val2 (i)
  (declare (xargs :guard (INST-p i)))
  (read-reg (INST-rb i) (ISA-RF (INST-pre-ISA i))))

(defthm word-p-INST-src-val2
    (implies (INST-p i) (word-p (INST-src-val2 i))))

(defun INST-src-val3 (i)
  (declare (xargs :guard (INST-p i)))
  (read-reg (INST-rc i) (ISA-RF (INST-pre-ISA i))))
		   
(defthm word-p-INST-src-val3
    (implies (INST-p i) (word-p (INST-src-val3 i))))

(defun INST-ADD-dest-val (i)
  (declare (xargs :guard (INST-p i)))
  (word (+ (INST-src-val1 i) (INST-src-val2 i))))

(defthm word-p-INST-ADD-dest-val
    (word-p (INST-ADD-dest-val i)))

(defun INST-MULT-dest-val (i)
  (declare (xargs :guard (INST-p i)))
  (word (* (INST-src-val1 i) (INST-src-val2 i))))

(defthm word-p-INST-MULT-dest-val
    (word-p (INST-MULT-dest-val i)))

(defun INST-LD-dest-val (i)
  (declare (xargs :guard (INST-p i)))
  (read-mem (addr (+ (INST-src-val1 i) (INST-src-val2 i)))
	    (ISA-mem (INST-pre-ISA i))))

(defthm word-p-INST-LD-dest-val
    (implies (INST-p i) (word-p (INST-LD-dest-val i))))

(defun INST-LD-im-dest-val (i)
  (declare (xargs :guard (INST-p i)))
  (read-mem (addr (INST-src-val1 i)) (ISA-mem (INST-pre-ISA i))))

(defthm word-p-INST-LD-im-dest-val
    (implies (INST-p i) (word-p (INST-LD-im-dest-val i))))

(defun INST-MFSR-dest-val (i)
  (declare (xargs :guard (INST-p i)))
  (INST-src-val1 i))

(defthm word-p-INST-MFSR-dest-val
    (implies (INST-p i) (word-p (INST-MFSR-dest-val i))))

(defun INST-MTSR-dest-val (i)
  (declare (xargs :guard (INST-p i)))
  (INST-src-val1 i))

(defthm word-p-INST-MTSR-dest-val
    (implies (INST-p i) (word-p (INST-MTSR-dest-val i))))

; This is true for any instruction i which writes back its value to
; the register file or the special register file.
; INST-writeback-p is true if and only if INST-wb? is 1.
(defun INST-writeback-p (i)
  (declare (xargs :guard (INST-p i)))
  (let ((op (opcode (INST-word i))))
    (or (equal op 0) (equal op 1) (equal op 3) (equal op 6)
	(equal op 9) (equal op 10))))

(defun INST-dest-val (i)
  (declare (xargs :guard (INST-p i)))
  (let ((op (opcode (INST-word i))))
    (cond ((equal op 0)
	   (INST-ADD-dest-val i))
	  ((equal op 1)
	   (INST-MULT-dest-val i))
	  ((equal op 3)
	   (INST-LD-dest-val i))
	  ((equal op 6)
	   (INST-LD-im-dest-val i))
	  ((equal op 9)
	   (INST-MFSR-dest-val i))
	  ((equal op 10)
	   (INST-MTSR-dest-val i))
	  (t 0))))
	     
(defthm word-p-INST-dest-val
    (implies (INST-p i) (word-p (INST-dest-val i))))

(defun INST-dest-reg (i)
  (declare (xargs :guard (INST-p i)))
  (let ((op (opcode (INST-word i))))
    (cond ((or (equal op 0) (equal op 1) (equal op 3) (equal op 6)
	       (equal op 9))
	   (INST-rc i))
	  ((equal op 10) (INST-ra i))
	  (t 0))))

(defthm rname-p-INST-dest-reg
    (rname-p (INST-dest-reg i)))

(defun INST-IU? (i)
  (declare (xargs :guard (INST-p i)))
  (logbit 0 (cntlv-exunit (INST-cntlv i))))

(defthm bitp-INST-IU?
    (bitp (INST-IU? i)))

(defun INST-MU? (i)
  (declare (xargs :guard (INST-p i)))
  (logbit 1 (cntlv-exunit (INST-cntlv i))))

(defthm bitp-INST-MU?
    (bitp (INST-MU? i)))

(defun INST-LSU? (i)
  (declare (xargs :guard (INST-p i)))
  (logbit 2 (cntlv-exunit (INST-cntlv i))))

(defthm bitp-INST-LSU?
    (bitp (INST-LSU? i)))

(defun INST-BU? (i)
  (declare (xargs :guard (INST-p i)))
  (logbit 3 (cntlv-exunit (INST-cntlv i))))

(defthm bitp-INST-BU?
    (bitp (INST-BU? i)))

(defun INST-no-unit? (i)
  (declare (xargs :guard (INST-p i)))
  (logbit 4 (cntlv-exunit (INST-cntlv i))))

(defthm bitp-INST-no-unit?
    (bitp (INST-no-unit? i)))

(defun INST-ld-st? (i)
  (declare (xargs :guard (INST-p i)))
  (cntlv-ld-st? (INST-cntlv i)))

(defthm bitp-INST-ld-st? (bitp (INST-ld-st? i)))

(defun INST-store? (i)
  (declare (xargs :guard (INST-p i)))
  (b-and (INST-LSU? i) (INST-ld-st? i)))

(defthm bitp-INST-store?
    (bitp (INST-store? i)))

(defun INST-load? (i)
  (declare (xargs :guard (INST-p i)))
  (b-andc2 (INST-LSU? i) (INST-ld-st? i)))

(defthm bitp-INST-load?
    (bitp (INST-load? i)))

(defun INST-wb? (i)
  (declare (xargs :guard (INST-p i)))
  (cntlv-wb? (INST-cntlv i)))

(defthm bitp-INST-wb? (bitp (INST-wb? i)))

; INST-wb-SRF? is used to indicate whether the writeback value
; is directed to the special register file or the general register file.
(defun INST-wb-sreg? (i)
  (declare (xargs :guard (INST-p i)))
  (cntlv-wb-sreg? (INST-cntlv i)))

(defthm bitp-INST-wb-sreg? (bitp (INST-wb-sreg? i)))

(defun INST-sync? (i)
  (declare (xargs :guard (INST-p i)))
  (cntlv-sync? (INST-cntlv i)))

(defthm bitp-INST-sync? (bitp (INST-sync? i)))
    
(defun INST-rfeh? (i)
  (declare (xargs :guard (INST-p i)))
  (cntlv-rfeh? (INST-cntlv i)))

(defthm bitp-INST-rfeh (bitp (INST-rfeh? i)))

(defun INST-branch-dest (i)
  (declare (xargs :guard (INST-p i)))
  (addr (+ (logextu *addr-size* *immediate-size* (INST-im i))
	   (ISA-pc (INST-pre-ISA i)))))

(defthm addr-p-INST-branch-dest
    (addr-p (INST-branch-dest i)))

; Flags to indicate IU operation. If 0, add operation of source values
; val1 and val2.  If 1, IU simply returns an source operand val1.
(defun INST-IU-op? (i)
  (declare (xargs :guard (INST-p i)))
  (b-not (logbit 0 (cntlv-operand (INST-cntlv i)))))

(defthm bitp-INST-IU-op
    (bitp (INST-IU-op? i)))

; Operation flag for load store unit.  If this flag is on, 
; Immediate value is used as the memory access address.
; Note:
; I forgot what op originally meant.  In this function, op
; probably meant "operands" rather than "operation". See the definition
; of LSU-RS in MA2-def.
(defun INST-LSU-op? (i)
  (declare (xargs :guard (INST-p i)))
  (logbit 1 (cntlv-operand (INST-cntlv i))))

(defthm bitp-INST-LSU-op
    (bitp (INST-LSU-op? i)))

; INST-commit? is true if instruction i commits at this cycle. 
(defun INST-commit? (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))
  (bs-and (commit-inst? MA)
	  (if (complete-stg-p (INST-stg i)) 1 0)
	  (bv-eqv *rob-index-size* (ROB-head (MA-ROB MA))
		  (INST-tag i))))

(defthm bitp-INST-commit (bitp (INST-commit? i MA)))

(defun INST-cause-jmp? (i MT MA sigs)
  (declare (xargs :guard (and (INST-p i) (MAETT-p MT)
			      (MA-state-p MA) (MA-input-p sigs)))
; Matt K. mod: Added necessary ignorable declaration.
           (ignorable sigs))
  (bs-and (if (complete-stg-p (INST-stg i)) 1 0)
	  (bv-eqv *rob-index-size* (inst-tag i) (MT-rob-head MT))
	  (bs-ior (commit-jmp? MA)
		  (enter-excpt? MA)
		  (leave-excpt? MA))))

(defthm bitp-INST-cause-jmp (bitp (INST-cause-jmp? i MT MA sigs)))

(defun INST-exintr-now? (i MA sigs)
  (declare (xargs :guard (and (INST-p i)
			      (MA-state-p MA) (MA-input-p sigs))))
  (if (or (IFU-stg-p (INST-stg i)) (DQ-stg-p (INST-stg i)))
      (bs-and (ROB-empty? (MA-ROB MA))
	      (b-not (LSU-pending-writes? (MA-LSU MA)))
	      (b-ior (ROB-exintr? (MA-ROB MA))
		     (MA-input-exintr sigs)))
      0))

(defthm bitp-INST-exintr-now (bitp (INST-exintr-now? i MA sigs)))
				     
(defun INST-context-sync? (i)
  (declare (xargs :guard (INST-p i)))  
  (b-andc1 (INST-excpt? i)
	   (INST-sync? i)))

(defthm bitp-INST-context-sync (bitp (INST-context-sync? i)))

(defun INST-branch-taken? (i)
  (declare (xargs :guard (INST-p i)))  
  (let ((s (INST-pre-ISA i)))  
    (bv-eqv *word-size* (read-reg (rc (INST-word i)) (ISA-RF s)) 0)))

(defthm bitp-INST-branch-taken (bitp (INST-branch-taken? i)))

(defun INST-wrong-branch? (i)
  (declare (xargs :guard (INST-p i)))  
  (bs-and (b-not (INST-excpt? i))
	  (INST-BU? i)
	  (cond ((IFU-stg-p (INST-stg i))
		 (INST-branch-taken? i))
		(t (b-xor (INST-branch-taken? i)
			  (INST-br-predict? i))))))

(defthm bitp-INST-wrong-branch? (bitp (INST-wrong-branch? i)))

(defun INST-start-specultv? (i)
  (declare (xargs :guard (INST-p i)))
  (if (committed-p i)
      0
      (bs-ior (INST-excpt? i)
	      (INST-context-sync? i)
	      (INST-wrong-branch? i))))

(defthm bitp-INST-start-specultv (bitp (INST-start-specultv? i)))

(defun INST-decode-error-detected-p (i)
  (declare (xargs :guard (INST-p i)))
  (let ((op (INST-opcode i)))
    (and (not (INST-fetch-error-detected-p i))
	 (not (equal op 0))
	 (not (equal op 1))
	 (not (equal op 2))
	 (not (equal op 3))
	 (not (equal op 4))
	 (not (equal op 5))
	 (not (equal op 6))
	 (not (equal op 7))
	 (not (and (equal op 8) (b1p (INST-su i))))
	 (not (and (equal op 9) (b1p (INST-su i))
		   (or (equal (INST-ra i) 0) (equal (INST-ra i) 1))))
	 (not (and (equal op 10) (b1p (INST-su i))
		   (or (equal (INST-ra i) 0) (equal (INST-ra i) 1))))
	 (not (IFU-stg-p (INST-stg i))))))

(defun INST-load-accs-error-detected-p (i)
  (declare (xargs :guard (INST-p i)))
  (let ((s (INST-pre-ISA i)) (op (INST-opcode i)))
    (and (not (INST-fetch-error-detected-p i))
	 (or (equal op 3) (equal op 6))
	 (b1p (read-error? (INST-load-addr i)
			   (ISA-mem s)
			   (SRF-su (ISA-SRF s))))
	 (or (equal (INST-stg i) '(LSU lch))
	     (complete-stg-p (INST-stg i))
	     (commit-stg-p (INST-stg i))
	     (retire-stg-p (INST-stg i))))))

(defun INST-store-accs-error-detected-p (i)
  (declare (xargs :guard (INST-p i)))
  (let ((s (INST-pre-ISA i)) (op (INST-opcode i)))
    (and (not (INST-fetch-error-detected-p i))
	 (or (equal op 4) (equal op 7))
	 (b1p (write-error? (INST-store-addr i)
			    (ISA-mem s)
			    (SRF-su (ISA-SRF s))))
	 (or (equal (INST-stg i) '(LSU wbuf0 lch))
	     (equal (INST-stg i) '(LSU wbuf1 lch))
	     (complete-stg-p (INST-stg i))
	     (commit-stg-p (INST-stg i))
	     (retire-stg-p (INST-stg i))))))

(defun INST-data-accs-error-detected-p (i)
  (declare (xargs :guard (INST-p i)))
  (or (INST-load-accs-error-detected-p i)
      (INST-store-accs-error-detected-p i)))

(defun INST-excpt-detected-p (i)
  (declare (xargs :guard (INST-p i)))
  (or (INST-fetch-error-detected-p i)
      (INST-decode-error-detected-p i)
      (INST-data-accs-error-detected-p i)))

(defun INST-excpt-flags (i)
  (declare (xargs :guard (INST-p i)))
  (cond ((INST-fetch-error-detected-p i) #b101)
	((INST-decode-error-detected-p i) #b100)
	((INST-data-accs-error-detected-p i) #b110)
	(t 0)))

(defthm excpt-flags-p-INST-excpt-flags
    (excpt-flags-p (INST-excpt-flags i)))

(deflabel end-INST-function-def)

(defun trace-no-write-at (addr trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace)
      T
      (and (or (not (b1p (INST-store? (car trace))))
	       (not (equal (INST-store-addr (car trace)) addr))
	       (b1p (INST-excpt? (car trace)))
	       (b1p (INST-exintr? (car trace))))
	   (trace-no-write-at addr (cdr trace)))))

(defun MT-no-write-at (addr MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-no-write-at addr (MT-trace MT)))

(defun fetched-inst (MT pre-ISA specultv? modified?)
  (declare (xargs :guard (and (ISA-state-p pre-ISA) (MAETT-p MT)
			      (bitp specultv?)
			      (bitp modified?))))
  (INST (MT-new-ID MT)
	(b-orc2 modified?
		(if (MT-no-write-at (ISA-pc pre-ISA) MT) 1 0))
	specultv?
	(b-nor modified? (if (MT-no-write-at (ISA-pc pre-ISA) MT) 1 0))
	0
	0
	'(IFU)
	0
	pre-ISA
	(ISA-step pre-ISA (ISA-input 0))))

(defun exintr-INST (MT pre-ISA modified?)
  (declare (xargs :guard (and (ISA-state-p pre-ISA) (MAETT-p MT))))
  (INST (MT-new-ID MT)
	modified?
	0
	0
	0
	1
	'(retire)
	0
	pre-ISA
	(ISA-step pre-ISA (ISA-input 1))))

; Coerce-DQ-stg coerces argument len to an integer between 0 and 3.
; The result is an index to a dispatch queue entry.
(defun coerce-DQ-stg (len)
  (declare (xargs :guard t))
  (if (and (integerp len) (> len 3)) 3 (nfix len)))

(defthm type-coerce-DQ-stg
    (and (integerp (coerce-DQ-stg len))
	 (<= 0 (coerce-DQ-stg len)))
  :rule-classes :type-prescription)

(defthm range-coerce-DQ-stg
    (and (<= 0 (coerce-DQ-stg len))
	 (<= (coerce-DQ-stg len) 3))
  :rule-classes :linear)
(in-theory (disable coerce-DQ-stg))

(defun new-DQ-stage (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (let ((len (MT-dq-len MT)))
    (list 'DQ (b-if (dispatch-inst? MA)
		    (coerce-DQ-stg (1- len))
		    (coerce-DQ-stg len)))))

(defthm dq-stg-p-new-dq-stg
    (DQ-stg-p (new-DQ-stage MT MA))
  :hints (("goal" :in-theory (enable new-dq-stage dq-stg-p))))

(defun step-INST-IFU (i MT MA sigs)
  (declare (xargs :guard (and (INST-p i)
			      (MAETT-p MT)
			      (MA-state-p MA)
			      (MA-input-p sigs))))
  (b-if (DQ-full? (MA-DQ MA))
	i
	(b-if (IFU-branch-predict? (MA-IFU MA) MA sigs)
	      (update-INST i :stg (new-DQ-stage MT MA)
			   :br-predict? 1)
	      (update-INST i :stg (new-DQ-stage MT MA)
			   :br-predict? 0))))

(defthm INST-p-step-INST-IFU
    (implies (and (INST-p i) (MAETT-p MT)
		  (MA-state-p MA) (MA-input-p sigs))
	     (INST-p (step-INST-IFU i MT MA sigs))))
(in-theory (disable step-INST-IFU))

(defun dispatch-INST (i MA sigs)
  (declare (xargs :guard (and (INST-p i)
			      (MA-state-p MA) (MA-input-p sigs)))
; Matt K. mod: Added necessary ignorable declaration.
           (ignorable sigs))
  (cond ((b1p (dispatch-no-unit? MA))
	 (update-INST i :stg '(complete)
		      :tag (ROB-tail (MA-ROB MA))))
	((b1p (dispatch-to-IU? MA))
	 (b-if (select-IU-RS0? (MA-IU MA))
	       (update-INST i :stg '(IU RS0)
			    :tag (ROB-tail (MA-ROB MA)))
	       ; must be (select-IU-RS1? (MA-IU MA)) 
	       (update-INST i :stg '(IU RS1)
			    :tag (ROB-tail (MA-ROB MA)))))
	((b1p (dispatch-to-MU? MA))
	 (b-if (select-MU-RS0? (MA-MU MA))
	       (update-INST i :stg '(MU RS0)
			    :tag (ROB-tail (MA-ROB MA)))
	       ; must be (select-MU-RS1? (MA-MU MA))
	       (update-INST i :stg '(MU RS1)
			    :tag (ROB-tail (MA-ROB MA)))))
	((b1p (dispatch-to-BU? MA))
	 (b-if (select-BU-RS0? (MA-BU MA))
	       (update-INST i :stg '(BU RS0)
			    :tag (ROB-tail (MA-ROB MA)))
	       ; must be (select-BU-RS1? (MA-BU MA))
	       (update-INST i :stg '(BU RS1)
			    :tag (ROB-tail (MA-ROB MA)))))
	(t ; must be (dispatch-to-LSU? MA)
	 (b-if (select-LSU-RS0? (MA-LSU MA))
	       (update-INST i :stg '(LSU RS0)
			    :tag (ROB-tail (MA-ROB MA)))
	       ; must be (select-LSU-RS1? (MA-BU MA))	       
	       (update-INST i :stg '(LSU RS1)
			    :tag (ROB-tail (MA-ROB MA)))))))

(defun step-INST-DQ (i MT MA sigs)
  (declare (xargs :guard (and (INST-p i) (DQ-stg-p (INST-stg i))
			      (MAETT-p MT)
			      (MA-state-p MA) (MA-input-p sigs)))
; Matt K. mod: Added necessary ignorable declaration.
           (ignorable MT))
  (let ((idx (DQ-stg-idx (INST-stg i))))
    (b-if (dispatch-inst? MA)
	  (if (zp idx)
	      (dispatch-INST i MA sigs)
	      (update-INST i :stg (list 'DQ (nfix (1- idx)))))
	  i)))

(defthm INST-p-step-INST-DQ
    (implies (and (INST-p i) (MAETT-p MT)
		  (MA-state-p MA) (MA-input-p sigs))
	     (INST-p (step-INST-DQ i MT MA sigs))))
(in-theory (disable step-INST-DQ))

(defun step-INST-IU (i MA sigs)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA)
			      (IU-stg-p (INST-stg i))
			      (MA-input-p sigs)))
; Matt K. mod: Added necessary ignorable declaration.
           (ignorable sigs))
  (case (cadr (INST-stg i))
    (RS0 (b-if (issue-IU-RS0? (MA-IU MA) MA)
	       (update-INST i :stg '(complete))
	       i))
    (otherwise ; RS1
     (b-if (issue-IU-RS1? (MA-IU MA) MA)
	   (update-INST i :stg '(complete))
	   i))))

(defun step-INST-MU (i MA sigs)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA)
			      (MA-input-p sigs)))
; Matt K. mod: Added necessary ignorable declaration.
           (ignorable sigs))
  (let ((MU (MA-MU MA)))
    (case (cadr (INST-stg i))
      (RS0 (b-if (issue-MU-RS0? (MA-MU MA) MA)
		 (update-INST i :stg '(MU lch1))
		 i))
      (RS1
       (b-if (issue-MU-RS1? (MA-MU MA) MA)
	     (update-INST i :stg '(MU lch1))
	     i))
      (lch1
       (b-if (b-ior (CDB-for-MU? MA)
		    (b-not (MU-latch2-valid? (MU-lch2 MU))))
	     (update-INST i :stg '(MU lch2))
	     i))
      (otherwise ; lch2
       (b-if (CDB-for-MU? MA)
	     (update-INST i :stg '(complete))
	     i)))))
  
(defun step-INST-BU (i MA sigs)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA)
			      (MA-input-p sigs)))
; Matt K. mod: Added necessary ignorable declaration.
           (ignorable sigs))
  (let ((BU (MA-BU MA)))
    (case (cadr (INST-stg i))
      (RS0 (b-if (issue-BU-RS0? BU MA)
		 (update-INST i :stg '(complete))
		 i))
      (otherwise			; RS1
       (b-if (issue-BU-RS1? BU MA)
	     (update-INST i :stg '(complete))
	     i)))))

(defun INST-select-wbuf0? (MA sigs)
  (declare (xargs :guard (and (MA-state-p MA) (MA-input-p sigs))))
  (b-ior (b-not (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
	 (b-and (b-not (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		(release-wbuf0? (MA-LSU MA) sigs))))

(defun step-INST-LSU-RS0 (i MA sigs)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA) (MA-input-p sigs))))
  (let ((RS0 (LSU-RS0 (MA-LSU MA)))
	(LSU (MA-LSU MA)))
    (b-if (issue-LSU-RS0? LSU MA sigs)
	  (b-if (LSU-RS-ld-st? RS0)
		(b-if (INST-select-wbuf0? MA sigs)
		      (update-INST i :stg '(LSU wbuf0))
		; if wbuf1 is not selected 
		      (update-INST i :stg '(LSU wbuf1)))
		(update-INST i :stg '(LSU rbuf)))
	  i)))

(defun step-INST-LSU-RS1 (i MA sigs)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA) (MA-input-p sigs))))
  (let ((RS1 (LSU-RS1 (MA-LSU MA)))
	(LSU (MA-LSU MA)))
    (b-if (issue-LSU-RS1? LSU MA sigs)
	  (b-if (LSU-RS-ld-st? RS1)
		(b-if (INST-select-wbuf0? MA sigs)
		      (update-INST i :stg '(LSU wbuf0))
		; if not, wbuf1 is selected 
		      (update-INST i :stg '(LSU wbuf1)))
		(update-INST i :stg '(LSU rbuf)))
	  i)))

(defun step-INST-LSU-rbuf (i MA sigs)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA) (MA-input-p sigs))))
  (let ((LSU (MA-LSU MA)))
    (b-if (release-rbuf? LSU MA sigs)
	  (update-INST i :stg '(LSU lch))
	  i)))

(defun step-INST-LSU-lch (i)
  (declare (xargs :guard (INST-p i)))
  (update-INST i :stg '(complete)))

(defun step-INST-LSU-wbuf0 (i MA) 
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))
  (let ((LSU (MA-LSU MA)))
    (b-if (check-wbuf0? LSU)
	  (update-INST i :stg '(LSU wbuf0 lch))
	  i)))

(defun step-INST-LSU-wbuf0-lch (i)
  (declare (xargs :guard (INST-p i)))
  (update-INST i :stg '(complete wbuf0)))

(defun step-INST-LSU-wbuf1 (i MA sigs) 
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA) (MA-input-p sigs))))
  (let ((LSU (MA-LSU MA)))
    (b-if (check-wbuf1? LSU)
	  (update-INST i :stg '(LSU wbuf1 lch))
	  (b-if (release-wbuf0? LSU sigs)
		(update-INST i :stg '(LSU wbuf0))
		i))))

(defun step-INST-LSU-wbuf1-lch (i MA sigs)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA) (MA-input-p sigs))))
  (b-if (release-wbuf0? (MA-LSU MA) sigs)
	(update-INST i :stg '(complete wbuf0))
	(update-INST i :stg '(complete wbuf1))))

(defun step-INST-LSU (i MA sigs)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA) (MA-input-p sigs))))
  (cond ((equal (INST-stg i) '(LSU RS0)) (step-INST-LSU-RS0 i MA sigs))
	((equal (INST-stg i) '(LSU RS1)) (step-INST-LSU-RS1 i MA sigs))
	((equal (INST-stg i) '(LSU rbuf))
	 (step-INST-LSU-RBUF i MA sigs))
	((equal (INST-stg i) '(LSU lch)) (step-INST-LSU-lch i))
	((equal (INST-stg i) '(LSU wbuf0))
	 (step-INST-LSU-wbuf0 i MA))
	((equal (INST-stg i) '(LSU wbuf0 lch))
	 (step-INST-LSU-wbuf0-lch i))
	((equal (INST-stg i) '(LSU wbuf1))
	 (step-INST-LSU-wbuf1 i MA sigs))
	(t ; must be '(LSU wbuf1 lch)
	 (step-INST-LSU-wbuf1-lch i MA sigs))))

(defun step-INST-execute (i MA sigs)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA) (MA-input-p sigs))))
  (let ((stg (INST-stg i)))
    (cond ((IU-stg-p stg) (step-INST-IU i MA sigs))
	  ((MU-stg-p stg) (step-INST-MU i MA sigs))
	  ((BU-stg-p stg) (step-INST-BU i MA sigs))
	  (t ; must be (LSU-stg-p stg)
	   (step-INST-LSU i MA sigs)))))

(defthm INST-p-step-INST-execute
    (implies (and (INST-p i) (MAETT-p MT)
		  (MA-state-p MA) (MA-input-p sigs))
	     (INST-p (step-INST-execute i MA sigs))))
(in-theory (disable step-INST-execute))

; Describes the behavior of instruction i at the complete stage.  If
; it commits, an instruction generally retires. However, if it is a
; memory store instruction, we may still have a corresponding entry in
; the write buffer. In that case, the instruction goes into the commit
; stage, where the actual write operation takes place.  However, if
; exception is already detected for i, i retires when it is committed.
; So instructions at the commit stage cannot be an exception causing
; instruction.  An exception must be detected before the commit occurs
; in order to implement precise exceptions.
(defun step-INST-complete (i MA sigs)
  (declare (xargs :guard (and (INST-p i)
			      (MA-state-p MA) (MA-input-p sigs))))
  (cond ((equal (INST-stg i) '(complete))
	 (b-if (INST-commit? i MA)
	       (update-INST i :stg '(retire))
	       i))
	((equal (INST-stg i) '(complete wbuf0))
	 (b-if (b-and (INST-commit? i MA) (enter-excpt? MA))
	       (update-INST i :stg '(retire))
	 (b-if (INST-commit? i MA)
	       (update-INST i :stg '(commit wbuf0))
	       i)))
	(t ; must be (equal (INST-stg i) '(complete wbuf1))
	 (b-if (b-and (INST-commit? i MA) (enter-excpt? MA))
	       (update-INST i :stg '(retire))
	 (b-if (b-and (INST-commit? i MA) (release-wbuf0? (MA-LSU MA) sigs))
	       (update-INST i :stg '(commit wbuf0))
         (b-if (INST-commit? i MA)
	       (update-INST i :stg '(commit wbuf1))
	 (b-if (release-wbuf0? (MA-LSU MA) sigs)
	       (update-INST i :stg '(complete wbuf0))
	       i)))))))

(defthm INST-p-step-INST-complete
    (implies (and (INST-p i) (MAETT-p MT)
		  (MA-state-p MA) (MA-input-p sigs))
	     (INST-p (step-INST-complete i MA sigs))))
(in-theory (disable step-INST-complete))

(defun step-INST-commit (i MA sigs)
  (declare (xargs :guard (and (INST-p i)
			      (MA-state-p MA) (MA-input-p sigs))))
  (if (equal (INST-stg i) '(commit wbuf0))
      (if (b1p (release-wbuf0? (MA-LSU MA) sigs))
	  (update-INST i :stg '(retire))
	  i)
      ; must be (equal (INST-stg i) '(commit wbuf1))
      (if (b1p (release-wbuf0? (MA-LSU MA) sigs))
	  (update-INST i :stg '(commit wbuf0))
	  i)))

(defthm INST-p-step-INST-commit
    (implies (and (INST-p i) (MAETT-p MT)
		  (MA-state-p MA) (MA-input-p sigs))
	     (INST-p (step-INST-commit i MA sigs))))
(in-theory (disable step-INST-commit))

(defun step-INST (i MT MA sigs)
  (declare (xargs :guard (and (INST-p i) (MAETT-p MT)
			      (MA-state-p MA) (MA-input-p sigs))))
  (cond ((IFU-stg-p (INST-stg i))
	 (step-INST-IFU i MT MA sigs))
	((DQ-stg-p (INST-stg i))
	 (step-INST-DQ i MT MA sigs))
	((execute-stg-p (INST-stg i))
	 (step-INST-execute i MA sigs))
	((complete-stg-p (INST-stg i))
	 (step-INST-complete i MA sigs))
	((commit-stg-p (INST-stg i))
	 (step-INST-commit i MA sigs))
	(t ; retire
	 i)))

(defthm INST-p-step-INST
    (implies (and (INST-p i) (MAETT-p MT)
		  (MA-state-p MA) (MA-input-p sigs))
	     (INST-p (step-INST i MT MA sigs))))
(in-theory (disable step-INST))

(defun fetch-inst? (MA sigs)
  (declare (xargs :guard (and (MA-state-p MA) (MA-input-p sigs))
		  :guard-hints (("goal" :in-theory
					(enable IFU-fetch-prohibited?)))))
  (bs-and (b-not (flush-all? MA sigs))
	  (b-not (IFU-branch-predict? (MA-IFU MA) MA sigs))
	  (b-nand (IFU-valid? (MA-IFU MA)) (DQ-full? (MA-DQ MA)))
	  (b-ior (MA-input-fetch sigs)
		 (IFU-fetch-prohibited? (MA-pc MA) (MA-mem MA)
					(SRF-su (MA-SRF MA))))))

(defun step-MT-dq-len (MT MA sigs)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))))
  (b-if (flush-all? MA sigs)
	0
	(b-if (dispatch-inst? MA)
	      (b-if (b-andc1 (DQ-full? (MA-DQ MA)) (IFU-valid? (MA-IFU MA)))
		    (nfix (MT-dq-len MT))
		    (nfix (1- (MT-dq-len MT))))
	      (b-if (b-andc1 (DQ-full? (MA-DQ MA)) (IFU-valid? (MA-IFU MA)))
		    (nfix (1+ (MT-dq-len MT)))
		    (nfix (MT-dq-len MT))))))

(defthm type-step-MT-dq-len
    (and (integerp (step-MT-dq-len MT MA sigs))
	 (<= 0 (step-MT-dq-len MT MA sigs)))
  :rule-classes
  ((:type-prescription)
   (:rewrite :corollary
	     (integerp (step-MT-dq-len MT MA sigs)))
   (:linear  :corollary
	     (<= 0 (step-MT-dq-len MT MA sigs)))))

(in-theory (disable step-MT-dq-len))

(defun step-MT-wb-len (MT MA sigs)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))))
  (let ((LSU (MA-LSU MA)))
    (b-if (flush-all? MA sigs)
	  (b-if (release-wbuf0? LSU sigs)
		(b-if (b-and (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))
			     (wbuf-commit? (LSU-wbuf1 (MA-LSU MA))))
		      1 0)
		(b-if (b-and (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))
			     (wbuf-commit? (LSU-wbuf1 (MA-LSU MA))))
		      2
		      (b-if (b-and (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))
				   (wbuf-commit? (LSU-wbuf0 (MA-LSU MA))))
			    1 0)))
	  (b-if (b-ior (b-and (issue-LSU-RS0? LSU MA sigs)
			      (LSU-RS-ld-st? (LSU-RS0 LSU)))
		       (b-and (issue-LSU-RS1? LSU MA sigs)
			      (LSU-RS-ld-st? (LSU-RS1 LSU))))
		(b-if (release-wbuf0? LSU sigs)
		      (MT-wb-len MT)
		      (1+ (MT-wb-len MT)))
		(b-if (release-wbuf0? LSU sigs)
		      (nfix (1- (MT-wb-len MT)))
		      (MT-wb-len MT))))))
  
(defthm type-step-MT-wb-len
    (implies (and (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (and (integerp (step-MT-wb-len MT MA sigs))
		  (<= 0 (step-MT-wb-len MT MA sigs))))
  :rule-classes
  ((:type-prescription)
   (:rewrite :corollary
	     (implies (and (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
		      (integerp (step-MT-wb-len MT MA sigs))))
   (:linear  :corollary
	     (implies (and (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
		      (<= 0 (step-MT-wb-len MT MA sigs))))))
(in-theory (disable step-MT-wb-len))

(defun step-MT-ROB-flg (MT MA sigs)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))))
  (b-if (flush-all? MA sigs) 0
	(b-xor (MT-ROB-flg MT)
	       (b-xor (b-and (commit-inst? MA)
			     (logbit *rob-index-size* (+ 1 (MT-ROB-head MT))))
		      (b-and (dispatch-inst? MA)
			     (logbit *rob-index-size* (+ 1 (MT-ROB-tail MT))))))))

(defun step-MT-ROB-head (MT MA sigs)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))))
  (b-if (flush-all? MA sigs) 0
	(b-if (commit-inst? MA)
	      (rob-index (+ 1 (MT-ROB-head MT)))
	      (MT-ROB-head MT))))

(defthm rob-index-p-step-MT-rob-head
    (implies (and (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (rob-index-p (step-MT-rob-head MT MA sigs))))
(in-theory (disable step-MT-rob-head))

(defun step-MT-ROB-tail (MT MA sigs)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))))
  (b-if (flush-all? MA sigs) 0
	(b-if (dispatch-inst? MA)
	      (rob-index (+ 1 (MT-ROB-tail MT)))
	      (MT-ROB-tail MT))))

(defthm rob-index-p-step-MT-rob-tail
    (implies (and (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (rob-index-p (step-MT-rob-tail MT MA sigs))))
(in-theory (disable step-MT-rob-tail))

     
; MAETT trace updating function.
(defun step-trace (INST-list MT MA sigs pre-ISA specultv? modified?)
  (declare (xargs :guard (and (INST-listp INST-list)
			      (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
			      (ISA-state-p pre-ISA) (bitp specultv?)
			      (bitp modified?))))
  (if (endp INST-list)
      (b-if (fetch-inst? MA sigs)
	    (list (fetched-inst MT pre-ISA specultv? modified?))
	    (b-if (ex-intr? MA sigs)
		  (list (exintr-INST MT pre-ISA modified?))
		  nil))
      (b-if (INST-cause-jmp? (car INST-list) MT MA sigs)
	    (list (step-INST (car INST-list) MT MA sigs))
      (b-if (INST-exintr-now? (car INST-list) MA sigs)
	    (list (exintr-INST MT pre-ISA modified?))
	    (cons (step-INST (car INST-list) MT MA sigs)
		  (step-trace (cdr INST-list) MT MA sigs
			      (INST-post-ISA (car INST-list))
			      (b-ior (inst-specultv? (car INST-list))
				     (INST-start-specultv? (car INST-list)))
			      (INST-modified? (car INST-list))))))))
	    
(defthm INST-listp-step-MT-trace
    (implies (and (INST-listp INST-list)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (ISA-state-p ISA) (bitp spc) (bitp smc))
	     (INST-listp (step-trace INST-list MT MA sigs ISA spc smc))))
 
; MAETT step function.
(defun MT-step (MT MA sigs)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))))
  (MAETT (MT-init-ISA MT)
	 (1+ (MT-new-ID MT))
	 (step-MT-dq-len MT MA sigs)
	 (step-MT-wb-len MT MA sigs)
	 (step-MT-rob-flg MT MA sigs)
	 (step-MT-rob-head MT MA sigs)
	 (step-MT-rob-tail MT MA sigs)
	 (step-trace (MT-trace MT) MT MA sigs (MT-init-ISA MT) 0 0)))

(defthm MAETT-p-MT-step
    (implies (and (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (MAETT-p (MT-step MT MA sigs))))

(in-theory (disable MT-step))

; MAETT N-step function.
(defun MT-stepn (MT MA sig-list n)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA)
			      (MA-input-listp sig-list)
			      (integerp n)
			      (>= n 0))))
  (if (zp n)
      MT
      (if (endp sig-list)
	  MT
	  (MT-stepn (MT-step MT MA (car sig-list))
		    (MA-step MA (car sig-list))
		    (cdr sig-list)
		    (1- n)))))

(defthm MAETT-p-MT-stepn
    (implies (and (MAETT-p MT) (MA-state-p MA) (MA-input-listp sig-list))
	     (MAETT-p (MT-stepn MT MA sig-list n))))

(deflabel end-of-MT-def)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  Definition of init-MT
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun init-MT (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (MAETT (proj MA)
	 0 0 0 0			; ID  DQ-len  WB-len ROB-flg
	 (rob-head (MA-ROB MA))		; rob-head
	 (rob-tail (MA-ROB MA))		; rob-tail
	 nil))				; trace

(defthm MAETT-p-init-MT
    (implies (MA-state-p MA) (MAETT-p (init-MT MA))))
(in-theory (disable init-MT))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; An alternative definition of MT-step
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  We have an alternative definition of MT-step, which is defined as
;  MT-step*.  MT-step and MT-stepn* are slightly different. 
;  Because I need a some functional definitions used in the 
;  definition of MT-step.  See invariant-proof.lisp
;
;  Script Deleted in this file.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; INST-at-stg
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deflabel begin-INST-at-functions)

(defun INST-at-stg-in-trace (stg trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace)
      nil
      (if (equal stg (INST-stg (car trace)))
	  (car trace)
	  (INST-at-stg-in-trace stg (cdr trace)))))

(defun INST-at-stg (stg MT)
  (declare (xargs :guard (and (stage-p stg) (MAETT-p MT))))
  (INST-at-stg-in-trace stg (MT-trace MT)))

(defun no-INST-at-stg-in-trace (stg trace)
  (declare (xargs :guard (and (stage-p stg) (INST-listp trace))))  
  (if (endp trace)
      T
      (if (equal (INST-stg (car trace)) stg)
	  nil
	  (no-INST-at-stg-in-trace stg (cdr trace)))))

(defun uniq-INST-at-stg-in-trace (stg trace)
  (declare (xargs :guard (and (stage-p stg) (INST-listp trace))))  
  (if (endp trace)
      nil
      (if (equal (INST-stg (car trace)) stg)
	  (no-INST-at-stg-in-trace stg (cdr trace))
	  (uniq-INST-at-stg-in-trace stg (cdr trace)))))

(defun no-INST-at-stg (stg MT)
  (declare (xargs :guard (and (stage-p stg) (MAETT-p MT))))  
  (no-INST-at-stg-in-trace stg (MT-trace MT)))

(defun uniq-INST-at-stg (stg MT)
  (declare (xargs :guard (and (stage-p stg) (MAETT-p MT))))  
  (uniq-INST-at-stg-in-trace stg (MT-trace MT)))

(defun INST-at-stgs-in-trace (stgs trace)
  (declare (xargs :guard (and (true-listp stgs) (INST-listp trace))))
  (if (endp trace)
      nil
      (if (member-equal (INST-stg (car trace)) stgs)
	  (car trace)
	  (INST-at-stgs-in-trace stgs (cdr trace)))))

(defun INST-at-stgs (stgs MT)
  (declare (xargs :guard (and (true-listp stgs) (MAETT-p MT))))
  (INST-at-stgs-in-trace stgs (MT-trace MT)))

(defun no-INST-at-stgs-in-trace (stgs trace)
  (declare (xargs :guard (and (true-listp stgs) (INST-listp trace))))
  (if (endp trace)
      T
      (if (member-equal (INST-stg (car trace)) stgs)
	  nil
	  (no-INST-at-stgs-in-trace stgs (cdr trace)))))

(defun uniq-INST-at-stgs-in-trace (stgs trace)
  (declare (xargs :guard (and (true-listp stgs) (INST-listp trace))))
  (if (endp trace)
      nil
      (if (member-equal (INST-stg (car trace)) stgs)
	  (no-INST-at-stgs-in-trace stgs (cdr trace))
	  (uniq-INST-at-stgs-in-trace stgs (cdr trace)))))

(defun no-INST-at-stgs (stgs MT)
  (declare (xargs :guard (and (true-listp stgs) (MAETT-p MT))))
  (no-INST-at-stgs-in-trace stgs (MT-trace MT)))

(defun uniq-INST-at-stgs (stgs MT)
  (declare (xargs :guard (and (true-listp stgs) (MAETT-p MT))))
  (uniq-INST-at-stgs-in-trace stgs (MT-trace MT)))

(defun inst-of-tag-in-trace (tg trace)
  (declare (xargs :guard (and (rob-index-p tg) (INST-listp trace))))
  (if (endp trace)
      nil
      (if (and (equal (inst-tag (car trace)) tg)
	       (dispatched-p (car trace))
	       (not (committed-p (car trace))))
	  (car trace)
	  (inst-of-tag-in-trace tg (cdr trace)))))

(defun inst-of-tag (tg MT)
  (declare (xargs :guard (and (rob-index-p tg) (MAETT-p MT))))
  (inst-of-tag-in-trace tg (MT-trace MT)))

(defun no-inst-of-tag-in-trace (tg trace)
  (declare (xargs :guard (and (rob-index-p tg) (INST-listp trace))))  
  (if (endp trace)
      T
      (if (and (equal (inst-tag (car trace)) tg)
	       (dispatched-p (car trace))
	       (not (committed-p (car trace))))
	  nil
	  (no-inst-of-tag-in-trace tg (cdr trace)))))

(defun uniq-inst-of-tag-in-trace (tg trace)
  (declare (xargs :guard (and (rob-index-p tg) (INST-listp trace))))  
  (if (endp trace)
      nil
      (if (and (equal (inst-tag (car trace)) tg)
	       (dispatched-p (car trace))
	       (not (committed-p (car trace))))
	  (no-inst-of-tag-in-trace tg (cdr trace))
	  (uniq-inst-of-tag-in-trace tg (cdr trace)))))

(defun no-inst-of-tag (tg MT)
  (declare (xargs :guard (and (rob-index-p tg) (MAETT-p MT))))  
  (no-inst-of-tag-in-trace tg (MT-trace MT)))

(defun uniq-inst-of-tag (tg MT)
  (declare (xargs :guard (and (rob-index-p tg) (MAETT-p MT))))  
  (uniq-inst-of-tag-in-trace tg (MT-trace MT)))

(deflabel end-INST-at-functions)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Defining Theories
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deftheory MA-stg-def
    (set-difference-theories (function-theory 'end-MA-stg-def)
			     (function-theory 'begin-MA-stg-def)))

(deftheory MT-def
    (set-difference-theories (function-theory 'end-of-MT-def)
			     (function-theory 'begin-of-MT-def)))

(deftheory MT-def-non-rec-functions
    (non-rec-functions (theory 'MT-def) world))

(deftheory INST-at-functions
    (set-difference-theories (function-theory 'end-INST-at-functions)
			     (function-theory 'begin-INST-at-functions)))

(deftheory INST-function-def
    (definition-theory 
	(set-difference-theories (universal-theory 'end-INST-function-def)
				 (universal-theory 'begin-INST-function-def))))

(deftheory INST-at-non-rec-functions
    (non-rec-functions (theory 'INST-at-functions) world))
			     
(in-theory (disable MT-def-non-rec-functions))
(in-theory (disable MA-stg-def))
(in-theory (disable INST-at-non-rec-functions))
(in-theory (disable INST-function-def))

(in-theory (enable INST-su INST-pc))

(deftheory step-INST-low-level-functions
    '(step-inst-IFU step-inst-DQ step-inst-execute
      step-INST-IU step-INST-MU step-INST-BU step-INST-LSU
      step-INST-LSU-RS0 step-INST-LSU-RS1 step-INST-LSU-rbuf
      step-INST-LSU-lch step-INST-LSU-wbuf0 step-INST-LSU-wbuf0-lch
      step-INST-LSU-wbuf1 step-INST-LSU-wbuf1-lch
      step-inst-complete
      step-inst-commit dispatch-inst))

#|
;; Eval-set-print-MA evaluates expression expr, set variable s to the result,
;; and print out the result briefly.
;; 
;; Example (eval-set-print-MA s1 (MA-step (@ s) (MA-input 0 0 1 1)))
(defmacro eval-set-print-MA (s expr)
  `(pprogn (f-put-global ',s ,expr state)
           (mv nil
	     (list (MA-pc (f-get-global ',s state))
 	           (MA-RF (f-get-global ',s state))
	           (MA-SRF (f-get-global ',s state))
    	           (MA-DQ (f-get-global ',s state))
    	           (MA-ROB (f-get-global ',s state))
	           (MA-IU (f-get-global ',s state))
	           (MA-MU (f-get-global ',s state))
	           (MA-BU (f-get-global ',s state))
    	           (MA-LSU (f-get-global ',s state)))
	      state)))

(defmacro natp (n) `(and (integerp ,n) (<= 0 ,n)))

; (make-pair-seq from end) generates a list of pair of symbols
; beginning with s and MT.  For instance, (make-pair-seq 0 3)
; generates ((S0 MT0) (S1 MT1) (S2 MT2) (S3 MT3)).
(defun make-pair-seq (from end)
  (declare (xargs :mode :program))
  (if (or (not (natp from)) (not (natp end)) (zp (- end from)))
      nil
      (cons
       (list (pack-intern 's (coerce (append (coerce "S" 'list)
					     (explode-nonnegative-integer from
									  nil))
				     'string))
	     (pack-intern 's (coerce (append (coerce "MT" 'list)
					     (explode-nonnegative-integer from
									  nil))
				     'string)))
       (make-pair-seq (1+ from) end))))
	     
;; A help function.
(defun make-MA-step-seq (sigs seq)
  (if (endp seq) nil
      (if (endp (cdr seq)) nil
	  (let ((new-s (car (cadr seq)))
		(new-m (cadr (cadr seq)))
		(old-s (car (car seq)))
		(old-m (cadr (car seq))))
	    (cons `(f-put-global ',new-s (MA-step (@ ,old-s) ,sigs)
				 state)
		  (cons `(f-put-global ',new-m (MT-step (@ ,old-m)
							(@ ,old-s)
							,sigs)
				       state)
			(make-MA-step-seq sigs (cdr seq))))))))

; Apply MA-step repeatedly and bind the generated MA states to the variables
; given in list seq.  Sigs is supplied to MA-step at every transition.
; Example:
; (MT-step-seq (MA-input 0 0 1 1) ((S0 MT0) (S1 MT1) (S2 MT2) (S3 MT3)))
(defmacro MT-step-seq (sigs seq)
  (if (endp seq) nil
      (let ((last-s (car (car (last seq)))))
	`(pprogn 
	  ,@(make-MA-step-seq sigs seq)
	  (mv nil
	      (list (MA-pc (f-get-global ',last-s state))
		    (MA-RF (f-get-global ',last-s state))
		    (MA-SRF (f-get-global ',last-s state))
		    (MA-ROB (f-get-global ',last-s state)))
	      state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Printing functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun pr-ISA (s)
  (list (ISA-pc s) (ISA-RF s) (ISA-SRF s)))

(defun pr-INST (i)
  (list (INST-ID i) (ISA-pc (INST-pre-ISA i))
	(inst-specultv? i) (INST-word i) (INST-stg i)
	(inst-tag i)))
	 
(defun pr-INST-list (mlist)
  (if (endp mlist)
      nil
      (cons (pr-INST (car mlist)) (pr-INST-list (cdr mlist)))))

; Typical Usage:
; (pr-MT mt0)
(defmacro pr-MT (MT)
  `(list (pr-isa (MT-init-ISA (@ ,MT)))
	 (MT-new-ID (@ ,MT))
	 (MT-dq-len (@ ,MT))
	 (MT-wb-len (@ ,MT))
	 (MT-rob-head (@ ,MT))
	 (MT-rob-tail (@ ,MT))
	 (pr-INST-list (MT-trace (@ ,MT)))))

; Typical Usage:
; (pr-MA s0)
(defmacro pr-MA (s)
  `(list (MA-pc (@ ,s)) (MA-RF (@ ,s)) (MA-SRF (@ ,s))
    (MA-IFU (@ ,s)) (MA-DQ (@ ,s)) (MA-ROB (@ ,s)) (MA-IU (@ ,s))
    (MA-MU (@ ,s)) (MA-BU (@ ,s)) (MA-LSU (@ ,s))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Initial State Setting
(progn
(assign RF '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) 
(assign SRF (SRF 1 0 0))

(assign IFU (IFU 0 0 0 0))
(assign DE (dispatch-entry 0 0 0 0 0 0 0 0 0))
(assign reg-s (reg-ref 0 0))
(assign reg-tbl (make-list *num-regs* :initial-element (@ reg-s)))
(assign sreg-tbl (sreg-tbl (@ reg-s) (@ reg-s)))
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
(assign s0 (MA-state #x100 (@ RF) (@ SRF) (@ IFU) (@ DQ) (@ ROB)
		    (@ IU) (@ MU) (@ BU) (@ LSU) (@ mem)))

(assign MT0
	(MAETT (proj (@ s0))
	       0 0 0 0 0 0 nil))

(assign sigs (MA-input 0 0 1 1))
)

|#
