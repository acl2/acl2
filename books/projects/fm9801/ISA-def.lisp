;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; ISA-def.lisp:
; Author  Jun Sawada, University of Texas at Austin
;
;  This file includes the definitions of our ISA. 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The definition ISA behavior is given by (ISA-step ISA intr), which 
; returns the state of ISA after executing one instructions.
; (ISA-stepn ISA intr-lst n) returns the state of ISA after n instructions
; are executed. 
;
; This ISA implements following exceptions.
;  External Interrupt
;  Fetch Error
;  Illegal instruction
;  Data Access Error
;  
; When an exception happens, following actions are taken by the machine.
;   su <--- 0  (Set Supervisor mode)
;   sr0 <-- The restarting address after exception handling
;   sr1 <-- su
;   pc  <-- Exception Vectors 
;   RF <-- All writes to the registers take place before the exception
;            handling takes place.
;   mem <-- All writes to the memory by the preceding instructions must
;           complete.  If another error happens during the completion, 
;           the first instruction in program order is considered to
;           have caused the memory error.
;
; External Interrupt
;  The machine will complete all issued instructions, but does not
;  issue any new instructions.  SR0 will point to the next instruction
;  to be executed after the exception handling.  Exception vector is
;  0x30
; 
; Fetch Error
;  If the instruction fetch address is not readable, a fetch error
;  will be raised.  SR0 will point to the instruction address which
;  the processor failed to access.  Exception Vector is 0x10.  Note
;  that speculative fetch may cause a fake fetch error, but the
;  machine should not go into the exception handling cycle.
; 
; Data Access Error
;  If the processor fails to load or store data on the memory, an data
;  access error occurs and the exception is raised. Sr0 points to the
;  instruction that caused the data access error.  Exception vector is
;  0x20.
; 
; Illegal instruction
;  If the processor tries to execute an undefined instruction, or it
;  tries to execute a privileged instruction from the user mode, an
;  illegal instruction exception is raised and the processor goes into
;  the exception handling.  SR0 points to the next instruction after
;  the Illegal instruction.  The exception vector is 0x0
; 
; Memory protection issues on Supervisor and User mode.
;  Memory protection is effective only in the user mode.  In the
;  supervisor mode, the processor can access any address.  Memory
;  address translation does not exist in our model.
; 
; Added instructions 
;  In order to control the exception handling, we add a few more instructions.
; RFEH (Return From Exception Handling) privileged instruction
;     su <- SR1 & 0x1
;     pc <- Sr0
; MFSR rc (Move From Special Register) Privileged instruction
;     rc <- SR0  
; MTSR rc (Move To Special Register) Privileged instruction
;     SR0 <- rc
; SPM rc,ra+rb (Set page mode) (proposed, not implemented)
;     The access mode of the page containing ra+rb address is 
;     set to rc.  If rc does not contain 0, 1 or 2, the page mode is 
;     set to no-access.
; 
(in-package "ACL2")

(include-book "utils")
(include-book "basic-def")
(include-book "b-ops-aux")

;; Beginning of the definition of the Instruction-Set Architecture.
(deflabel begin-ISA-def)	     

(deflabel begin-ISA-state-def)

; An ISA state consists of a program counter, register file
; special register file and memory.
(defstructure ISA-state 
  (pc (:assert (addr-p pc) :rewrite (:rewrite (Integerp pc))))
  (RF (:assert (RF-p RF) :rewrite))
  (SRF (:assert (SRF-p SRF) :rewrite))
  (mem (:assert (mem-p mem) :rewrite))
  (:options :guards  (:conc-name ISA-))) 

; An ISA input contains a flag for external interrupt.
(defstructure ISA-input
  (exint (:assert (bitp exint) :rewrite))
  (:options :guards))

(deflist ISA-input-listp (l)
  (declare (xargs :guard t))
  ISA-input-p)

(deflabel end-ISA-state-def)

(defun read-error? (addr mem su)
  (declare (xargs :guard (and (addr-p addr) (mem-p mem) (bitp su))))
  (b-nor su (readable-addr? addr mem)))

(defthm bitp-read-error (bitp (read-error? addr mem su)))

(defun write-error? (addr mem su)
  (declare (xargs :guard (and (addr-p addr) (mem-p mem) (bitp su))))
  (b-nor su (writable-addr? addr mem)))

(defthm bitp-write-error (bitp (write-error? addr mem su)))

(deflabel begin-ISA-step-functions)

(defun supervisor-mode? (ISA)
  (declare (xargs :guard (ISA-state-p ISA)))
  (SRF-su (ISA-SRF ISA)))

(defthm bitp-supervisor-mode 
    (implies (ISA-state-p ISA) (bitp (supervisor-mode? ISA))))

;; Definitions of states after jumping to exception handling states.
(defun ISA-fetch-error (ISA)
  (declare (xargs :guard (ISA-state-p ISA)))
  (ISA-state #x10
	     (ISA-RF ISA)
	     (SRF 1 (word (ISA-pc ISA)) (word (SRF-su (ISA-SRF ISA))))
	     (ISA-mem ISA)))

(defun ISA-data-accs-error (ISA)
  (declare (xargs :guard (ISA-state-p ISA)))
  (ISA-state #x20
	     (ISA-RF ISA)
	     (SRF 1 (word (ISA-pc ISA)) (word (SRF-su (ISA-SRF ISA))))
	     (ISA-mem ISA)))

(defun ISA-illegal-inst (ISA)
  (declare (xargs :guard (ISA-state-p ISA)))
  (ISA-state #x0
	     (ISA-RF ISA)
	     (SRF 1 (word (1+ (ISA-pc ISA))) (word (SRF-su (ISA-SRF ISA))))
	     (ISA-mem ISA)))

(defun ISA-external-intr (ISA)
  (declare (xargs :guard (ISA-state-p ISA)))
  (ISA-state #x30
	     (ISA-RF ISA)
	     (SRF 1 (word (ISA-pc ISA)) (word (SRF-su (ISA-SRF ISA))))
	     (ISA-mem ISA)))

;; In the following definitions, rc ra and rb represent the field
;; value of the current instruction, and ISA represents the current
;; state of the machine.
(defun ISA-add (rc ra rb ISA)
  (declare (xargs :guard (and (rname-p rc) (rname-p ra) (rname-p rb)
			      (ISA-state-p ISA))))
  (let* ((pc (ISA-pc ISA))
	 (RF (ISA-RF ISA))
	 (val (word (+ (read-reg ra RF) (read-reg rb RF)))))
    (ISA-state (addr (1+ pc))
	       (write-reg val rc RF)
	       (ISA-SRF ISA)
	       (ISA-mem ISA))))

(defun ISA-mul (rc ra rb ISA)		  
  (declare (xargs :guard (and (rname-p rc) (rname-p ra) (rname-p rb)
			      (ISA-state-p ISA))))
  (let* ((pc (ISA-pc ISA))
	 (RF (ISA-RF ISA))
	 (val (word (* (read-reg ra RF) (read-reg rb RF)))))
    (ISA-state (addr (1+ pc))
	       (write-reg val rc RF)
	       (ISA-SRF ISA)
	       (ISA-mem ISA))))

(defun ISA-br (rc im ISA)
  (declare (xargs :guard (and (rname-p rc) (immediate-p im)
			      (ISA-state-p ISA))))
  (let ((RF (ISA-RF ISA))
	(pc (ISA-pc ISA)))
    (ISA-state (if (equal (read-reg rc RF) 0)
		   (addr (+ (logextu *addr-size* *immediate-size* im) pc))
		   (addr (1+ pc)))
	       (ISA-RF ISA)
	       (ISA-SRF ISA)
	       (ISA-mem ISA))))

(defun ISA-ld (rc ra rb ISA)
  (declare (xargs :guard (and (rname-p rc) (rname-p ra) (rname-p rb)
			      (ISA-state-p ISA))))
  (let* ((pc (ISA-pc ISA))
	 (RF (ISA-RF ISA))
	 (SRF (ISA-SRF ISA))
	 (mem (ISA-mem ISA))
	 (ad (addr (+ (read-reg ra RF) (read-reg rb RF))))
	 (val (read-mem ad mem)))
    (b-if (read-error? ad mem (SRF-su SRF))
	  (ISA-data-accs-error ISA)
	  (ISA-state (addr (1+ pc))
		     (write-reg val rc RF)
		     (ISA-SRF ISA)
		     (ISA-mem ISA)))))

(defun ISA-ldi (rc im ISA)
  (declare (xargs :guard (and (rname-p rc) (immediate-p im)
			      (ISA-state-p ISA))))
  (let* ((pc (ISA-pc ISA))
	 (RF (ISA-RF ISA))
	 (SRF (ISA-SRF ISA))
	 (mem (ISA-mem ISA))
	 (ad (addr im))
	 (val (read-mem ad mem)))
    (b-if (read-error? ad mem (SRF-su SRF))
	  (ISA-data-accs-error ISA)
	  (ISA-state (addr (1+ pc))
		     (write-reg val rc RF)
		     (ISA-SRF ISA)
		     (ISA-mem ISA)))))

(defun ISA-st (rc ra rb ISA)
  (declare (xargs :guard (and (rname-p rc) (rname-p ra) (rname-p rb)
			      (ISA-state-p ISA))))
  (let* ((pc (ISA-pc ISA))
	 (RF (ISA-RF ISA))
	 (SRF (ISA-SRF ISA))
	 (mem (ISA-mem ISA))
	 (ad (addr (+ (read-reg ra RF) (read-reg rb RF))))
	 (val (read-reg rc RF)))
    (b-if (write-error? ad mem (SRF-su SRF))
	  (ISA-data-accs-error ISA)
	  (ISA-state (addr (1+ pc))
		     (ISA-RF ISA)
		     (ISA-SRF ISA)
		     (write-mem val ad mem)))))

(defun ISA-sti (rc im ISA)
  (declare (xargs :guard (and (rname-p rc) (immediate-p im)
			      (ISA-state-p ISA))))
  (let* ((pc (ISA-pc ISA))
	 (RF (ISA-RF ISA))
	 (SRF (ISA-SRF ISA))
	 (mem (ISA-mem ISA))
	 (ad (addr im))
	 (val (read-reg rc RF)))
    (b-if (write-error? ad mem (SRF-su SRF))
	  (ISA-data-accs-error ISA)
	  (ISA-state (addr (1+ pc))
		     (ISA-RF ISA)
		     (ISA-SRF ISA)
		     (write-mem val ad mem)))))

(defun ISA-rfeh (ISA)
  (declare (xargs :guard (ISA-state-p ISA)))
  (b-if (supervisor-mode? ISA)
	(let* ((SRF (ISA-SRF ISA))
	       (sr0 (read-sreg 0 SRF))
	       (sr1 (read-sreg 1 SRF)))
	  (ISA-state (addr sr0)
		     (ISA-RF ISA)
		     (SRF (logcar sr1) sr0 sr1)
		     (ISA-mem ISA)))
	(ISA-illegal-inst ISA)))
		    
(defun ISA-mfsr (rc ra ISA)
  (declare (xargs :guard (and (rname-p rc) (rname-p ra) (ISA-state-p ISA))))
  (cond ((zbp (supervisor-mode? ISA))
	 (ISA-illegal-inst ISA))
	((or (equal ra 0) (equal ra 1))
	 (let* ((pc (ISA-pc ISA))
		(RF (ISA-RF ISA))
		(SRF (ISA-SRF ISA))
		(val (read-sreg ra SRF)))
	   (ISA-state (addr (1+ pc))
		      (write-reg val rc RF)
		      (ISA-SRF ISA)
		      (ISA-mem ISA))))
	(t (ISA-illegal-inst ISA))))

(defun ISA-mtsr (rc ra ISA)
  (declare (xargs :guard (and (rname-p rc) (rname-p ra) (ISA-state-p ISA))))
  (cond ((zbp (supervisor-mode? ISA))
	 (ISA-illegal-inst ISA))
	((or (equal ra 0) (equal ra 1))
	 (let* ((pc (ISA-pc ISA))
		(RF (ISA-RF ISA))
		(SRF (ISA-SRF ISA))
		(val (read-reg rc RF)))
	   (ISA-state (addr (1+ pc))
		      (ISA-RF ISA)
		      (write-sreg val ra SRF)
		      (ISA-mem ISA))))
	(t (ISA-illegal-inst ISA))))

(defun ISA-sync (ISA)
  (declare (xargs :guard (ISA-state-p ISA)))
  (ISA-state (addr (1+ (ISA-pc ISA)))
	     (ISA-RF ISA)
	     (ISA-SRF ISA)
	     (ISA-mem ISA)))

(deflabel end-ISA-step-functions)

; ISA-step takes the current state, ISA, and the interrupt signal, intr,
; and returns the next state. 
(defun ISA-step (ISA intr)
  "ISA represents the current state."
  (declare (xargs :guard (and (ISA-state-p ISA) (ISA-input-p intr))))
  (b-if (ISA-input-exint intr)
	(ISA-external-intr ISA)
  ; otherwise      
  (b-if (read-error? (ISA-pc ISA) (ISA-mem ISA) (SRF-su (ISA-SRF ISA)))
	(ISA-fetch-error ISA)
	(let ((inst (read-mem (ISA-pc ISA) (ISA-mem ISA))))
	  (let ((op (opcode inst))
		(rc (rc inst))
		(ra (ra inst))
		(rb (rb inst))
		(im (im inst)))
	    (cond ((equal op 0)		; add
		   (ISA-add rc ra rb ISA))
		  ((equal op 1)		; multiply
		   (ISA-mul rc ra rb ISA))
		  ((equal op 2)		; conditional branch
		   (ISA-br rc im ISA))
		  ((equal op 3)		; load
		   (ISA-ld rc ra rb ISA))
		  ((equal op 6)		; load from an immediate address
		   (ISA-ldi rc im ISA))
		  ((equal op 4)		; store
		   (ISA-st rc ra rb ISA))
		  ((equal op 7)		; store at an immediate address
		   (ISA-sti rc im ISA))
		  ((equal op 5)		; sync
		   (ISA-sync ISA))
		  ((equal op 8) ; RFEH
		   (ISA-rfeh ISA))
		  ((equal op 9) ; MFSR
		   (ISA-mfsr rc ra ISA))
		  ((equal op 10) ; MTSR
		   (ISA-mtsr rc ra ISA))
		  (t (ISA-illegal-inst ISA))))))))

; Runs the ISA machine n-steps.
; Argument intr-lst is the list of interrupt signals.
(defun ISA-stepn (ISA intr-lst n)
  (declare (xargs :guard (and (ISA-state-p ISA) (integerp n) (>= n 0)
			      (ISA-input-listp intr-lst)
			      (<= n (len intr-lst)))
		  :verify-guards nil))
  (if (zp n)
      ISA
      (ISA-stepn (ISA-step ISA (car intr-lst)) (cdr intr-lst) (1- n))))

(verify-guards ISA-stepn)

(defthm ISA-state-p-ISA-fetch-error
    (implies (ISA-state-p ISA)
	     (ISA-state-p (ISA-fetch-error ISA))))

(defthm ISA-state-p-ISA-data-accs-error
    (implies (ISA-state-p ISA)
	     (ISA-state-p (ISA-data-accs-error ISA))))

(defthm ISA-state-p-ISA-illegal-inst
    (implies (ISA-state-p ISA)
	     (ISA-state-p (ISA-illegal-inst ISA))))

(defthm ISA-state-p-ISA-external-intr 
    (implies (ISA-state-p ISA)
	     (ISA-state-p (ISA-external-intr ISA))))

(defthm ISA-state-p-ISA-add
    (implies (and (ISA-state-p ISA)
		  (rname-p rc))
	     (ISA-state-p (ISA-add rc ra rb ISA))))

(defthm ISA-state-p-ISA-mul
    (implies (and (ISA-state-p ISA)
		  (rname-p rc))
	     (ISA-state-p (ISA-mul rc ra rb ISA))))

(defthm ISA-state-p-ISA-br
    (implies (ISA-state-p ISA)
	     (ISA-state-p (ISA-br rc im ISA))))

(defthm ISA-state-p-ISA-ld
    (implies (and (ISA-state-p ISA)
		  (rname-p rc))
	     (ISA-state-p (ISA-ld rc ra rb ISA))))

(defthm ISA-state-p-ISA-ldi
    (implies (and (ISA-state-p ISA)
		  (rname-p rc))
	     (ISA-state-p (ISA-ldi rc im ISA))))

(defthm ISA-state-p-ISA-st
    (implies (and (ISA-state-p ISA)
		  (rname-p rc))
	     (ISA-state-p (ISA-st rc ra rb ISA))))

(defthm ISA-state-p-ISA-sti
    (implies (and (ISA-state-p ISA) (rname-p rc))
	     (ISA-state-p (ISA-sti rc im ISA))))

(defthm ISA-state-p-ISA-rfeh
    (implies (ISA-state-p ISA)
	     (ISA-state-p (ISA-rfeh ISA))))

(defthm ISA-state-p-ISA-mfsr
    (implies (and (ISA-state-p ISA)
		  (rname-p rc))
	     (ISA-state-p (ISA-mfsr rc ra ISA))))

(defthm ISA-state-p-ISA-mtsr
    (implies (and (ISA-state-p ISA)
		  (rname-p rc))
	     (ISA-state-p (ISA-mtsr rc ra ISA))))

(defthm ISA-state-p-ISA-sync
    (implies (ISA-state-p ISA)
	     (ISA-state-p (ISA-sync ISA))))

(defthm ISA-state-p-ISA-step
    (implies (ISA-state-p ISA)
	     (ISA-state-p (ISA-step ISA intr))))

(in-theory (disable ISA-step))

(defthm ISA-state-p-ISA-stepn
    (implies (ISA-state-p ISA)
	     (ISA-state-p (ISA-stepn ISA intr-lst n))))

(deflabel end-ISA-def)	     

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Definition of No-Self-Modifying Code 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deflabel begin-ISA-functions)

(defun store-inst-p (inst)
  (declare (xargs :guard (word-p inst)))
  (or (equal (opcode inst) 7) (equal (opcode inst) 4)))

(defun ISA-store-inst-p (ISA)
  (declare (xargs :guard (ISA-state-p ISA)))
  (store-inst-p (read-mem (ISA-pc ISA) (ISA-mem ISA))))
    
(defun ISA-store-addr (ISA)
  (declare (xargs :guard (ISA-state-p ISA)))
  (let ((inst (read-mem (ISA-pc ISA) (ISA-mem ISA)))
	(RF (ISA-RF ISA)))
    (cond ((equal (opcode inst) 7)
	   (addr (im inst)))
	  ((equal (opcode inst) 4)
	   (addr (+ (read-reg (ra inst) RF)
		    (read-reg (rb inst) RF))))
	  (t 0))))
  
(defun ISA-fetch-error-p (ISA)
  (declare (xargs :guard (ISA-state-p ISA)))
  (b1p (read-error? (ISA-pc ISA) (ISA-mem ISA) (SRF-su (ISA-SRF ISA)))))
  
(defun ISA-decode-error-p (ISA)
  (declare (xargs :guard (ISA-state-p ISA)))
  (let ((opcd (opcode (read-mem (ISA-pc ISA) (ISA-mem ISA))))
	(ra (ra (read-mem (ISA-pc ISA) (ISA-mem ISA))))
	(su (SRF-su (ISA-SRF ISA))))
    (not (or (equal opcd 0)
	     (equal opcd 1)
	     (equal opcd 2)
	     (equal opcd 3)
	     (equal opcd 4)
	     (equal opcd 5)
	     (equal opcd 6)
	     (equal opcd 7)
	     (and (equal opcd 8) (b1p su))
	     (and (equal opcd 9) (b1p su) (or (equal ra 0) (equal ra 1)))
	     (and (equal opcd 10) (b1p su) (or (equal ra 0) (equal ra 1)))))))

(defun ISA-load-access-error-p (ISA)
  (declare (xargs :guard (ISA-state-p ISA)))
  (let ((inst (read-mem (ISA-pc ISA) (ISA-mem ISA)))
	(su (SRF-su (ISA-SRF ISA)))
	(mem (ISA-mem ISA))
	(RF (ISA-RF ISA)))
    (if (equal (opcode inst) 6)
	(b1p (read-error? (addr (im inst)) mem su))
	(if (equal (opcode inst) 3)
	    (b1p (read-error? (addr (+ (read-reg (ra inst) RF)
				       (read-reg (rb inst) RF)))
			      mem su))
	    nil))))

(defun ISA-store-access-error-p (ISA)
  (declare (xargs :guard (ISA-state-p ISA)))
  (let ((inst (read-mem (ISA-pc ISA) (ISA-mem ISA)))
	(su (SRF-su (ISA-SRF ISA)))
	(mem (ISA-mem ISA))
	(RF (ISA-RF ISA)))
    (if (equal (opcode inst) 7)
	(b1p (write-error? (addr (im inst)) mem su))
	(if (equal (opcode inst) 4)
	    (b1p (write-error? (addr (+ (read-reg (ra inst) RF)
					(read-reg (rb inst) RF)))
			       mem su))
	    nil))))

(defun ISA-data-access-error-p (ISA)
  (declare (xargs :guard (ISA-state-p ISA)))
  (or (ISA-load-access-error-p ISA) (ISA-store-access-error-p ISA)))

(defun ISA-excpt-p (ISA)
  (declare (xargs :guard (ISA-state-p ISA)))
  (or (ISA-fetch-error-p ISA)
      (ISA-decode-error-p ISA)
      (ISA-data-access-error-p ISA)))

; If ISA state transition (ISA-step ISA intr) fetches an instruction 
; from addr, (ISA-fetches-from addr ISA intr) returns non-nil.
(defun ISA-fetches-from (addr ISA intr)
  (declare (xargs :guard (and (addr-p addr) (ISA-state-p ISA)
			      (ISA-input-p intr))))
  (and (equal addr (ISA-pc ISA))
       (not (b1p (ISA-input-exint intr)))))

;; If ISA state transition (ISA-stepn ISA intr n) fetches an instruction 
; from addr, (ISA-stepn-fetches-from addr ISA intr-lst n) returns non-nil.
(defun ISA-stepn-fetches-from (addr ISA intr-lst n)
  (declare (xargs :guard (and (addr-p addr) (ISA-state-p ISA)
			      (integerp n) (<= 0 n)
			      (ISA-input-listp intr-lst)
			      (<= n (len intr-lst)))
		  :measure (nfix n)))
  (if (zp n)
      nil
      (or (ISA-fetches-from addr ISA (car intr-lst))
	  (ISA-stepn-fetches-from addr (ISA-step ISA (car intr-lst))
				  (cdr intr-lst) (1- n)))))

(defun ISA-self-modify-p (ISA intr-lst n)
  (declare (xargs :guard (and (ISA-state-p ISA) (integerp n) (<= 0 n)
			      (ISA-input-listp intr-lst)
			      (<= n (len intr-lst)))
		  :measure (nfix n)))
  (if (zp n)
      nil
      (or (and (ISA-store-inst-p ISA)
	       (not (ISA-excpt-p ISA))
	       (not (b1p (ISA-input-exint (car intr-lst))))
	       (ISA-stepn-fetches-from (ISA-store-addr ISA)
				       (ISA-step ISA (car intr-lst))
				       (cdr intr-lst)
				       (1- n)))
	  (ISA-self-modify-p (ISA-step ISA (car intr-lst))
			     (cdr intr-lst)
			     (1- n)))))

(defun ISA-writes-at (addr ISA intr)
  (declare (xargs :guard (and (addr-p addr) (ISA-state-p ISA)
			      (ISA-input-p intr))))
  (and (ISA-store-inst-p ISA)
       (not (ISA-excpt-p ISA))
       (not (b1p (ISA-input-exint intr)))
       (equal (ISA-store-addr ISA) addr)))

(defun ISA-stepn-writes-at (addr ISA intr-lst n)
  (declare (xargs :guard (and (addr-p addr) (ISA-state-p ISA)
			      (integerp n) (<= 0 n)
			      (ISA-input-listp intr-lst)
			      (<= n (len intr-lst)))
		  :measure (nfix n)))
  (if (zp n)
      nil
      (or (ISA-writes-at addr ISA (car intr-lst))
	  (ISA-stepn-writes-at addr (ISA-step ISA (car intr-lst))
			       (cdr intr-lst) (1- n)))))

(deflabel end-ISA-functions)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; ISA theories
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deftheory ISA-def
    (set-difference-theories (function-theory 'end-ISA-def)
			     (function-theory 'begin-ISA-def)))

(deftheory ISA-state-def
    (set-difference-theories (function-theory 'end-ISA-state-def)
			     (function-theory 'begin-ISA-state-def)))
    
(deftheory ISA-step-functions
  (definition-theory
     (set-difference-theories (universal-theory 'end-ISA-step-functions)
			      (universal-theory 'begin-ISA-step-functions))))
(in-theory (disable ISA-step-functions))

(deftheory ISA-functions
    (set-difference-theories (function-theory 'end-ISA-functions)
			     (function-theory 'begin-ISA-functions)))

(deftheory ISA-non-rec-functions
    (non-rec-functions (theory 'ISA-functions) world))

(in-theory (disable ISA-def))
(in-theory (disable ISA-non-rec-functions))

#|
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  Proof of an Equivalent Definition of ISA-self-modify-p
;  This is irrelevant to the main proof.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; We prove that
; (ISA-fetches-from addr ISA intr-lst n)
; <=> (exists i j addr (and (< i j) (< j n)
;                          (ISA-writes-at addr ISA-i intr-i)
;                          (ISA-fetches-from addr ISA-j intr-j))
; We prove this lemma by showing two lemmas ISA-fetches-from* and 
; ISA-fetches-from**. ISA-fetches-from* shows the right arrow, and 
; ISA-fetches-from** shows the left arrow.
;
; We show the existence of i, j, and addr with the witness functions i, j,
; and write-addr. 
(defun j-i-1 (addr ISA intr-lst n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
      (if (ISA-fetches-from addr ISA (car intr-lst))
	  0
	  (1+ (j-i-1 addr (ISA-step ISA (car intr-lst))
		     (cdr intr-lst) (1- n))))))

(defun i (ISA intr-lst n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
      (if (and (ISA-store-inst-p ISA)
	       (not (ISA-excpt-p ISA))
	       (not (b1p (ISA-input-exint (car intr-lst))))
	       (ISA-stepn-fetches-from (ISA-store-addr ISA)
				       (ISA-step ISA (car intr-lst))
				       (cdr intr-lst)
				       (1- n)))
	  0
	  (1+ (i (ISA-step ISA (car intr-lst)) (cdr intr-lst) (1- n))))))

(defun j (ISA intr-lst n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
      (if (and (ISA-store-inst-p ISA)
	       (not (ISA-excpt-p ISA))
	       (not (b1p (ISA-input-exint (car intr-lst))))
	       (ISA-stepn-fetches-from (ISA-store-addr ISA)
				       (ISA-step ISA (car intr-lst))
				       (cdr intr-lst)
				       (1- n)))
	  (1+ (j-i-1 (ISA-store-addr ISA)
		     (ISA-step ISA (car intr-lst)) (cdr intr-lst) (1- n)))
	  (1+ (j (ISA-step ISA (car intr-lst)) (cdr intr-lst) (1- n))))))

(defun write-addr (ISA intr n)
  (ISA-store-addr (ISA-stepn ISA intr (i ISA intr n))))

(defthm fetch-from-at-the-cycle
    (let ((ISA-i (ISA-stepn ISA-0 intr-lst (j-i-1 addr ISA-0 intr-lst n)))
	  (intr-i (nth (j-i-1 addr ISA-0 intr-lst n) intr-lst)))
      (implies (ISA-stepn-fetches-from addr ISA-0 intr-lst n)
	       (ISA-fetches-from addr ISA-i intr-i)))
  :hints (("goal" :in-theory (enable ISA-stepn))))

(defthm i-is-right
    (let ((i (i ISA-0 intr-lst n))
	  (addr (write-addr ISA-0 intr-lst n)))
      (let ((ISA-i (ISA-stepn ISA-0 intr-lst i))
	    (intr-i (nth i intr-lst)))
	(implies (ISA-self-modify-p ISA-0 intr-lst n)
		 (ISA-writes-at addr ISA-i intr-i))))
  :hints (("goal" :in-theory (enable ISA-stepn ISA-WRITES-AT))))

(defthm j-is-right
    (let ((j (j ISA-0 intr-lst n))
	  (addr (write-addr ISA-0 intr-lst n)))
      (let ((ISA-j (ISA-stepn ISA-0 intr-lst j))
	    (intr-j (nth j intr-lst)))
	(implies (ISA-self-modify-p ISA-0 intr-lst n)
		 (ISA-fetches-from addr ISA-j intr-j))))
  :hints (("goal" :in-theory (enable ISA-stepn ISA-WRITES-AT))))

(in-theory (disable write-addr))

(defthm i-<-j
    (implies (ISA-self-modify-p ISA-0 intr-lst n)
	     (< (i ISA-0 intr-lst n) (j ISA-0 intr-lst n))))

(defthm j-i-1-<-n
    (implies (ISA-stepn-fetches-from addr ISA intr-lst n)
	     (< (j-i-1 addr ISA intr-lst n) n))
  :rule-classes :linear)

(defthm j-<-n
    (implies (ISA-self-modify-p ISA-0 intr-lst n)
	     (< (j ISA-0 intr-lst n) n)))

; This lemma tells that 
; (ISA-fetches-from addr ISA intr-lst n)
; => exists i j addr (and (< i j) (< j n)
;                          (ISA-writes-at addr ISA-i intr-i)
;                          (ISA-fetches-from addr ISA-j intr-j)
(defthm ISA-self-modify-p*
    (let ((i (i ISA-0 intr-lst n))
	  (j (j ISA-0 intr-lst n))
	  (addr (write-addr ISA-0 intr-lst n)))
      (let ((ISA-i (ISA-stepn ISA-0 intr-lst i))
	    (intr-i (nth i intr-lst))
	    (ISA-j (ISA-stepn ISA-0 intr-lst j))
	    (intr-j (nth j intr-lst)))
	(implies (ISA-self-modify-p ISA-0 intr-lst n)
		 (and (ISA-writes-at addr ISA-i intr-i)
		      (ISA-fetches-from addr ISA-j intr-j)
		      (< i j) (< j n)))))
  :hints (("goal" :do-not-induct t)))

(defthm ISA-fetches-from-implies-ISA-stepn-fetches-from
    (implies (and (integerp j) (integerp n) (<= 0 j) (< j n)
		  (ISA-fetches-from addr (ISA-stepn ISA intr-lst j)
				    (nth j intr-lst)))
	     (ISA-stepn-fetches-from addr ISA intr-lst n))
  :hints (("goal" :in-theory (enable ISA-stepn))))

; This lemma tells that 
; (ISA-fetches-from addr ISA intr-lst n)
; <= exists i j addr (and (< i j) (< j n)
;                          (ISA-writes-at addr ISA-i intr-i)
;                          (ISA-fetches-from addr ISA-j intr-j)
(defthm ISA-self-modify-p**
    (let ((ISA-i (ISA-stepn ISA-0 intr-lst i))
	  (intr-i (nth i intr-lst))
	  (ISA-j (ISA-stepn ISA-0 intr-lst j))
	  (intr-j (nth j intr-lst)))
      (implies (and (integerp i) (integerp j) (integerp n) (<= 0 i)
		    (< i j) (< j n)
		    (ISA-writes-at addr ISA-i intr-i)
		    (ISA-fetches-from addr ISA-j intr-j))
	       (ISA-self-modify-p ISA-0 intr-lst n)))
  :hints (("goal" :in-theory (enable ISA-WRITES-AT
				     ISA-stepn
				     ISA-STEPN-SELF-MODIFIES-P)
		  :restrict
		  ((ISA-fetches-from-implies-ISA-stepn-fetches-from
		    ((j (+ -1 j))))))))
|#

#|
Here is a simple example program for our ISA.

Our program calculates the factorial of the number at address #x800 and stores
it at address #x801.

Initial memory setting:

#x0: STI R0,(#x50)
#x1: LDI R0,(#x3)
#x2: BR R0, 0
#x3: 0

#x10: STI R0,(#x50)
#x11: LDI R0,(#x13)
#x12: BR R0, 0
#x13: 0

#x20: STI R0,(#x50)
#x21: LDI R0,(#x23)
#x22: BR R0, 0
#x23: 0

#x30: STI R0,(#x50)
#x31: LDI R0,(#x33)
#x32: BR R0, 0
#x33: 0

#x60: 0
#x61: 1
#x62: 2
#x63: -1

#x70: #x400
#x71: #x800

#x100: LDI R15,(#x70) ; program base
#x101: LDI R14,(#x71) ; data base
#x102: LDI R0, (#x60) ; 0      
#x103: LDI R1, (#x61) ; 1
#x104: LDI R2, (#x62) ; 2
#x105: LDI R3, (#x63) ; -1
#x106: MTSR SR0,R15
#x107: MTSR SR1,R0
#x108: RFEH

Initial memory image:
#x400     LD R5,(R14+R0) ; R5 holds counter
#x401     ADD R6, R0, R1     ; R6 holds factorial. Initially 1.
Loop:
#x402:    MUL R6, R6, R5  ; counter * fact -> fact
#x403:    ADD R5, R5, R3  ; decrement fact
#x404:    BR  R5, Exit; if counter is zero, exit
#x405:    BR  R0, Loop ; always jump to loop
EXIT:
#x406: ST  R6, (R14+R1)
#x407: SYNC
#x408: Trap

#x800: 5
#x801: 0
#x802: 5 ; Offset to Loop
#x803: 9 ; Offset to Exit

(assign mem-alist '(
; Exception Handler
(#x0 . #x7050) ; STI R0,(#x50)
(#x1 . #x6003) ; LDI R0,(#x3)
(#x2 . #x2000) ; BR R0, 0
(#x3 . 0)
; Exception Handler
(#x10 . #x7050) ; STI R0,(#x50)
(#x11 . #x6013) ; LDI R0,(#x13)
(#x12 . #x2000) ; BR R0, 0
(#x13 . 0)
; Exception Handler
(#x20 . #x7050) ; STI R0,(#x50)
(#x21 . #x6023) ; LDI R0,(#x23)
(#x22 . #x2000) ; BR R0, 0
(#x23 . 0)

; Exception Handler
(#x30 . #x7050) ; STI R0,(#x50)
(#x31 . #x6033) ; LDI R0,(#x33)
(#x32 . #x2000) ; BR R0, 0
(#x33 . 0)

; Kernel Data Section
(#x60 .  0)
(#x61 . 1)
(#x62 . 2)
(#x63 . #xFFFF) ; -1
(#x70 . #x400)
(#x71 . #x800)
; Kernel Dispatching code
(#x100 . #x6F70) ; LDI R15,(#x70) ; program base
(#x101 . #x6E71) ;  LDI R14,(#x71) ; data base
(#x102 . #x6060) ;  LDI R0, (#x60) ; 0      
(#x103 . #x6161) ;  LDI R1, (#x61) ; 1
(#x104 . #x6262) ; LDI R2, (#x62) ; 2
(#x105 . #x6363) ; LDI R3, (#x63) ; -1
(#x106 . #xAF00) ;  MTSR SR0,R15
(#x107 . #xA010) ;  MTSR SR1,R0
(#x108 . #x8000) ; #x103: RFEH
; Program
(#x400 . #x35E0) ;  LD R5,(R14+R0) ; R5 holds counter
(#x401 . #x0601) ;  ADD R6, R0, R1     ; R6 holds factorial. Initially 1.
; Loop:
(#x402 . #x1665) ;  Mul R6, R6, R5  ; counter * fact -> fact
(#x403 . #x0553) ;  ADD R5, R5, R3  ; decrement fact
(#x404 . #x2502) ;  BR  R5, Exit; if counter is zero, exit
(#x405 . #x20FD) ;  BR  R0, Loop ; always jump to loop
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
|#

; How to run the program:
; 1. Certify and compile all the proof scripts.
;    (You may skip this, but the execution will be slow.)
; 2. Run ACL2.
; 3. Type command '(ld "ISA-def.lisp")'.
; 4. Run following assign commands, which defines initial state s.
;  (assign RF '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) 
;  (assign mem  See Above) 
;  (assign SRF (SRF 1 0 0))
;  (assign s (ISA-state #x100 (@ RF) (@ SRF) (@ mem)))
; 
; 5. You can run the ISA machine for one cycle by
;    (ISA-step (@ s) (ISA-input 1)).
;    You can also run the machine for multiple cycles with ISA-stepn.
;    For instance, if you want to run the machine 15 cycles, type:
;      (assign input-list (make-list 15 :initial-element (ISA-input 0)))
;      (ISA-stepn (@ s) 15).  
; 
; 6. Following macro may be useful to evaluate and assign an ISA state
; to a variable, and print out only pc and register file, but not memory.
; 
; (defmacro eval-set-print-ISA-RF (s expr)
;   `(pprogn (f-put-global ',s ,expr state)
;            (mv nil
; 	     (list (ISA-pc (f-get-global ',s state))
;  	           (ISA-RF (f-get-global ',s state))
; 	           (ISA-SRF (f-get-global ',s state)))
; 	      state)))
