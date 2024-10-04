;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; MI-inv.lisp
; Author  Jun Sawada, University of Texas at Austin
;
;  This book proves theorems about register modifiers and memory
;  modifiers.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "ACL2")

(include-book "MA2-lemmas")
(include-book "MAETT-lemmas")
(include-book "memory-inv")

(deflabel begin-modifier)
; This book proves basic lemmas about register modifiers and memory
; modifiers. 
;  Index
;    Lemmas about register modifiers
;      Basic Lemmas
;      Relation between register modifiers and register reference table
;      Behavior of register modifier in the ISA model 
;      Other more complex lemmas.
;    Lemmas about memory modifiers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Lemmas about register modifiers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Start of basic lemmas about register modifiers.

; A register modifier in the current state is a register modifier in
; the next state.
(defthm reg-modifier-step-inst
    (equal (reg-modifier-p idx (step-inst i MT MA sigs))
	   (reg-modifier-p idx i))
  :hints (("Goal" :in-theory (enable reg-modifier-p))))

; A special register modifier in the current state is a register
; modifier in the next state.
(defthm sreg-modifier-step-inst
    (equal (sreg-modifier-p idx (step-inst i MT MA sigs))
	   (sreg-modifier-p idx i))
  :hints (("Goal" :in-theory (enable sreg-modifier-p))))

; Some trivial lemmas. 

; relation between the register modifiers and uncommitted register modifiers.
(defthm trace-exist-uncommitted-LRM-if-exist-reg-modifier
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (trace-exist-LRM-before-p i r trace)
		  (not (committed-p (trace-LRM-before i r trace))))
	     (trace-exist-uncommitted-LRM-before-p i r trace)))

; If there are register modifiers, and the last register modifier is
; not committed, then there exists uncommitted register modifiers.
(defthm exist-uncommitted-LRM-if-exist-reg-modifier
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (exist-LRM-before-p i r MT)
		  (not (committed-p (LRM-before i r MT))))
	     (exist-uncommitted-LRM-before-p i r MT))
  :hints (("goal" :in-theory (enable exist-uncommitted-LRM-before-p
				     exist-LRM-before-p
				     LRM-before))))

(defthm trace-exist-uncommitted-LSRM-if-exist-sreg-modifier
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (trace-exist-LSRM-before-p i r trace)
		  (not (committed-p (trace-LSRM-before i r trace))))
	     (trace-exist-uncommitted-LSRM-before-p i r trace)))

; If there are special register modifiers, and the last special
; register modifier is not committed, then there exists uncommitted
; special register modifiers. 
(defthm exist-uncommitted-LSRM-if-exist-reg-modifier
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (exist-LSRM-before-p i r MT)
		  (not (committed-p (LSRM-before i r MT))))
	     (exist-uncommitted-LSRM-before-p i r MT))
  :hints (("goal" :in-theory (enable exist-uncommitted-LSRM-before-p
				     exist-LSRM-before-p
				     LSRM-before))))

(in-theory (disable trace-exist-uncommitted-LRM-if-exist-reg-modifier
		    trace-exist-uncommitted-LSRM-if-exist-sreg-modifier))

(defthm exist-uncommitted-LRM-if-commit-car
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (not (committed-p (car trace)))
		  (trace-exist-LRM-before-p i r (cdr trace)))
	     (trace-exist-uncommitted-LRM-before-p i r (cdr trace)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
   (implies (and (inv MT MA)
		 (MAETT-p MT) (MA-state-p MA)
		 (subtrace-p trace MT)
		 (INST-listp trace)
		 (not (committed-p (car trace)))
		 (not (trace-exist-uncommitted-LRM-before-p i r
							      (cdr trace))))
	    (not (trace-exist-LRM-before-p i r (cdr trace)))))))

(defthm exist-uncommitted-LSRM-if-commit-car
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (not (committed-p (car trace)))
		  (trace-exist-LSRM-before-p i r (cdr trace)))
	     (trace-exist-uncommitted-LSRM-before-p i r (cdr trace)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (not (committed-p (car trace)))
		  (not (trace-exist-uncommitted-LSRM-before-p i r
								(cdr trace))))
	     (not (trace-exist-LSRM-before-p i r (cdr trace)))))))

(encapsulate nil
(local
(defthm inst-in-LRM-before-help
    (implies (trace-exist-LRM-before-p i rname trace)
	     (member-equal (trace-LRM-before i rname trace)
			   trace))))

(defthm inst-in-LRM-before
    (implies (exist-LRM-before-p i rname MT)
	     (INST-in (LRM-before i rname MT) MT))
  :hints (("goal" :in-theory (enable INST-in LRM-before
				     exist-LRM-before-p))))
)

(encapsulate  nil
(local
(defthm inst-in-LSRM-before-help
    (implies (trace-exist-LSRM-before-p i rname trace)
	     (member-equal (trace-LSRM-before i rname trace)
			   trace))))

(defthm inst-in-LSRM-before
    (implies (exist-LSRM-before-p i rname MT)
	     (INST-in (LSRM-before i rname MT) MT))
  :hints (("goal" :in-theory (enable INST-in LSRM-before
				     exist-LSRM-before-p))))
)

; Register modifiers are INSTs in MT. 
(encapsulate nil
(local
(defthm inst-in-LRM-in-ROB-help
    (implies (trace-exist-LRM-in-ROB-p rname trace)
	     (member-equal (trace-LRM-in-ROB rname trace)
			   trace))))

(defthm inst-in-LRM-in-ROB
    (implies (exist-LRM-in-ROB-p rname MT)
	     (INST-in (LRM-in-ROB rname MT) MT))
  :hints (("goal" :in-theory (enable INST-in exist-LRM-in-ROB-p 
				     LRM-in-ROB))))

)

(encapsulate nil
(local
(defthm inst-in-LSRM-in-ROB-help
    (implies (trace-exist-LSRM-in-ROB-p rname trace)
	     (member-equal (trace-LSRM-in-ROB rname trace)
			   trace))))

(defthm inst-in-LSRM-in-ROB
    (implies (exist-LSRM-in-ROB-p rname MT)
	     (INST-in (LSRM-in-ROB rname MT) MT))
  :hints (("goal" :in-theory (enable INST-in exist-LSRM-in-ROB-p 
				     LSRM-in-ROB))))
)

(encapsulate nil
(local
 (defthm LRM-before-differs-from-i-help
    (implies (trace-exist-LRM-before-p i rname MT)
	     (not (equal (trace-LRM-before i rname MT) i)))))

; The last register modifier before i is not i.
(defthm LRM-before-differs-from-i
    (implies (exist-LRM-before-p i rname MT)
	     (not (equal (LRM-before i rname MT) i)))
  :hints (("goal" :in-theory (enable exist-LRM-before-p
				     LRM-before))))
)

(encapsulate nil
(local
 (defthm LSRM-before-differs-from-i-help
    (implies (trace-exist-LSRM-before-p i rname MT)
	     (not (equal (trace-LSRM-before i rname MT) i)))))

; The last special register modifier before i is not i.
(defthm LSRM-before-differs-from-i
    (implies (exist-LSRM-before-p i rname MT)
	     (not (equal (LSRM-before i rname MT) i)))
  :hints (("goal" :in-theory (enable exist-LSRM-before-p
				     LSRM-before))))
)

(encapsulate nil
(local
 (defthm INST-in-order-LRM-before-help
    (implies (and (member-equal i trace)
		  (trace-exist-LRM-before-p I rname trace))
	     (member-in-order (trace-LRM-before i rname trace)
			      i trace))
   :hints (("goal" :in-theory (enable member-in-order*)))))

; The last register modifier before i precedes i in program order.
(defthm INST-in-order-LRM-before
    (implies (and (INST-in i MT) (exist-LRM-before-p I rname MT))
	     (INST-in-order-p (LRM-before i rname MT) i MT))
  :hints (("goal" :in-theory (enable LRM-before INST-in
				     INST-in-order-p exist-LRM-before-p))))
)

(encapsulate nil
(local
 (defthm INST-in-order-LSRM-before-help
    (implies (and (member-equal i trace)
		  (trace-exist-LSRM-before-p I rname trace))
	     (member-in-order (trace-LSRM-before i rname trace)
			      i trace))
   :hints (("goal" :in-theory (enable member-in-order*)))))

; The last special register modifier before i precedes i in program order.
(defthm INST-in-order-LSRM-before
    (implies (and (INST-in i MT) (exist-LSRM-before-p I rname MT))
	     (INST-in-order-p (LSRM-before i rname MT) i MT))
  :hints (("goal" :in-theory (enable exist-LSRM-before-p INST-in
				     INST-in-order-p LSRM-before))))
)

(encapsulate nil
(local
(defthm reg-modifier-p-LRM-before-help
    (implies (trace-exist-LRM-before-p I rname trace)
	     (reg-modifier-p rname
			     (trace-LRM-before I rname trace)))))

; The last register modifier is a register modifier.
(defthm reg-modifier-p-LRM-before
    (implies (exist-LRM-before-p I rname MT)
	     (reg-modifier-p rname (LRM-before I rname MT)))
  :hints (("goal" :in-theory (enable exist-LRM-before-p
				     LRM-before))))
)

(encapsulate nil
(local
(defthm sreg-modifier-p-LSRM-before-help
    (implies (trace-exist-LSRM-before-p I rname trace)
	     (sreg-modifier-p rname
			      (trace-LSRM-before I rname trace)))))

; The last special register modifier is a special register modifier.
(defthm sreg-modifier-p-LSRM-before
    (implies (exist-LSRM-before-p I rname MT)
	     (sreg-modifier-p rname (LSRM-before I rname MT)))
  :hints (("goal" :in-theory (enable exist-LSRM-before-p
				     LSRM-before))))
)

(encapsulate nil
(local
(defthm reg-modifier-p-LRM-in-ROB-help
    (implies (trace-exist-LRM-in-ROB-p idx trace)
	     (reg-modifier-p idx (trace-LRM-in-ROB idx trace)))))

; The last register modifier in the ROB is a register modifier.
(defthm reg-modifier-p-LRM-in-ROB
    (implies (exist-LRM-in-ROB-p idx MT)
	     (reg-modifier-p idx (LRM-in-ROB idx MT)))
  :hints (("Goal" :in-theory (enable exist-LRM-in-ROB-p
				     LRM-in-ROB))))
)

(encapsulate nil
(local
(defthm sreg-modifier-p-LSRM-in-ROB-help
    (implies (trace-exist-LSRM-in-ROB-p idx trace)
	     (sreg-modifier-p idx
			      (trace-LSRM-in-ROB idx trace)))))

; The last special register modifier in the ROB is a special register
; modifier. 
(defthm sreg-modifier-p-LSRM-in-ROB
    (implies (exist-LSRM-in-ROB-p idx MT)
	     (sreg-modifier-p idx (LSRM-in-ROB idx MT)))
  :hints (("Goal" :in-theory (enable exist-LSRM-in-ROB-p
				     LSRM-in-ROB))))
)

; A register modifier is a write-back instruction.
(defthm INST-writeback-p-reg-modifier
    (implies (reg-modifier-p rname i)
	     (INST-writeback-p i))
  :hints (("goal" :in-theory (enable reg-modifier-p 
				     INST-function-def
				     decode logbit* rdb lift-b-ops))))

; A special register modifier is a write-back instruction.
(defthm INST-writeback-p-sreg-modifier
    (implies (sreg-modifier-p rname i)
	     (INST-writeback-p i))
  :hints (("goal" :in-theory (enable sreg-modifier-p 
				     INST-function-def lift-b-ops
				     decode logbit* rdb))))
(in-theory (disable INST-writeback-p-reg-modifier
		    INST-writeback-p-sreg-modifier))

; The last register modifier is a write-back instruction.
(defthm INST-writeback-p-LRM-before
    (implies (and (MAETT-p MT) (INST-p i)
		  (exist-LRM-before-p I rname MT))
	     (INST-writeback-p (LRM-before I rname MT)))
  :hints (("goal" :in-theory (disable INST-writeback-p-reg-modifier)
		  :use (:instance INST-writeback-p-reg-modifier
				  (i (LRM-BEFORE I RNAME MT))))))

; The last special register modifier is a write-back instruction.
(defthm INST-writeback-p-LSRM-before
    (implies (exist-LSRM-before-p I rname MT)
	     (INST-writeback-p (LSRM-before I rname MT)))
  :hints (("goal" :in-theory (disable INST-writeback-p-sreg-modifier)
		  :use (:instance INST-writeback-p-sreg-modifier
				  (i (LSRM-BEFORE I RNAME MT))))))

; The destination register of the last register modifier of
; register idx is idx itself. 
(defthm INST-dest-reg-LRM-in-ROB
    (implies (exist-LRM-in-ROB-p idx MT)
	     (equal (INST-dest-reg (LRM-in-ROB idx MT)) idx))
  :hints (("Goal" :use (:instance REG-MODIFIER-P-LRM-IN-ROB)
		  :in-theory (e/d (reg-modifier-p)
				  (REG-MODIFIER-P-LRM-IN-ROB)))))

; Similar to INST-dest-reg-LRM-in-ROB.
(defthm INST-dest-sreg-LRM-in-ROB
    (implies (exist-LSRM-in-ROB-p idx MT)
	     (equal (INST-dest-reg (LSRM-in-ROB idx MT)) idx))
  :hints (("Goal" :use (:instance SREG-MODIFIER-P-LSRM-IN-ROB)
		  :in-theory (e/d (sreg-modifier-p)
				  (SREG-MODIFIER-P-LSRM-IN-ROB)))))

;; End of basic lemmas about register modifiers.

;; Start of the lemmas about the relation between the register modifiers
;; and the register reference table. 
(encapsulate nil
(local
(defthm consistent-reg-ref-if-consistent-reg-tbl-under
    (implies (and (consistent-reg-tbl-under ub MT MA)
		  (integerp ub) (integerp rix)
		  (<= 0 rix) (< rix ub))
	     (consistent-reg-ref-p rix MT MA))))

(local
  (defthm not-reg-modifier-in-rob-if-not-reg-ref-wait-help
      (implies (and (consistent-reg-ref-p rname MT MA)
		    (not (b1p (MT-specultv-at-dispatch? MT)))
		    (not (b1p (MT-modified-at-dispatch? MT))))
	       (iff (exist-LRM-in-ROB-p rname MT)
		    (b1p (reg-ref-wait?
			  (reg-tbl-nth rname (DQ-reg-tbl (MA-DQ MA)))))))
    :hints (("goal" :in-theory (enable consistent-reg-ref-p)))))

; Wait? field of the corresponding entry in the register
; reference table is 1 iff register modifiers of register rname
; are currently stored in the ROB.
(defthm not-reg-modifier-in-rob-if-not-reg-ref-wait
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (rname-p rname)
		  (not (b1p (MT-specultv-at-dispatch? MT)))
		  (not (b1p (MT-modified-at-dispatch? MT))))
	     (iff (exist-LRM-in-ROB-p rname MT)
		  (b1p (reg-ref-wait?
			(reg-tbl-nth rname (DQ-reg-tbl (MA-DQ MA)))))))
  :hints (("goal" :in-theory (enable inv consistent-reg-tbl-p)
		  :restrict ((not-reg-modifier-in-rob-if-not-reg-ref-wait-help
			      ((MA MA)))))))
(local
(defthm reg-ref-tag-points-to-LRM-in-ROB-help
    (implies (and (consistent-reg-ref-p rname MT MA)
		  (not (b1p (MT-specultv-at-dispatch? MT)))
		  (not (b1p (MT-modified-at-dispatch? MT)))
		  (b1p (reg-ref-wait? (reg-tbl-nth rname
						   (DQ-reg-tbl (MA-DQ MA))))))
	     (equal (reg-ref-tag (reg-tbl-nth rname (DQ-reg-tbl (MA-DQ MA))))
		    (INST-tag (LRM-in-ROB rname MT))))
  :hints (("goal" :in-theory (enable consistent-reg-ref-p lift-b-ops)))))

; If wait? field is 1 in the register reference table,
; field tag of a register reference table entry designates the
; ROB entry where the last register modifier is stored. 
(defthm reg-ref-tag-points-to-LRM-in-ROB
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (rname-p rname)
		  (not (b1p (MT-specultv-at-dispatch? MT)))
		  (not (b1p (MT-modified-at-dispatch? MT)))
		  (b1p (reg-ref-wait? (reg-tbl-nth rname
						   (DQ-reg-tbl (MA-DQ MA))))))
	     (equal (reg-ref-tag (reg-tbl-nth rname (DQ-reg-tbl (MA-DQ MA))))
		    (INST-tag (LRM-in-ROB rname MT))))
  :hints (("goal" :in-theory (enable inv consistent-reg-tbl-p)
		  :restrict ((reg-ref-tag-points-to-LRM-in-ROB-help
			      ((MT MT)))))))
)

(encapsulate nil
(local
  (defthm not-sreg-modifier-in-rob-if-not-sreg-ref-wait-help
      (implies (and (consistent-sreg-ref-p rname MT MA)
		    (not (b1p (MT-specultv-at-dispatch? MT)))
		    (not (b1p (MT-modified-at-dispatch? MT))))
	       (iff (exist-LSRM-in-ROB-p rname MT)
		    (b1p (reg-ref-wait?
			  (sreg-tbl-nth rname (DQ-sreg-tbl (MA-DQ MA)))))))
    :hints (("goal" :in-theory (enable consistent-sreg-ref-p)))))
  
; Register modifiers of special register rname are in the ROB if
; the wait field of the corresponding entry in the register reference
; table is 1.
(defthm not-sreg-modifier-in-rob-if-not-sreg-ref-wait
    (implies (and (inv MT MA)
		  (srname-p rname)
		  (not (b1p (MT-specultv-at-dispatch? MT)))
		  (not (b1p (MT-modified-at-dispatch? MT))))
	     (iff (exist-LSRM-in-ROB-p rname MT)
		  (b1p (reg-ref-wait?
			(sreg-tbl-nth rname (DQ-sreg-tbl (MA-DQ MA)))))))
  :hints (("goal" :in-theory (enable inv consistent-sreg-tbl-p
				     srname-p)
		  :cases ((equal rname 0) (equal rname 1)))))
)

(encapsulate nil
(local
(defthm sreg-ref-tag-points-to-LSRM-in-ROB-help
    (implies (and (consistent-sreg-ref-p rname MT MA)
		  (not (b1p (MT-specultv-at-dispatch? MT)))
		  (not (b1p (MT-modified-at-dispatch? MT)))
		  (b1p (reg-ref-wait?
			(sreg-tbl-nth rname (DQ-sreg-tbl (MA-DQ MA))))))
     (equal (reg-ref-tag (sreg-tbl-nth rname (DQ-sreg-tbl (MA-DQ MA))))
	    (INST-tag (LSRM-in-ROB rname MT))))
  :hints (("goal" :in-theory (enable consistent-sreg-ref-p lift-b-ops)))))

; Field tag of the special register reference table entry designates
; the ROB entry to which the last modifier of the special register is
; assigned.
(defthm reg-ref-tag-points-to-LSRM-in-ROB
    (implies (and (inv MT MA)
		  (b1p (reg-ref-wait?
			(sreg-tbl-nth rname (DQ-sreg-tbl (MA-DQ MA)))))
		  (srname-p rname)
		  (not (b1p (MT-specultv-at-dispatch? MT)))
		  (not (b1p (MT-modified-at-dispatch? MT))))
	     (equal (reg-ref-tag
		     (sreg-tbl-nth rname (DQ-sreg-tbl (MA-DQ MA))))
		    (INST-tag (LSRM-in-ROB rname MT))))
  :hints (("goal" :in-theory (enable inv consistent-sreg-tbl-p
				     srname-p)
		  :cases ((equal rname 0) (equal rname 1)))))
)
;; End of the lemmas about the relation between the register modifiers
;; and the register reference table. 

;; Lemmas about the behavior of register modifiers in the ISA model.

; If instruction i is not a write-back instruction, it does not modify 
; the register file in ISA executions.
;
; Note: the same lemma is proven in ISA-comp.lisp.  We want to move
; it to one of the books containing shared lemmas, but we have not 
; yet found the right place.
(defthm ISA-RF-ISA-step-if-not-INST-wb
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (not (b1p (INST-wb? i))))
	     (equal (ISA-RF (ISA-step (INST-pre-ISA i) intr))
		    (ISA-RF (INST-pre-ISA i))))
  :hints (("goal" :in-theory (enable ISA-step-functions ISA-step
				     INST-wb? INST-cntlv
				     INST-opcode
				     opcode-inst-type))))

; If (INST-wb-sreg? i) is 1, instruction i does not modify
; general register file in the ISA execution. WB-sreg? specifies whether
; the instruction modifies a general register or a special register. 
; Wb-SRF? is 1 iff the instruction is modifying a special register.
(defthm read-reg-ISA-step-if-INST-wb-sreg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (rname-p rname)
		  (b1p (INST-wb-sreg? i)))
     (equal (read-reg rname (ISA-RF (ISA-step (INST-pre-ISA i) intr)))
	    (read-reg rname (ISA-RF (INST-pre-ISA i)))))
  :hints (("goal" :in-theory (enable INST-wb-sreg? decode INST-cntlv
				     lift-b-ops rdb logbit*
				     INST-opcode
				     ISA-step ISA-step-functions))))

; If (INST-dest-reg i) is different from rname, instruction i does 
; not modify register rname.
(defthm read-reg-ISA-step-if-not-INST-dest-reg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (rname-p rname)
		  (not (equal (INST-dest-reg I) rname)))
     (equal (read-reg rname (ISA-RF (ISA-step (INST-pre-ISA i) intr)))
	    (read-reg rname (ISA-RF (INST-pre-ISA i)))))
  :hints (("goal" :in-theory (enable INST-DEST-REG
				     INST-rc INST-ra
				     ISA-step ISA-step-functions))))

; If instruction i is not a register modifier of register rname,
; i does not modify the value of register rname.
(defthm read-reg-ISA-step-non-reg-modifier
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (rname-p rname)
		  (not (reg-modifier-p rname i)))
     (equal (read-reg rname (ISA-RF (ISA-step (INST-pre-ISA i) intr)))
	    (read-reg rname (ISA-RF (INST-pre-ISA i)))))
  :hints (("goal" :in-theory (enable  reg-modifier-p))))

; If (INST-wb? i) is 0, instruction i does not modify
; special register file.
(defthm read-sreg-ISA-step-if-not-INST-wb
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)  (INST-in i MT)
		  (rname-p rname)
		  (not (b1p (INST-wb? i)))
		  (not (b1p (INST-excpt? i)))
		  (not (b1p (INST-context-sync? i)))
		  (not (b1p (ISA-input-exint intr))))
     (equal (read-sreg rname (ISA-SRF (ISA-step (INST-pre-ISA i) intr)))
	    (read-sreg rname (ISA-SRF (INST-pre-ISA i)))))
  :hints (("goal" :in-theory (enable decode
				     lift-b-ops rdb logbit*
				     equal-b1p-converter
				     DECODE-ILLEGAL-INST?
				     INST-function-def
				     ISA-step ISA-step-functions))))
				     
; If (INST-wb-sreg? i) is 0, instruction i does not modify
; the special register file.
(defthm read-sreg-ISA-step-if-not-INST-wb-sreg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (rname-p rname)
		  (not (b1p (INST-wb-sreg? i)))
		  (not (b1p (INST-excpt? i)))
		  (not (b1p (INST-context-sync? i)))
		  (not (b1p (ISA-input-exint intr))))
     (equal (read-sreg rname (ISA-SRF (ISA-step (INST-pre-ISA i) intr)))
	    (read-sreg rname (ISA-SRF (INST-pre-ISA i)))))
  :hints (("goal" :in-theory (enable decode lift-b-ops rdb logbit*
				     DECODE-ILLEGAL-INST?
				     INST-function-def
				     ISA-step ISA-step-functions))))

; If (INST-dest-reg i) is different from rname, instruction i does 
; not modify special register rname.
(defthm read-sreg-ISA-step-if-not-INST-dest-reg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (srname-p rname)
		  (not (equal (INST-dest-reg I) rname))
		  (not (b1p (INST-excpt? i)))
		  (not (b1p (INST-context-sync? i)))
		  (not (b1p (ISA-input-exint intr))))
     (equal (read-sreg rname (ISA-SRF (ISA-step (INST-pre-ISA i) intr)))
	    (read-sreg rname (ISA-SRF (INST-pre-ISA i)))))
  :hints (("goal" :in-theory (enable INST-DEST-REG
				     decode rdb logbit* lift-b-ops
				     equal-b1p-converter
				     INST-function-def DECODE-ILLEGAL-INST?
				     INST-rc INST-ra
				     ISA-step ISA-step-functions))))

; If i is not a register modifier of a special register rname, i does not
; modify the special register.
(defthm read-sreg-ISA-step-non-sreg-modifier
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (srname-p rname)
		  (not (sreg-modifier-p rname i))
		  (not (b1p (INST-excpt? i)))
		  (not (b1p (INST-context-sync? i)))
		  (not (b1p (ISA-input-exint intr))))
     (equal (read-sreg rname (ISA-SRF (ISA-step (INST-pre-ISA i) intr)))
	    (read-sreg rname (ISA-SRF (INST-pre-ISA i)))))
  :hints (("goal" :in-theory (enable  sreg-modifier-p srname-p))))
    
(in-theory (enable not-member-of-cdr-if-car-is-IFU-stg))

;; End of the lemmas about the behavior of register modifiers in the ISA model.

;; More complex lemmas follows.  Major topics are
;;   pipeline stages and register modifiers.
;;   register modifiers and MA-step.
(encapsulate nil
(local
(defthm not-committed-p-trace-LRM-before
    (implies (and (no-commit-inst-p trace)  
		  (trace-exist-uncommitted-LRM-before-p i rname trace))
	     (not (committed-p (trace-LRM-before i rname trace))))))
    

(local
(defthm not-committed-p-LRM-before-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace) 
		  (member-equal i trace)
		  (committed-p
		   (trace-LRM-before i rname trace)))
	     (not (trace-exist-uncommitted-LRM-before-p I rname trace)))))

; (exist-LRM-before-p i rname MT) is true only if there exists
; an uncommitted register modifier of register rname before i.
(defthm not-committed-p-LRM-before
     (implies (and (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-in i MT)
		   (committed-p (LRM-before i rname MT)))
	      (not (exist-uncommitted-LRM-before-p i rname MT)))
  :hints (("goal" :in-theory (enable LRM-before
				     INST-in
				     exist-uncommitted-LRM-before-p)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary 
        (implies (and (inv MT MA)
		      (MAETT-p MT) (MA-state-p MA)
		      (INST-in i MT)
		      (exist-uncommitted-LRM-before-p I rname MT))
		 (not (committed-p (LRM-before I rname MT)))))))
)

(encapsulate nil
(local
(defthm not-committed-p-trace-LSRM-before
    (implies (and (no-commit-inst-p trace)  
		  (trace-exist-uncommitted-LSRM-before-p i rname trace))
	     (not (committed-p (trace-LSRM-before i rname trace))))))
    

(local
(defthm not-committed-p-LSRM-before-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace) 
		  (member-equal i trace)
		  (committed-p
		   (trace-LSRM-before i rname trace)))
	     (not (trace-exist-uncommitted-LSRM-before-p I rname trace)))))

; exist-LSRM-before-p is true only if there exists an
; uncommitted register modifier of special register rname.
(defthm not-committed-p-LSRM-before
     (implies (and (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-in i MT)
		   (committed-p (LSRM-before I rname MT)))
	      (not (exist-uncommitted-LSRM-before-p I rname MT)))
  :hints (("goal" :in-theory (enable LSRM-before
				     INST-in
				     exist-uncommitted-LSRM-before-p)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
     (implies (and (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-in i MT)
		   (exist-uncommitted-LSRM-before-p I rname MT))
	      (not (committed-p (LSRM-before I rname MT)))))))
)

; Following two lemmas say that last register modifier in the ROB is 
; dispatched and not committed. 
(encapsulate nil
(local
(defthm dispatched-p-LRM-in-ROB-help
    (implies (trace-exist-LRM-in-ROB-p idx trace)
	     (dispatched-p (trace-LRM-in-ROB idx trace)))))

(defthm dispatched-p-LRM-in-ROB
    (implies (exist-LRM-in-ROB-p idx MT)
	     (dispatched-p (LRM-in-ROB idx MT)))
  :hints (("goal" :in-theory (enable exist-LRM-in-ROB-p
				     LRM-in-ROB))))
)

(encapsulate nil
(local
(defthm not-committed-p-LRM-in-ROB-help
    (implies (trace-exist-LRM-in-ROB-p idx trace)
	     (not (committed-p (trace-LRM-in-ROB idx trace))))))

(defthm not-committed-p-LRM-in-ROB
    (implies (exist-LRM-in-ROB-p idx MT)
	     (not (committed-p (LRM-in-ROB idx MT))))
  :hints (("Goal" :in-theory (enable exist-LRM-in-ROB-p
				     LRM-in-ROB))))
)

; (Last-reg-modifier-before i) is a dispatched instruction if
; i is also dispatched. 
(defthm dispatched-p-LRM-before-dispatched
    (implies (and (dispatched-p i)
		  (exist-LRM-before-p i rname MT)
		  (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT))
	     (dispatched-p (LRM-before i rname MT)))
  :hints (("goal" :use (:instance INST-IN-ORDER-LRM-BEFORE)
		  :in-theory (disable INST-IN-ORDER-LRM-BEFORE))))

; (Last-sreg-modifier-before i) is a dispatched instruction if
; i is also dispatched. 
(defthm dispatched-p-LSRM-before-dispatched
    (implies (and (dispatched-p i)
		  (exist-LSRM-before-p i rname MT)
		  (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT))
	     (dispatched-p (LSRM-before i rname MT)))
  :hints (("goal" :use (:instance INST-IN-ORDER-LSRM-BEFORE)
		  :in-theory (disable INST-IN-ORDER-LSRM-BEFORE))))

(defthm exist-LRM-before-p-and-exist-uncommitted-LRM-before-p
     (implies (and (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-in i MT))
	      (iff (exist-uncommitted-LRM-before-p i rname MT)
		   (and (exist-LRM-before-p i rname MT)
			(not (committed-p (LRM-before i rname MT)))))))

(defthm exist-LSRM-before-p-and-exist-uncommitted-LSRM-before-p
     (implies (and (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-in i MT))
	      (iff (exist-uncommitted-LSRM-before-p i rname MT)
		   (and (exist-LSRM-before-p i rname MT)
			(not (committed-p (LSRM-before i rname MT)))))))
(in-theory
 (disable exist-LRM-before-p-and-exist-uncommitted-LRM-before-p
	  exist-LSRM-before-p-and-exist-uncommitted-LSRM-before-p))

; Following two lemmas say that the last register or special register
; modifier in ROB is not in the dispatch queue.
(encapsulate nil
(local
(defthm not-DQ-stg-p-LRM-in-ROB-help
    (implies (trace-exist-LRM-in-ROB-p idx trace)
	     (not (DQ-stg-p (INST-stg (trace-LRM-in-ROB idx trace)))))))

(defthm not-DQ-stg-p-LRM-in-ROB
    (implies (exist-LRM-in-ROB-p idx MT)
	     (not (DQ-stg-p (INST-stg (LRM-in-ROB idx MT)))))
  :hints (("Goal" :in-theory (enable LRM-in-ROB exist-LRM-in-ROB-p))))
)

(encapsulate nil
(local
(defthm not-DQ-stg-p-LSRM-in-ROB-help
    (implies (trace-exist-LSRM-in-ROB-p idx trace)
	     (not (DQ-stg-p (INST-stg (trace-LSRM-in-ROB idx trace)))))))

(defthm not-DQ-stg-p-LSRM-in-ROB
    (implies (exist-LSRM-in-ROB-p idx MT)
	     (not (DQ-stg-p (INST-stg (LSRM-in-ROB idx MT)))))
  :hints (("Goal" :in-theory (enable LSRM-in-ROB exist-LSRM-in-ROB-p))))
)

(encapsulate nil
(local
(defthm not-trace-exist-LRM-in-ROB-p-if-no-dispatched-inst-p
    (implies (no-dispatched-inst-p trace)
	     (not (trace-exist-LRM-in-ROB-p rname trace)))))

; A help lemma.
(defthm not-trace-reg-modifier-cdr-if-car-not-dispatched
    (implies (and (consp trace)
		  (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace) 
		  (not (dispatched-p (car trace))))
	     (not (trace-exist-LRM-in-ROB-p rname (cdr trace))))
  :hints (("goal" :cases ((no-dispatched-inst-p (cdr trace))))
	  ("subgoal 1" :in-theory (disable NO-DISPATCHED-INST-P-CDR))))
)

(encapsulate nil
(local
(defthm exist-LRM-before-p-undispatched-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-p i) (member-equal i trace)
		  (INST-listp trace)
		  (not (dispatched-p i))
		  (trace-exist-LRM-in-ROB-p rname trace))
	     (trace-exist-LRM-before-p i rname trace))))

; If instruction i is not dispatched, and a register modifier of rname is
; in the ROB,  there exist register modifiers preceding i.
(defthm exist-LRM-before-p-undispatched
    (implies (and (inv MT MA)
		  (not (dispatched-p i))
		  (exist-LRM-in-ROB-p rname MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (exist-LRM-before-p i rname MT))
  :hints (("goal" :in-theory (enable exist-LRM-before-p
				     exist-LRM-in-ROB-p INST-in))))
)

(encapsulate nil
(local
(defthm not-trace-exist-LSRM-in-ROB-p-if-no-dispatched-inst-p
    (implies (no-dispatched-inst-p trace)
	     (not (trace-exist-LSRM-in-ROB-p rname trace)))))

; A help lemma.
(defthm not-trace-sreg-modifier-cdr-if-car-not-dispatched
    (implies (and (consp trace)
		  (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace) 
		  (not (dispatched-p (car trace))))
	     (not (trace-exist-LSRM-in-ROB-p rname (cdr trace))))
  :hints (("goal" :cases ((no-dispatched-inst-p (cdr trace))))
	  ("subgoal 1" :in-theory (disable NO-DISPATCHED-INST-P-CDR))))
)

(encapsulate nil
(local
(defthm exist-LSRM-before-p-undispatched-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-p i) (member-equal i trace)
		  (INST-listp trace)
		  (not (dispatched-p i))
		  (trace-exist-LSRM-in-ROB-p rname trace))
	     (trace-exist-LSRM-before-p i rname trace))))

; If instruction i is not dispatched, and a register modifier of 
; special register rname is in the ROB,  there exist register modifiers
; preceding i. 
(defthm exist-LSRM-before-p-undispatched
    (implies (and (inv MT MA)
		  (not (dispatched-p i))
		  (exist-LSRM-in-ROB-p rname MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (exist-LSRM-before-p i rname MT))
  :hints (("goal" :in-theory (enable exist-LSRM-before-p
				     exist-LSRM-in-ROB-p INST-in))))
)

(encapsulate nil
(local
(defthm exist-LRM-in-ROB-p-iff-exist-uncommitted-LRM-before-p-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace) 
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (member-equal i trace))
	     (equal (trace-exist-uncommitted-LRM-before-p i rname trace)
		    (trace-exist-LRM-in-ROB-p rname trace)))))

; If instruction i is at (DQ 0), (exist-LRM-before-p i rname MT) iff
; (exist-LRM-in-ROB-p rname MT).  See the comment of 
; INST-dest-val-LRM-in-ROB
(defthm exist-LRM-in-ROB-p-iff-exist-uncommitted-LRM-before-p
   (implies (and (inv MT MA)
		 (equal (INST-stg i) '(DQ 0))
		 (MAETT-p MT) (MA-state-p MA)
		 (INST-p i) (INST-in i MT))
	     (equal (exist-uncommitted-LRM-before-p i rname MT)
		    (exist-LRM-in-ROB-p rname MT)))
  :hints (("goal" :in-theory (enable exist-LRM-in-ROB-p
				     exist-uncommitted-LRM-before-p
				     INST-in)))
  :rule-classes
  ((:rewrite :corollary
	     (implies (and (inv MT MA)
			   (exist-LRM-in-ROB-p rname MT)
			   (equal (INST-stg i) '(DQ 0))
			   (MAETT-p MT) (MA-state-p MA)
			   (INST-p i) (INST-in i MT))
		      (exist-uncommitted-LRM-before-p i rname MT)))
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (not (exist-LRM-in-ROB-p rname MT))
			   (equal (INST-stg i) '(DQ 0))
			   (MAETT-p MT) (MA-state-p MA)
			   (INST-p i) (INST-in i MT))
		      (not (exist-uncommitted-LRM-before-p i rname MT))))))

(local
(defthm INST-dest-val-LRM-in-ROB-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (equal (INST-stg i) '(DQ 0))
		  (INST-listp trace)
		  (INST-p i) (member-equal i trace)
		  (trace-exist-LRM-in-ROB-p rname trace))
	     (equal (trace-LRM-in-ROB rname trace)
		    (trace-LRM-before i rname trace)))))

; If instruction i is at (DQ 0), the last register modifier before i
; is the last register modifier in ROB.  This is a critical lemma in
; proving the correctness of our invariants.  The register reference table 
; keeps track of the last instruction in the ROB that modifies registers. 
; A dispatched instruction uses this information to get the operand source
; value.  This lemmas implies that that behavior is correct because
; the source operand for instruction i should come from the last register 
; modifier before i. 
(defthm INST-dest-val-LRM-in-ROB
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(DQ 0))
		  (exist-LRM-in-ROB-p rname MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT))
	     (equal (LRM-in-ROB rname MT)
		    (LRM-before i rname MT)))
  :hints (("goal" :in-theory (enable LRM-in-ROB
				     LRM-before
				     exist-LRM-in-ROB-p
				     INST-in))))
)

(encapsulate nil
(local
(defthm exist-LSRM-in-ROB-p-iff-exist-uncommitted-LSRM-before-p-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace) 
		  (equal (INST-stg i) '(DQ 0))
		  (INST-p i) (member-equal i trace))
	     (equal (trace-exist-uncommitted-LSRM-before-p i rname trace)
		    (trace-exist-LSRM-in-ROB-p rname trace)))))

; If instruction i is at (DQ 0), (exist-LSRM-before-p i rname MT) and
; (exist-LSRM-in-ROB-p rname MT) are equivalent.
(defthm exist-LSRM-in-ROB-p-iff-exist-uncommitted-LSRM-before-p
   (implies (and (inv MT MA)
		 (equal (INST-stg i) '(DQ 0))
		 (MAETT-p MT) (MA-state-p MA)
		 (INST-p i) (INST-in i MT))
	     (equal (exist-uncommitted-LSRM-before-p i rname MT)
		    (exist-LSRM-in-ROB-p rname MT)))
  :hints (("goal" :in-theory (enable exist-LSRM-in-ROB-p
				     exist-uncommitted-LSRM-before-p
				     INST-in)))
  :rule-classes
  ((:rewrite :corollary
	     (implies (and (inv MT MA)
			   (equal (INST-stg i) '(DQ 0))
			   (MAETT-p MT) (MA-state-p MA)
			   (INST-p i) (INST-in i MT)
			   (exist-LSRM-in-ROB-p rname MT))
		      (exist-uncommitted-LSRM-before-p i rname MT)))
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (equal (INST-stg i) '(DQ 0))
			   (MAETT-p MT) (MA-state-p MA)
			   (INST-p i) (INST-in i MT)
			   (not (exist-LSRM-in-ROB-p rname MT)))
		      (not (exist-uncommitted-LSRM-before-p i rname MT))))))

(local
(defthm INST-dest-val-LSRM-in-ROB-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (equal (INST-stg i) '(DQ 0))
		  (INST-listp trace)
		  (INST-p i) (member-equal i trace)
		  (trace-exist-LSRM-in-ROB-p rname trace))
	     (equal (trace-LSRM-in-ROB rname trace)
		    (trace-LSRM-before i rname trace)))))

; If instruction i is at (DQ 0), the last register modifier before i
; is the last register modifier in ROB.  See the comment
; of INST-dest-val-LRM-in-ROB.
(defthm INST-dest-val-LSRM-in-ROB
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(DQ 0))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (exist-LSRM-in-ROB-p rname MT))
	     (equal (LSRM-in-ROB rname MT)
		    (LSRM-before i rname MT)))
    :hints (("goal" :in-theory (enable LSRM-in-ROB
				     LSRM-before
				     exist-LSRM-in-ROB-p
				     INST-in))))
)

;  The ROB contains a field complete?.  This field is 1 if the corresponding
; instruction has completed its execution.  This lemma says that
; the last register modifier is still being executed if the corresponding
; complete? flag in the ROB is off. 
(defthm execute-stg-LRM-before
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (exist-uncommitted-LRM-before-p I rname MT)
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (robe-complete? 
			     (nth-robe (INST-tag (LRM-before i rname MT))
				       (MA-rob MA))))))
     (execute-stg-p (INST-stg (LRM-before i rname MT))))
  :hints (("goal" :in-theory (e/d (IFU-IS-LAST-INST
				   DQ0-is-earlier-than-other-DQ)
				  (INST-in-order-LRM-before
				   INST-is-at-one-of-the-stages
				      committed-p))
		  :use ((:instance INST-is-at-one-of-the-stages
			     (i (LRM-before i rname MT)))
			(:instance INST-in-order-LRM-before)))))

; Similar to the lemma above.
(defthm execute-stg-LSRM-before
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (exist-uncommitted-LSRM-before-p I rname MT)
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (robe-complete? 
			     (nth-robe (INST-tag (LSRM-before i rname MT))
				       (MA-rob MA))))))
     (execute-stg-p (INST-stg (LSRM-before i rname MT))))
  :hints (("goal" :in-theory (e/d (IFU-IS-LAST-INST
				   DQ0-is-earlier-than-other-DQ)
				  (INST-in-order-LSRM-before
				   INST-is-at-one-of-the-stages
				      committed-p))
		  :use ((:instance INST-is-at-one-of-the-stages
				   (i (LSRM-before i rname MT)))
			(:instance INST-in-order-LSRM-before)))))

(encapsulate nil
(local
(defthm not-exist-LRM-before-p-step-INST-help
    (implies (and (inv MT MA)
		  (member-equal i trace) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (subtrace-p trace MT) (INST-listp trace) 
		  (not (trace-exist-LRM-before-p i idx trace))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (trace-exist-LRM-before-p (step-inst i MT MA sigs)
			   idx (step-trace trace MT MA sigs ISA spc smc))))))

(local
(defthm exist-LRM-before-p-step-INST-help
    (implies (and (inv MT MA)
		  (member-equal i trace) (INST-p i)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (not (b1p (flush-all? MA sigs)))
		  (trace-exist-LRM-before-p i idx trace)
		  (MAETT-p MT) (MA-state-p MA))
	     (trace-exist-LRM-before-p (step-inst i MT MA sigs)
		      idx (step-trace trace MT MA sigs ISA spc smc))))) 

(local
(defthm LRM-before-step-INST-help
    (Implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)  
		  (member-equal i trace) (INST-p i) 
		  (not (b1p (flush-all? MA sigs)))
		  (trace-exist-LRM-before-p i idx trace)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (trace-LRM-before (step-INST i MT MA sigs)
			    idx (step-trace trace MT MA sigs ISA spc smc))
		    (step-INST (trace-LRM-before i idx trace)
			       MT MA sigs)))))

; Commutativity of LRM-before and step-INST.
(defthm LRM-before-step-INST
    (Implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (not (b1p (flush-all? MA sigs)))
;		  (execute-stg-p
;		   (INST-stg (LRM-before i idx MT)))
		  (exist-LRM-before-p i idx MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LRM-before (step-INST i MT MA sigs)
				idx (MT-step MT MA sigs))
		    (step-INST (LRM-before i idx MT)
			       MT MA sigs)))
  :hints (("Goal" :in-theory (enable LRM-before
				     exist-LRM-before-p INST-in))))

; If there is an register modifier before i, then there still is a register
; modifier before i in the next cycle. 
(defthm exist-LRM-before-p-step-INST
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (exist-LRM-before-p i idx MT)
;		  (execute-stg-p (INST-stg
;				  (LRM-before i idx MT)))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LRM-before-p (step-INST i MT MA sigs)
				 idx (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable exist-LRM-before-p
				     LRM-before
				     INST-in))))

(local
(defthm not-exist-uncommitted-LRM-before-p-step-INST-help
    (implies (and (inv MT MA)
		  (member-equal i trace) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (subtrace-p trace MT) (INST-listp trace) 
		  (not (trace-exist-uncommitted-LRM-before-p i idx trace))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (trace-exist-uncommitted-LRM-before-p
		   (step-inst i MT MA sigs)
		   idx (step-trace trace MT MA sigs ISA spc smc))))))

(local
(defthm exist-uncommitted-LRM-before-p-step-INST-help
    (implies (and (inv MT MA)
		  (member-equal i trace) (INST-p i)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (not (b1p (flush-all? MA sigs)))
		  (trace-exist-uncommitted-LRM-before-p i idx trace)
		  (execute-stg-p
		   (INST-stg
		    (trace-LRM-before i idx trace)))
		  (MAETT-p MT) (MA-state-p MA))
	     (trace-exist-uncommitted-LRM-before-p (step-inst i MT MA sigs)
		      idx (step-trace trace MT MA sigs ISA spc smc))))) 

(defthm exist-uncommitted-LRM-before-p-step-INST
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (exist-uncommitted-LRM-before-p i idx MT)
		  (execute-stg-p (INST-stg
				  (LRM-before i idx MT)))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-uncommitted-LRM-before-p (step-INST i MT MA sigs)
					     idx (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable exist-uncommitted-LRM-before-p
				     LRM-before
				     INST-in))))

; The last register modifier continues to have the same ROB entry number
; in the next cycle.
(defthm INST-tag-LRM-before-step-INST
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (exist-LRM-before-p i idx MT)
		  (execute-stg-p (INST-stg
				  (LRM-before i idx MT)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (INST-tag (LRM-before (step-INST i MT MA sigs)
					  idx (MT-step MT MA sigs)))
		    (INST-tag (LRM-before i idx MT))))
  :hints (("goal" :in-theory (enable exist-LRM-before-p
				     LRM-before
				     INST-in))))
)

(encapsulate nil
(local
(defthm not-exist-LSRM-before-p-step-INST-help
    (implies (and (inv MT MA)
		  (member-equal i trace) (INST-p i)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (not (b1p (flush-all? MA sigs)))
		  (not (trace-exist-LSRM-before-p i idx trace))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (trace-exist-LSRM-before-p (step-inst i MT MA sigs)
			   idx (step-trace trace MT MA sigs ISA spc smc))))))

(local
(defthm exist-LSRM-before-p-step-INST-help
    (implies (and (inv MT MA)
		  (member-equal i trace) (INST-p i)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (not (b1p (flush-all? MA sigs)))
		  (trace-exist-LSRM-before-p i idx trace)
		  (MAETT-p MT) (MA-state-p MA))
	     (trace-exist-LSRM-before-p (step-inst i MT MA sigs)
		      idx (step-trace trace MT MA sigs ISA spc smc))))) 

(local
(defthm LSRM-before-step-INST-help
    (Implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)  
		  (member-equal i trace) (INST-p i) 
		  (not (b1p (flush-all? MA sigs)))
		  (trace-exist-LSRM-before-p i idx trace)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (trace-LSRM-before (step-INST i MT MA sigs)
			    idx (step-trace trace MT MA sigs ISA spc smc))
		    (step-INST (trace-LSRM-before i idx trace)
			       MT MA sigs)))))

; Commutativity of LSRM-before and step-INST.
(defthm LSRM-before-step-INST
    (Implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (not (b1p (flush-all? MA sigs)))
		  (exist-LSRM-before-p i idx MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSRM-before (step-INST i MT MA sigs)
				 idx (MT-step MT MA sigs))
		    (step-INST (LSRM-before i idx MT)
			       MT MA sigs)))
  :hints (("Goal" :in-theory (enable LSRM-before
				     exist-LSRM-before-p INST-in))))

; If special register modifiers exist in the current cycle, they will
; in the next cycle. 
(defthm exist-LSRM-before-p-step-INST
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (exist-LSRM-before-p i idx MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-LSRM-before-p (step-INST i MT MA sigs)
				  idx (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable exist-LSRM-before-p
				     LSRM-before
				     INST-in))))

(local
(defthm not-exist-uncommitted-LSRM-before-p-step-INST-help
    (implies (and (inv MT MA)
		  (member-equal i trace) (INST-p i)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (not (b1p (flush-all? MA sigs)))
		  (not (trace-exist-uncommitted-LSRM-before-p i idx trace))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (trace-exist-uncommitted-LSRM-before-p
		   (step-inst i MT MA sigs)
		   idx (step-trace trace MT MA sigs ISA spc smc))))))

(local
(defthm exist-uncommitted-LSRM-before-p-step-INST-help
    (implies (and (inv MT MA)
		  (member-equal i trace) (INST-p i)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (not (b1p (flush-all? MA sigs)))
		  (trace-exist-uncommitted-LSRM-before-p i idx trace)
		  (execute-stg-p (INST-stg (trace-LSRM-before i idx trace)))
		  (MAETT-p MT) (MA-state-p MA))
	     (trace-exist-uncommitted-LSRM-before-p (step-inst i MT MA sigs)
		      idx (step-trace trace MT MA sigs ISA spc smc))))) 

(defthm exist-uncommitted-LSRM-before-p-step-INST
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (exist-uncommitted-LSRM-before-p i idx MT)
		  (execute-stg-p (INST-stg (LSRM-before i idx MT)))
		  (MAETT-p MT) (MA-state-p MA))
	     (exist-uncommitted-LSRM-before-p (step-INST i MT MA sigs)
					      idx (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable exist-uncommitted-LSRM-before-p
				     LSRM-before
				     INST-in))))

; The special register modifier continues to have the same tag entry
; number in the next cycle. 
(defthm INST-tag-LSRM-before-step-INST
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (exist-LSRM-before-p i idx MT)
		  (execute-stg-p (INST-stg (LSRM-before i idx MT)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (INST-tag (LSRM-before (step-INST i MT MA sigs)
					   idx (MT-step MT MA sigs)))
		    (INST-tag (LSRM-before i idx MT))))
  :hints (("goal" :in-theory (enable exist-LSRM-before-p
				     LSRM-before
				     INST-in))))
)

;;;;;;;;;;;;;;;;;;End of reg-modifier theory;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;Lemmas about memory modifiers;;;;;;;;;;;;;;;;;;;;;;;
(encapsulate nil
(local
 (defthm inst-in-LMM-before-help
    (implies (trace-exist-LMM-before-p i addr trace)
	     (member-equal (trace-LMM-before i addr trace)
			   trace))))

(defthm inst-in-LMM-before
    (implies (exist-LMM-before-p i addr MT)
	     (INST-in (LMM-before i addr MT) MT))
  :hints (("goal" :in-theory (enable INST-in LMM-before exist-LMM-before-p))))
)

(encapsulate nil
(local
 (defthm LMM-before-differs-from-i-help
    (implies (trace-exist-LMM-before-p i addr MT)
	     (not (equal (trace-LMM-before i addr MT) i)))))

; The last memory modifier before i is not i.
(defthm LMM-before-differs-from-i
    (implies (exist-LMM-before-p i addr MT)
	     (not (equal (LMM-before i addr MT) i)))
  :hints (("goal" :in-theory (enable exist-LMM-before-p
				     LMM-before))))
)

(encapsulate nil
(local
 (defthm INST-in-order-LMM-before-help
    (implies (and (member-equal i trace)
		  (trace-exist-LMM-before-p I addr trace))
	     (member-in-order (trace-LMM-before i addr trace)
			      i trace))
   :hints (("goal" :in-theory (enable member-in-order*)))))

; The last memory modifier before i precedes i.
(defthm INST-in-order-LMM-before
    (implies (and (INST-in i MT) (exist-LMM-before-p I addr MT))
	     (INST-in-order-p (LMM-before i addr MT) i MT))
  :hints (("goal" :in-theory (enable LMM-before INST-in
				     INST-in-order-p exist-LMM-before-p))))
)

(encapsulate nil
(local
(defthm mem-modifier-p-LMM-before-help
    (implies (trace-exist-LMM-before-p I addr trace)
	     (mem-modifier-p addr (trace-LMM-before I addr trace)))))

; The last memory modifier is a memory modifier.
(defthm mem-modifier-p-LMM-before
    (implies (exist-LMM-before-p I addr MT)
	     (mem-modifier-p addr (LMM-before I addr MT)))
  :hints (("goal" :in-theory (enable exist-LMM-before-p LMM-before))))
)

; A mem-modifier satisfies INST-store?
(defthm not-mem-modifier-p-if-not-INST-store?
    (implies (not (b1p (INST-store? i)))
	     (not (mem-modifier-p addr i)))
  :hints (("goal" :in-theory (enable mem-modifier-p 
				     INST-function-def
				     decode logbit* rdb lift-b-ops))))

; A last memory modifier satisfies INST-store?
(defthm INST-store-LRM-before
    (implies (and (MAETT-p MT) (INST-p i)
		  (exist-LMM-before-p I addr MT))
	     (equal (INST-store? (LMM-before I addr MT))
		    1))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter)
				  (not-mem-modifier-p-if-not-INST-store?))
		  :use (:instance not-mem-modifier-p-if-not-INST-store?
				  (i (LMM-before I addr MT))))))

; If the access address of an last memory modifier at address addr is, in
; fact, addr. 
(defthm INST-store-addr-LMM
    (implies (exist-LMM-before-p i addr MT)
	     (equal (INST-store-addr (LMM-before i addr MT))
		    addr))
  :hints (("goal" :in-theory (e/d (mem-modifier-p)
				  (MEM-MODIFIER-P-LMM-BEFORE))
		  :use (:instance MEM-MODIFIER-P-LMM-BEFORE))))

; (Last-mem-modifier-before i) is a dispatched instruction if
; i is dispatched, because instructions are dispatched in program order. 
(defthm dispatched-p-LMM-before-dispatched
    (implies (and (dispatched-p i)
		  (exist-LMM-before-p i addr MT)
		  (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT))
	     (dispatched-p (LMM-before i addr MT)))
  :hints (("goal" :use (:instance INST-IN-ORDER-LMM-BEFORE)
		  :in-theory (disable INST-IN-ORDER-LMM-BEFORE))))

; If j is the last register modifier before i, and i is not speculatively
; executed instruction, then j is not speculatively executed, either. 
(defthm INST-specultv-LMM-before
    (implies (and (inv MT MA)
		  (exist-LMM-before-p i addr MT)
		  (not (b1p (INST-specultv? i)))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)) 
	     (equal (INST-specultv? (LMM-before i addr MT))
		    0))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter)
				  (INST-in-order-p-INST-specultv))
		  :use (:instance INST-in-order-p-INST-specultv
				  (i (LMM-before i addr MT))
				  (j i)))))

; If j is the last register modifier before i, and i's modified flag is not
; on, then j's modified flag is not on either.
(defthm INST-modified-LMM-before
    (implies (and (inv MT MA)
		  (exist-LMM-before-p i addr MT)
		  (not (b1p (INST-modified? I)))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)) 
	     (equal (INST-modified? (LMM-before i addr MT))
		    0))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter)
				  (INST-in-order-p-INST-modified))
		  :use (:instance INST-in-order-p-INST-modified
				  (i (LMM-before i addr MT))
				  (j i)))))

(encapsulate nil
(local
 (defthm not-fetch-error-detected-p-if-commit-stg-p
     (implies (and (inv MT MA)
		   (INST-in i MT) (INST-p i)
		   (MAETT-p MT) (MA-state-p MA)
		   (not (b1p (INST-modified? i)))
		   (commit-stg-p (INST-stg i)))
	      (not (INST-fetch-error-detected-p i)))
   :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter
				 NOT-INST-SPECULTV-INST-IN-IF-COMMITTED
						 INST-excpt-detected-p)
				   (INST-inv-if-INST-in))
		   :use (:instance INST-inv-if-INST-in)))))
	   

; If j is the last register modifier before i, and i is not speculatively
; executed, then no fetch error is detected for j.  (In our theory, 
; speculation includes the execution of all instructions that should not
; be executed by the ISA.  Thus, an instruction following an exception 
; is a speculatively executed instruction.  )
(defthm INST-fetch-error-detected-p-LMM-before
    (implies (and (inv MT MA)
		  (exist-LMM-before-p i addr MT)
		  (not (retire-stg-p (INST-stg (LMM-before i addr MT))))
		  (not (b1p (INST-specultv? I)))
		  (not (b1p (INST-modified? I)))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)) 
	     (not (INST-fetch-error-detected-p (LMM-before i addr MT))))
    :hints (("goal" :in-theory (e/d (equal-b1p-converter
				     INST-start-specultv?
				     committed-p
				     INST-excpt?
				     lift-b-ops)
				  (INST-in-order-p-INST-start-specultv))
		  :use (:instance INST-in-order-p-INST-start-specultv
				  (i (LMM-before i addr MT))
				  (j i))
		  :restrict ((not-fetch-error-detected-p-if-commit-stg-p
			      ((i (LMM-before i addr MT))))))))
)

(encapsulate nil
(local
 (defthm not-excpt-detected-p-if-commit-stg-p
     (implies (and (inv MT MA)
		   (INST-in i MT) (INST-p i)
		   (MAETT-p MT) (MA-state-p MA)
		   (not (b1p (INST-modified? i)))
		   (commit-stg-p (INST-stg i)))
	      (not (INST-excpt-detected-p i)))
   :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter
				 NOT-INST-SPECULTV-INST-IN-IF-COMMITTED)
				   (INST-inv-if-INST-in))
		   :use (:instance INST-inv-if-INST-in)))))  

; If j is the last register modifier before i in program order, and 
; i is not speculatively executed, then j has not raised an exception.
; This is because the MAETT records instructions following an exceptions
; as a speculatively executed instruction. 
(defthm INST-excpt-detected-p-LMM-before
    (implies (and (inv MT MA)
		  (exist-LMM-before-p i addr MT)
		  (not (retire-stg-p (INST-stg (LMM-before i addr MT))))
		  (not (b1p (INST-specultv? I)))
		  (not (b1p (INST-modified? I)))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)) 
	     (not (INST-excpt-detected-p (LMM-before i addr MT))))
    :hints (("goal" :in-theory (e/d (equal-b1p-converter
				     INST-start-specultv?
				     committed-p
				     INST-excpt?
				     lift-b-ops)
				  (INST-in-order-p-INST-start-specultv))
		  :use (:instance INST-in-order-p-INST-start-specultv
				  (i (LMM-before i addr MT))
				  (j i)))))
)

(encapsulate nil
(local
(defthm not-excpt-detected-p-if-commit-stg-p
     (implies (and (inv MT MA)
		   (INST-in i MT) (INST-p i)
		   (MAETT-p MT) (MA-state-p MA)
		   (not (b1p (INST-modified? i)))
		   (commit-stg-p (INST-stg i)))
	      (not (b1p (INST-excpt? i))))
   :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter
				 NOT-INST-SPECULTV-INST-IN-IF-COMMITTED)
				   (INST-inv-if-INST-in))
		   :use (:instance INST-inv-if-INST-in)))))

; See the comment about INST-excpt-detected-p-LMM-before.
(defthm INST-excpt-LMM-before
    (implies (and (inv MT MA)
		  (exist-LMM-before-p i addr MT)
		  (not (retire-stg-p (INST-stg (LMM-before i addr MT))))
		  (not (b1p (INST-specultv? I)))
		  (not (b1p (INST-modified? I)))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)) 
	     (equal (INST-excpt? (LMM-before i addr MT)) 0))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter
				   INST-start-specultv?
				   committed-p
				   lift-b-ops)
				  (INST-in-order-p-INST-start-specultv))
		  :use (:instance INST-in-order-p-INST-start-specultv
				  (i (LMM-before i addr MT))
				  (j i)))))
)

(encapsulate nil
(local
(defthm  LMM-is-last-help-help
    (implies (trace-exist-LMM-before-p i addr trace)
	     (member-equal (trace-LMM-before i addr trace)
			   trace))))

(local
(defthm LMM-is-last-help
    (implies (and (distinct-member-p trace)
		  (member-equal j trace)
		  (mem-modifier-p addr j)
		  (member-in-order j i trace)
		  (not (equal (trace-LMM-before i addr trace) j)))
	     (member-in-order j (trace-LMM-before i addr trace)
			      trace))
  :hints (("goal" :in-theory (enable member-in-order*)))))

; If j is a memory modifier at address addr, and j precedes i in program 
; order, then j is the last memory modifier at addr, or the last memory
; modifier exists between j and i.
(defthm LMM-is-last
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in j MT) (INST-p j)
		  (mem-modifier-p addr j)
		  (INST-in i MT) (INST-p i)
		  (INST-in-order-p j i MT)
		  (not (equal (LMM-before i addr MT) j)))
	     (INST-in-order-p j (LMM-before i addr MT) MT))
  :hints (("goal" :in-theory (enable INST-in-order-p LMM-before
				     MT-distinct-inst-p
				     inv weak-inv
				     INST-in))))
)

(encapsulate nil
(local
(defthm exist-LMM-if-exist-non-retired-LMM-help
    (implies (trace-exist-non-retired-LMM-before-p i addr trace)
	     (trace-exist-LMM-before-p i addr trace))))

; Non-retired memory modifier is a memory modifier that has not
; retired.  If there exists an non-retired memory modifier before i,
; there is, in the normal sense, a memory modifier (the non-retired
; memory modifier itself).
(defthm exist-LMM-if-exist-non-retired-LMM
    (implies (exist-non-retired-LMM-before-p i addr MT)
	     (exist-LMM-before-p i addr MT))
  :hints (("goal" :in-theory (enable exist-non-retired-LMM-before-p
				     exist-LMM-before-p))))

)

; Instruction at write-buffer wbuf0 is a memory modifier at address
; (INST-store-addr i).
(defthm mem-modifier-p-INST-store-addr-if-wbuf0-stg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (wbuf0-stg-p (INST-stg i)))
	     (mem-modifier-p (INST-store-addr i) i))
  :hints (("goal" :in-theory (enable wbuf0-stg-p mem-modifier-p
				     LSU-STORE-IF-AT-LSU-WBUF))))

; Instruction at write-buffer wbuf1 is a memory modifier at address
; (INST-store-addr i).
(defthm mem-modifier-p-INST-store-addr-if-wbuf1-stg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (wbuf1-stg-p (INST-stg i)))
	     (mem-modifier-p (INST-store-addr i) i))
  :hints (("goal" :in-theory (enable wbuf1-stg-p mem-modifier-p
				     LSU-STORE-IF-AT-LSU-WBUF))))

; Following several lemmas help to locate the stage of the last memory
; modifier.  The last memory modifier before i is not at IFU stage or DQ
; stage when i is already in the execution stage, because the last memory
; modifier precedes i in program order.  The memory modifier cannot be
; in the integer unit, multiplier unit, or branch unit, of course. 
(defthm not-IFU-stg-p-LMM-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (execute-stg-p (INST-stg i))
		  (exist-LMM-before-p i addr MT))
	     (not (IFU-stg-p (INST-stg (LMM-before i addr MT)))))
  :hints (("goal" :use (:instance INST-in-order-LMM-before)
		  :in-theory (disable
			      INST-in-order-LMM-before
		      DISPATCHED-P-LMM-BEFORE-DISPATCHED))))

(defthm not-DQ-stg-p-LMM-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (execute-stg-p (INST-stg i))
		  (exist-LMM-before-p i addr MT))
	     (not (DQ-stg-p (INST-stg (LMM-before i addr MT)))))
  :hints (("goal" :in-theory (e/d (dispatched-p)
				  (DISPATCHED-P-LMM-BEFORE-DISPATCHED))
		  :use (:instance DISPATCHED-P-LMM-BEFORE-DISPATCHED))))

(defthm not-IU-stg-p-LMM-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (exist-LMM-before-p i addr MT)
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (not (IU-stg-p (INST-stg (LMM-before i addr MT)))))
  :hints (("goal" :cases ((b1p (INST-store? (LMM-before i addr MT)))))
	  ("subgoal 1" :in-theory (e/d (lift-b-ops equal-b1p-converter)
				       (INST-STORE-LRM-BEFORE
					INST-IU-IF-IU-STG-P))
		       :use (:instance INST-IU-IF-IU-STG-P
				       (i (LMM-before i addr MT))))))

(defthm not-MU-stg-p-LMM-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (exist-LMM-before-p i addr MT)
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (not (MU-stg-p (INST-stg (LMM-before i addr MT)))))
  :hints (("goal" :cases ((b1p (INST-store? (LMM-before i addr MT)))))
	  ("subgoal 1" :in-theory (e/d (lift-b-ops equal-b1p-converter)
				       (INST-STORE-LRM-BEFORE
					INST-MU-IF-MU-STG-P))
		       :use (:instance INST-MU-IF-MU-STG-P
				       (i (LMM-before i addr MT))))))

(defthm not-BU-stg-p-LMM-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (exist-LMM-before-p i addr MT)
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (not (BU-stg-p (INST-stg (LMM-before i addr MT)))))
  :hints (("goal" :cases ((b1p (INST-store? (LMM-before i addr MT)))))
	  ("subgoal 1" :in-theory (e/d (lift-b-ops equal-b1p-converter)
				       (INST-STORE-LRM-BEFORE
					INST-BU-IF-BU-STG-P))
		       :use (:instance INST-BU-IF-BU-STG-P
				       (i (LMM-before i addr MT))))))

; Following several rules specify which stage is not a legal stage for an
; memory modifier to stay.  See invariants in-order-LSU-inst-p.
(encapsulate nil
(local
(defthm not-no-issued-LSU-inst-p-if-member-equal
    (implies (and (member-equal i trace)
		  (LSU-issued-stg-p (INST-stg i)))
	     (not (no-issued-LSU-inst-p trace)))))
  
(local
(defthm LSU-rbuf-RS-in-order-help
    (implies (and (in-order-LSU-issue-p trace)
		  (member-equal i trace) (INST-p i)
		  (equal (INST-stg i) '(LSU rbuf))
		  (member-equal j trace) (INST-p j)
		  (or (equal (INST-stg j) '(LSU RS0))
		      (equal (INST-stg j) '(LSU RS1))))
	     (member-in-order i j trace))
  :hints (("goal" :in-theory (enable member-in-order*)))))

(local
(defthm LSU-rbuf-RS-in-order
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(LSU rbuf))
		  (INST-in j MT) (INST-p j)
		  (or (equal (INST-stg j) '(LSU RS0))
		      (equal (INST-stg j) '(LSU RS1)))
		  (MAETT-p MT) (MA-state-p MA))
	     (INST-in-order-p i j MT))
  :hints (("goal" :in-theory (enable INST-in-order-p INST-in
				     inv in-order-LSU-inst-p)))
  :rule-classes nil))

(defthm not-LSU-RS0-LMM-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (exist-LMM-before-p i addr MT)
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (not (equal (INST-stg (LMM-before i addr MT))
			 '(LSU RS0))))
  :hints (("goal" :use (:instance LSU-RBUF-RS-IN-ORDER
				  (j (LMM-before i addr MT))))))

(defthm not-LSU-RS1-LMM-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (exist-LMM-before-p i addr MT)
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (not (equal (INST-stg (LMM-before i addr MT))
			 '(LSU RS1))))
  :hints (("goal" :use (:instance LSU-RBUF-RS-IN-ORDER
				  (j (LMM-before i addr MT))))))
)

(defthm not-LSU-rbuf-LMM-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (exist-LMM-before-p i addr MT)
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (not (equal (INST-stg (LMM-before i addr MT))
			 '(LSU rbuf))))
  :hints (("goal" :cases ((b1p (INST-store? (LMM-before i addr MT)))))
	  ("subgoal 1" :in-theory (e/d (lift-b-ops equal-b1p-converter)
				       (INST-STORE-LRM-BEFORE
					LSU-LOAD-IF-AT-LSU-RBUF-LCH))
		       :use (:instance LSU-LOAD-IF-AT-LSU-RBUF-LCH
				       (i (LMM-before i addr MT))))))

(defthm not-LSU-lch-LMM-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (exist-LMM-before-p i addr MT)
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (not (equal (INST-stg (LMM-before i addr MT))
			 '(LSU lch))))
    :hints (("goal" :cases ((b1p (INST-store? (LMM-before i addr MT)))))
	  ("subgoal 1" :in-theory (e/d (lift-b-ops equal-b1p-converter)
				       (INST-STORE-LRM-BEFORE
					LSU-LOAD-IF-AT-LSU-RBUF-LCH))
		       :use (:instance LSU-LOAD-IF-AT-LSU-RBUF-LCH
				       (i (LMM-before i addr MT))))))

(defthm not-complete-normal-LMM-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (exist-LMM-before-p i addr MT)
		  (not (b1p (INST-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (not (equal (INST-stg (LMM-before i addr MT))
			 '(complete))))
  :hints (("goal" :use (:instance not-INST-store-if-complete
				  (i (LMM-before i addr MT)))
		  :in-theory (enable lift-b-ops equal-b1p-converter
				     exception-relations))))

; If i is not a memory modifier, it does not change the value of memory.
(defthm read-mem-ISA-step-if-not-mem-modifier
    (implies (and (inv MT MA)
		  (INST-in i MT) (addr-p addr) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (mem-modifier-p addr i)))
	     (equal (read-mem addr (ISA-mem (ISA-step (INST-pre-ISA i) intr)))
		    (read-mem addr (ISA-mem (INST-pre-ISA i)))))
  :hints (("goal" :in-theory (enable mem-modifier-p INST-store?
				     ISA-store-inst-p INST-store?
				     store-inst-p inst-ld-st? INST-LSU?
				     INST-opcode
				     INST-cntlv
				     lift-b-ops)
		  :use (:instance read-mem-ISA-step-if-not-ISA-store-INST-p
				  (ISA (INST-pre-ISA i))))))

(encapsulate nil
(local
 (defthm read-mem-LMM-before-help-help
     (implies (and (inv MT MA)
		   (member-equal i trace)
		   (subtrace-p trace MT)
		   (consp trace)
		   (INST-listp trace) (INST-p i)
		   (addr-p addr)
		   (not (trace-exist-LMM-before-p i addr trace))
		   (MAETT-p MT) (MA-state-p MA))
	      (equal (read-mem addr (ISA-mem (INST-pre-ISA i)))
		     (read-mem addr (ISA-mem (INST-pre-ISA (car trace))))))
   :hints  ((when-found (member-equal i (cdr trace))
		       (:cases ((consp (cdr trace))))))))

		     
(local
(defthm read-mem-LMM-before-help
    (implies (and  (inv MT MA)
		   (member-equal i trace)
		   (INST-listp trace) (INST-p i)
		   (MAETT-p MT) (MA-state-p MA)
		   (addr-p addr)
		   (subtrace-p trace MT)
		   (trace-exist-LMM-before-p i addr trace))
     (equal (read-mem addr
		      (ISA-mem
		       (INST-post-ISA (trace-LMM-before i addr trace))))
	    (read-mem addr (ISA-mem (INST-pre-ISA i)))))
   :hints ((when-found (member-equal i (cdr trace))
		       (:cases ((consp (cdr trace))))))))
		     

; This is a critical lemma.  The memory value at address addr in 
; the pre-ISA of i is the same as in the post-ISA of the last memory
; modifier.  In other words, no instruction modifies the value of the memory
; between the last memory modifier before i and i itself.
(defthm read-mem-LMM-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (addr-p addr)
		  (MAETT-p MT) (MA-state-p MA)
		  (exist-LMM-before-p i addr MT))
     (equal (read-mem addr
		      (ISA-mem (INST-post-ISA (LMM-before i addr MT))))
	    (read-mem addr (ISA-mem (INST-pre-ISA i)))))
  :hints (("goal" :in-theory (enable LMM-before
				     exist-LMM-before-p
				     INST-in)))
  :rule-classes nil)
)

;;;;;;;;;;;;;;;;End of memory modifier theory;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
