(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
;(include-book "centaur/gl/gl" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "../operations")
(include-book "../rv-state")
(include-book "../decode")

(defthm n12p-implies-n32p
  (implies (n12p x) (n32p x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;					       ;;
;;    Integer Register-Immediate Operations    ;;
;;					       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Format for RISC-V I-type operations
;;
;;   31                     20 19      15 14  12 11       7 6            0
;;  |-------------------------|----------|------|----------|--------------|
;;  |        imm[11:0]        |   rs1    |funct3|    rd    |    opcode    |
;;  |-------------------------|----------|------|----------|--------------|
;;            12 bits            5 bits   3 bits   5 bits       7 bits
;;	 I-immediate[11:0]        src1              dest          OP
;;

;;
;; ADDI
;;
;; Note: sign-extends imm to 32-bits
(define rv32-ADDI ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (xpc rv32))
       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'ADDI
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1   instr))
       (imm   (logext 12 (get-i-imm instr)))
       (rd    (get-rd    instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'ADD
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n32+ rs1-val imm))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!xpc (+ PC 4) rv32)))
      rv32))

;;
;; SUBI
;;
;; Note: There is no SUBI instruction
#|
(define rv32-SUBI ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (xpc rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'SUBI
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1 instr))
       (imm   (get-i-imm instr))
       (rd    (get-rd  instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'SUBI
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n32- rs1-val imm))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!xpc (+ PC 4) rv32)))
      rv32))
|#

;;
;; XORI
;;
;; Note: sign extends imm
(define rv32-XORI ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (xpc rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'XORI
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1 instr))
       (imm   (logext 12 (get-i-imm instr)))
       (rd    (get-rd  instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'XORI
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n32 (logxor rs1-val imm)))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!xpc (+ PC 4) rv32)))
      rv32))

;;
;; ORI
;;
;; Note: sign extends imm
(define rv32-ORI ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (xpc rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'ORI
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1 instr))
       (imm   (logext 12 (get-i-imm instr)))
       (rd    (get-rd  instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'ORI
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n32 (logior rs1-val imm)))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!xpc (+ PC 4) rv32)))
      rv32))

;;
;; ANDI
;;
;; Sign extends imm
(define rv32-ANDI ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (xpc rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'ANDI
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1 instr))
       (imm   (logext 12 (get-i-imm instr)))
       (rd    (get-rd  instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'ANDI
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n32 (logand rs1-val imm)))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!xpc (+ PC 4) rv32)))
      rv32))

;;
;; Shift Left Logical Immediate
;;
(define rv32-SLLI ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (xpc rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'SLLI
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1 instr))
       (imm   (n05 (get-i-imm instr)))
       (rd    (get-rd  instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'SLLI
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n32 (ash rs1-val imm)))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!xpc (+ PC 4) rv32)))
      rv32))

;;
;; Shift Right Logical Immediate
;;
(define rv32-SRLI ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (xpc rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'SRLI
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1 instr))
       (imm   (n05 (get-i-imm instr)))
       (rd    (get-rd  instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'SRLI
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n32 (ash rs1-val (- imm))))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!xpc (+ PC 4) rv32)))
      rv32))

;;
;; Shift Right Arithmetic Immediate
;;
(define rv32-SRAI ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (xpc rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'SRAI
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1 instr))
       (imm   (n05 (get-i-imm instr)))
       (rd    (get-rd  instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'SRAI
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (logext 32 (rgfi rs1 rv32)))
	
       ;; Compute result
       (result  (n32 (ash rs1-val (- imm))))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!xpc (+ PC 4) rv32)))
      rv32))

;;
;; Set Less Than Immediate
;;
;; Sign extends imm
(define rv32-SLTI ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (xpc rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'SLTI
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1 instr))
       (imm   (logext 12 (get-i-imm instr)))
       (rd    (get-rd  instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'SLTI
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (if (< rs1-val imm) 1 0))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!xpc (+ PC 4) rv32)))
      rv32))

;;
;; Set Less Than Immediate Unsigned
;;
;; Note: sign extends imm but treats it as unsigned when comparing to rs1-val
(define rv32-SLTIU ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (xpc rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'SLTIU
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1 instr))
       (imm   (n32 (logext 12 (get-i-imm instr))))
       (rd    (get-rd  instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'SLTIU
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (if (< rs1-val imm) 1 0))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!xpc (+ PC 4) rv32)))
      rv32))

;;
;; Load Byte
;; 
;;  ld = m[rs1 + imm][0:7]
(define rv32-LB ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (xpc rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'lb
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1   instr))
       (imm   (logext 12 (get-i-imm instr)))
       (rd    (get-rd    instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'LB
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n32 (logext 8 (rm08 (n32+ rs1-val imm) rv32))))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!xpc (+ PC 4) rv32)))
      rv32))

;;
;; Load Half
;; 
;;  ld = m[rs1 + imm][0:15]
(define rv32-LH ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (xpc rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'lb
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1   instr))
       (imm   (logext 12 (get-i-imm instr)))
       (rd    (get-rd    instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'LH
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n32 (logext 16 (n16 (rm32 (n32+ rs1-val imm) rv32)))))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!xpc (+ PC 4) rv32)))
      rv32))

;;
;; Load Word
;; 
;;  ld = m[rs1 + imm][0:15]
(define rv32-LW ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (xpc rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'lw
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1   instr))
       (imm   (logext 12 (get-i-imm instr)))
       (rd    (get-rd    instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'Lw
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n32 (logext 32 (rm32 (n32+ rs1-val imm) rv32))))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!xpc (+ PC 4) rv32)))
      rv32))

;;
;; Load Byte Unsigned
;; 
;;  ld = m[rs1 + imm][0:7]

;; Lemma for proving return types of LBU and LHU
(defthm n32p-of-n08p
  (implies (n08p x) (n32p x)))

(define rv32-LBU ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (xpc rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'lbu
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1   instr))
       (imm   (logext 12 (get-i-imm instr)))
       (rd    (get-rd    instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'LBU
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (rm08 (n32+ rs1-val imm) rv32))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!xpc (+ PC 4) rv32)))
      rv32))

;;
;; Load Half Unsigned
;; 
;;  ld = m[rs1 + imm][0:16]
(define rv32-LHU ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (xpc rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'lhu
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1   instr))
       (imm   (logext 12 (get-i-imm instr)))
       (rd    (get-rd    instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'LhU
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n16 (rm32 (n32+ rs1-val imm) rv32)))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!xpc (+ PC 4) rv32)))
      rv32))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;			   ;;
;;    Assembly Functions   ;;
;;			   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "centaur/gl/gl" :dir :system)

(gl::def-gl-thm n05-of-n05p
  :hyp (n05p x) 
  :concl (equal (n05 x) x)
  :g-bindings (gl::auto-bindings (:nat x 5)))

(gl::def-gl-thm n12-of-n12
  :hyp (n12p x) 
  :concl (equal (n12 x) x)
  :g-bindings (gl::auto-bindings (:nat x 12)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ADDI Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ADDi constants
(defconst *addi-opcode* #b00010011)
(defconst *addi-funct3* #x0)

(define asm-addi ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *addi-funct3* 12)
            (ash (n05 rd)       7)
                 *addi-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *addi-funct3* 12)
           (ash rd             7)
           	*addi-opcode*   )))

(gl::def-gl-thm n32p-of-asm-addi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *addi-funct3* 12)
                  (ash k    7)
                  *addi-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-addi
  (n32p (asm-addi rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-addi)
		  :use ((:instance n32p-of-asm-addi-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-addi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *addi-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *addi-opcode* )
				    127)) 
		*addi-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-addi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *addi-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *addi-opcode* ))
			
		*addi-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))


(gl::def-gl-thm get-i-imm-of-asm-addi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *addi-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *addi-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-addi
  (equal (get-opcode (asm-addi i j k)) *addi-opcode*)
  :hints (("Goal" :in-theory (enable asm-addi)
                  :use ((:instance get-opcode-of-asm-addi-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-addi 
  (equal (get-funct3 (asm-addi i j k)) *addi-funct3*)
  :hints (("Goal" :in-theory (enable asm-addi)
                  :use ((:instance get-funct3-of-asm-addi-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-addi
  (equal (get-i-imm (asm-addi i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-addi)
                  :use ((:instance get-i-imm-of-asm-addi-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-addi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *addi-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *addi-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-addi
  (equal (get-rs1 (asm-addi rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-addi)
		  :use ((:instance get-rs1-of-asm-addi-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-addi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *addi-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *addi-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-addi
  (equal (get-rd (asm-addi rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-addi)
		  :use ((:instance get-rd-of-asm-addi-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; XORI Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; XORI constants
(defconst *xori-opcode* *addi-opcode*)
(defconst *xori-funct3* #x4)

(define asm-xori ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *xori-funct3* 12)
            (ash (n05 rd)       7)
                 *xori-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *xori-funct3* 12)
           (ash rd             7)
           	*xori-opcode*   )))

(gl::def-gl-thm n32p-of-asm-xori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *xori-funct3* 12)
                  (ash k    7)
                  *xori-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-xori
  (n32p (asm-xori rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-xori)
		  :use ((:instance n32p-of-asm-xori-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-xori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *xori-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *xori-opcode* )
				    127)) 
		*xori-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-xori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *xori-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *xori-opcode* ))
			
		*xori-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))


(gl::def-gl-thm get-i-imm-of-asm-xori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *xori-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *xori-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-xori
  (equal (get-opcode (asm-xori i j k)) *xori-opcode*)
  :hints (("Goal" :in-theory (enable asm-xori)
                  :use ((:instance get-opcode-of-asm-xori-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-xori 
  (equal (get-funct3 (asm-xori i j k)) *xori-funct3*)
  :hints (("Goal" :in-theory (enable asm-xori)
                  :use ((:instance get-funct3-of-asm-xori-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-xori
  (equal (get-i-imm (asm-xori i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-xori)
                  :use ((:instance get-i-imm-of-asm-xori-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-xori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *xori-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *xori-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-xori
  (equal (get-rs1 (asm-xori rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-xori)
		  :use ((:instance get-rs1-of-asm-xori-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-xori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *xori-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *xori-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-xori
  (equal (get-rd (asm-xori rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-xori)
		  :use ((:instance get-rd-of-asm-xori-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ORI Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; XORI constants
(defconst *ori-opcode* *addi-opcode*)
(defconst *ori-funct3* #x6)

(define asm-ori ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *ori-funct3* 12)
            (ash (n05 rd)       7)
                 *ori-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *ori-funct3* 12)
           (ash rd             7)
           	*ori-opcode*   )))

(gl::def-gl-thm n32p-of-asm-ori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *ori-funct3* 12)
                  (ash k    7)
                  *ori-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-ori
  (n32p (asm-ori rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-ori)
		  :use ((:instance n32p-of-asm-ori-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-ori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *ori-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *ori-opcode* )
				    127)) 
		*ori-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-ori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *ori-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *ori-opcode* ))
			
		*ori-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-i-imm-of-asm-ori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *ori-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *ori-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-ori
  (equal (get-opcode (asm-ori i j k)) *ori-opcode*)
  :hints (("Goal" :in-theory (enable asm-ori)
                  :use ((:instance get-opcode-of-asm-ori-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-ori 
  (equal (get-funct3 (asm-ori i j k)) *ori-funct3*)
  :hints (("Goal" :in-theory (enable asm-ori)
                  :use ((:instance get-funct3-of-asm-ori-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-ori
  (equal (get-i-imm (asm-ori i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-ori)
                  :use ((:instance get-i-imm-of-asm-ori-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-ori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *ori-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *ori-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-ori
  (equal (get-rs1 (asm-ori rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-ori)
		  :use ((:instance get-rs1-of-asm-ori-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-ori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *ori-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *ori-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-ori
  (equal (get-rd (asm-ori rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-ori)
		  :use ((:instance get-rd-of-asm-ori-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ANDI Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ANDI constants
(defconst *andi-opcode* *addi-opcode*)
(defconst *andi-funct3* #x7)

(define asm-andi ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *andi-funct3* 12)
            (ash (n05 rd)       7)
                 *andi-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *andi-funct3* 12)
           (ash rd             7)
           	*andi-opcode*   )))

(gl::def-gl-thm n32p-of-asm-andi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *andi-funct3* 12)
                  (ash k    7)
                  *andi-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-andi
  (n32p (asm-andi rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-andi)
		  :use ((:instance n32p-of-asm-andi-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-andi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *andi-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *andi-opcode* )
				    127)) 
		*andi-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-andi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *andi-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *andi-opcode* ))
			
		*andi-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-i-imm-of-asm-andi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *andi-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *andi-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-andi
  (equal (get-opcode (asm-andi i j k)) *andi-opcode*)
  :hints (("Goal" :in-theory (enable asm-andi)
                  :use ((:instance get-opcode-of-asm-andi-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-andi 
  (equal (get-funct3 (asm-andi i j k)) *andi-funct3*)
  :hints (("Goal" :in-theory (enable asm-andi)
                  :use ((:instance get-funct3-of-asm-andi-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-andi
  (equal (get-i-imm (asm-andi i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-andi)
                  :use ((:instance get-i-imm-of-asm-andi-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-andi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *andi-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *andi-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-andi
  (equal (get-rs1 (asm-andi rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-andi)
		  :use ((:instance get-rs1-of-asm-andi-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-andi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *andi-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *andi-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-andi
  (equal (get-rd (asm-andi rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-andi)
		  :use ((:instance get-rd-of-asm-andi-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; SLLI Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; SLLI constants
(defconst *slli-opcode* *addi-opcode*)
(defconst *slli-funct3* #x1)

(define asm-slli ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *slli-funct3* 12)
            (ash (n05 rd)       7)
                 *slli-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *slli-funct3* 12)
           (ash rd             7)
           	*slli-opcode*   )))

(gl::def-gl-thm n32p-of-asm-slli-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *slli-funct3* 12)
                  (ash k    7)
                  *slli-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-slli
  (n32p (asm-slli rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-slli)
		  :use ((:instance n32p-of-asm-slli-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-slli-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *slli-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *slli-opcode* )
				    127)) 
		*slli-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-slli-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *slli-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *slli-opcode* ))
			
		*slli-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))


(gl::def-gl-thm get-i-imm-of-asm-slli-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *slli-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *slli-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-slli
  (equal (get-opcode (asm-slli i j k)) *slli-opcode*)
  :hints (("Goal" :in-theory (enable asm-slli)
                  :use ((:instance get-opcode-of-asm-slli-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-slli 
  (equal (get-funct3 (asm-slli i j k)) *slli-funct3*)
  :hints (("Goal" :in-theory (enable asm-slli)
                  :use ((:instance get-funct3-of-asm-slli-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-slli
  (equal (get-i-imm (asm-slli i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-slli)
                  :use ((:instance get-i-imm-of-asm-slli-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-slli-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *slli-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *slli-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-slli
  (equal (get-rs1 (asm-slli rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-slli)
		  :use ((:instance get-rs1-of-asm-slli-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-slli-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *slli-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *slli-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-slli
  (equal (get-rd (asm-slli rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-slli)
		  :use ((:instance get-rd-of-asm-slli-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; SRLI Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; SRLI constants
(defconst *srli-opcode* *addi-opcode*)
(defconst *srli-funct3* #x5)
(defconst *srli-funct7* #x0)

(define asm-srli ((rs1 n05p) (imm n05p) (rd n05p))
 (mbe
  :logic (+ (ash (n05 imm)     20)
            (ash (n05 rs1)     15)
            (ash *srli-funct3* 12)
            (ash (n05 rd)       7)
                 *srli-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *srli-funct3* 12)
           (ash rd             7)
           	*srli-opcode*   )))

(gl::def-gl-thm n32p-of-asm-srli-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *srli-funct3* 12)
                  (ash k    7)
                  *srli-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-srli
  (n32p (asm-srli rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-srli)
		  :use ((:instance n32p-of-asm-srli-gl (i (n05 rs1)) (j (n05 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-srli-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *srli-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *srli-opcode* )
				    127)) 
		*srli-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-srli-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *srli-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *srli-opcode* ))
			
		*srli-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-i-imm-of-asm-srli-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *srli-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *srli-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-srli
  (equal (get-opcode (asm-srli i j k)) *srli-opcode*)
  :hints (("Goal" :in-theory (enable asm-srli)
                  :use ((:instance get-opcode-of-asm-srli-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-srli 
  (equal (get-funct3 (asm-srli i j k)) *srli-funct3*)
  :hints (("Goal" :in-theory (enable asm-srli)
                  :use ((:instance get-funct3-of-asm-srli-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-srli
  (equal (get-i-imm (asm-srli i j k)) (n05 j))
  :hints (("Goal" :in-theory (enable asm-srli)
                  :use ((:instance get-i-imm-of-asm-srli-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-srli-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *srli-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *srli-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-srli
  (equal (get-rs1 (asm-srli rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-srli)
		  :use ((:instance get-rs1-of-asm-srli-gl (i (n05 rs1)) (j (n05 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-srli-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *srli-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *srli-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-srli
  (equal (get-rd (asm-srli rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-srli)
		  :use ((:instance get-rd-of-asm-srli-gl (i (n05 rs1)) (j (n05 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-funct7-of-asm-srli-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct7 (+ (ash j 20)
			     (ash *srli-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *srli-opcode* ))
		*srli-funct7*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-funct7-of-asm-srli
  (equal (get-funct7 (asm-srli rs1 imm rd)) *srli-funct7*)
  :hints (("Goal" :in-theory (enable asm-srli)
		  :use ((:instance get-funct7-of-asm-srli-gl (i (n05 rs1)) (j (n05 imm)) (k (n05 rd)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; SRAI Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; SRAI constants
(defconst *srai-opcode* *addi-opcode*)
(defconst *srai-funct3* #x5)
(defconst *srai-funct7* #x20)

(define asm-srai ((rs1 n05p) (imm n05p) (rd n05p))
 (mbe
  :logic (+ (ash *srai-funct7* 25) 
	    (ash (n05 imm)     20)
            (ash (n05 rs1)     15)
            (ash *srai-funct3* 12)
            (ash (n05 rd)       7)
                 *srai-opcode*   )
  :exec (+ (ash imm           20)
           (ash *srai-funct7* 25) 
           (ash rs1           15)
           (ash *srai-funct3* 12)
           (ash rd             7)
           	*srai-opcode*   )))

(gl::def-gl-thm n32p-of-asm-srai-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (n32p (+ (ash *srai-funct7* 25) 
		  (ash j    20)
                  (ash i    15)
                  (ash *srai-funct3* 12)
                  (ash k    7)
                  *srai-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-srai
  (n32p (asm-srai rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-srai)
		  :use ((:instance n32p-of-asm-srai-gl (i (n05 rs1)) (j (n05 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-srai-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash *srai-funct7* 25) 
					(ash j 20)
				       (ash *srai-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *srai-opcode* )
				    127)) 
		*srai-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-srai-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct3 (+  (ash *srai-funct7* 25) (ash j 20)
				       (ash *srai-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *srai-opcode* ))
			
		*srai-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-i-imm-of-asm-srai-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (n05 (get-i-imm  (+ (ash *srai-funct7* 25) 
			       (ash j 20)
				       (ash *srai-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *srai-opcode* )))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-srai
  (equal (get-opcode (asm-srai i j k)) *srai-opcode*)
  :hints (("Goal" :in-theory (enable asm-srai)
                  :use ((:instance get-opcode-of-asm-srai-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-srai 
  (equal (get-funct3 (asm-srai i j k)) *srai-funct3*)
  :hints (("Goal" :in-theory (enable asm-srai)
                  :use ((:instance get-funct3-of-asm-srai-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-srai
  (equal (n05 (get-i-imm (asm-srai i j k))) (n05 j))
  :hints (("Goal" :in-theory (enable asm-srai)
                  :use ((:instance get-i-imm-of-asm-srai-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-srai-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash *srai-funct7* 25)
			     (ash j 20)
			     (ash *srai-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *srai-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-srai
  (equal (get-rs1 (asm-srai rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-srai)
		  :use ((:instance get-rs1-of-asm-srai-gl (i (n05 rs1)) (j (n05 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-srai-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rd (+   (ash *srai-funct7* 25)
			     (ash j 20)
			     (ash *srai-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *srai-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-srai
  (equal (get-rd (asm-srai rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-srai)
		  :use ((:instance get-rd-of-asm-srai-gl (i (n05 rs1)) (j (n05 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-funct7-of-asm-srai-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct7 (+ (ash *srai-funct7* 25)
				(ash j 20)
			     (ash *srai-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *srai-opcode* ))
		*srai-funct7*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-funct7-of-asm-srai
  (equal (get-funct7 (asm-srai rs1 imm rd)) *srai-funct7*)
  :hints (("Goal" :in-theory (enable asm-srai)
		  :use ((:instance get-funct7-of-asm-srai-gl (i (n05 rs1)) (j (n05 imm)) (k (n05 rd)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; SLTI Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; SLTI constants
(defconst *slti-opcode* *addi-opcode*)
(defconst *slti-funct3* #x2)

(define asm-slti ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *slti-funct3* 12)
            (ash (n05 rd)       7)
                 *slti-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *slti-funct3* 12)
           (ash rd             7)
           	*slti-opcode*   )))

(gl::def-gl-thm n32p-of-asm-slti-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *slti-funct3* 12)
                  (ash k    7)
                  *slti-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-slti
  (n32p (asm-slti rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-slti)
		  :use ((:instance n32p-of-asm-slti-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-slti-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *slti-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *slti-opcode* )
				    127)) 
		*slti-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-slti-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *slti-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *slti-opcode* ))
			
		*slti-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))


(gl::def-gl-thm get-i-imm-of-asm-slti-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *slti-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *slti-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-slti
  (equal (get-opcode (asm-slti i j k)) *slti-opcode*)
  :hints (("Goal" :in-theory (enable asm-slti)
                  :use ((:instance get-opcode-of-asm-slti-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-slti 
  (equal (get-funct3 (asm-slti i j k)) *slti-funct3*)
  :hints (("Goal" :in-theory (enable asm-slti)
                  :use ((:instance get-funct3-of-asm-slti-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-slti
  (equal (get-i-imm (asm-slti i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-slti)
                  :use ((:instance get-i-imm-of-asm-slti-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-slti-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *slti-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *slti-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-slti
  (equal (get-rs1 (asm-slti rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-slti)
		  :use ((:instance get-rs1-of-asm-slti-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-slti-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *slti-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *slti-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-slti
  (equal (get-rd (asm-slti rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-slti)
		  :use ((:instance get-rd-of-asm-slti-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; SLTIU Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; SLTIU constants
(defconst *sltiu-opcode* *addi-opcode*)
(defconst *sltiu-funct3* #x3)

(define asm-sltiu ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *sltiu-funct3* 12)
            (ash (n05 rd)       7)
                 *sltiu-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *sltiu-funct3* 12)
           (ash rd             7)
           	*sltiu-opcode*   )))

(gl::def-gl-thm n32p-of-asm-sltiu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *sltiu-funct3* 12)
                  (ash k    7)
                  *sltiu-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-sltiu
  (n32p (asm-sltiu rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-sltiu)
		  :use ((:instance n32p-of-asm-sltiu-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-sltiu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *sltiu-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *sltiu-opcode* )
				    127)) 
		*sltiu-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-sltiu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *sltiu-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *sltiu-opcode* ))
			
		*sltiu-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-i-imm-of-asm-sltiu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *sltiu-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *sltiu-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-sltiu
  (equal (get-opcode (asm-sltiu i j k)) *sltiu-opcode*)
  :hints (("Goal" :in-theory (enable asm-sltiu)
                  :use ((:instance get-opcode-of-asm-sltiu-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-sltiu 
  (equal (get-funct3 (asm-sltiu i j k)) *sltiu-funct3*)
  :hints (("Goal" :in-theory (enable asm-sltiu)
                  :use ((:instance get-funct3-of-asm-sltiu-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-sltiu
  (equal (get-i-imm (asm-sltiu i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-sltiu)
                  :use ((:instance get-i-imm-of-asm-sltiu-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-sltiu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *sltiu-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *sltiu-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-sltiu
  (equal (get-rs1 (asm-sltiu rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-sltiu)
		  :use ((:instance get-rs1-of-asm-sltiu-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-sltiu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *sltiu-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *sltiu-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-sltiu
  (equal (get-rd (asm-sltiu rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-sltiu)
		  :use ((:instance get-rd-of-asm-sltiu-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; LB Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; LB constants
(defconst *lb-opcode* #b11)
(defconst *lb-funct3* 0)

(define asm-lb ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *lb-funct3* 12)
            (ash (n05 rd)       7)
                 *lb-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *lb-funct3* 12)
           (ash rd             7)
           	*lb-opcode*   )))

(gl::def-gl-thm n32p-of-asm-lb-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *lb-funct3* 12)
                  (ash k    7)
                  *lb-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-lb
  (n32p (asm-lb rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-lb)
		  :use ((:instance n32p-of-asm-lb-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-lb-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *lb-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lb-opcode* )
				    127)) 
		*lb-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-lb-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *lb-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lb-opcode* ))
			
		*lb-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))


(gl::def-gl-thm get-i-imm-of-asm-lb-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *lb-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lb-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-lb
  (equal (get-opcode (asm-lb i j k)) *lb-opcode*)
  :hints (("Goal" :in-theory (enable asm-lb)
                  :use ((:instance get-opcode-of-asm-lb-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-lb 
  (equal (get-funct3 (asm-lb i j k)) *lb-funct3*)
  :hints (("Goal" :in-theory (enable asm-lb)
                  :use ((:instance get-funct3-of-asm-lb-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-lb
  (equal (get-i-imm (asm-lb i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-lb)
                  :use ((:instance get-i-imm-of-asm-lb-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-lb-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *lb-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *lb-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-lb
  (equal (get-rs1 (asm-lb rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-lb)
		  :use ((:instance get-rs1-of-asm-lb-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-lb-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *lb-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *lb-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-lb
  (equal (get-rd (asm-lb rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-lb)
		  :use ((:instance get-rd-of-asm-lb-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; LH Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; LH constants
(defconst *lh-opcode* #b11)
(defconst *lh-funct3* #x1)

(define asm-lh ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *lh-funct3* 12)
            (ash (n05 rd)       7)
                 *lh-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *lh-funct3* 12)
           (ash rd             7)
           	*lh-opcode*   )))

(gl::def-gl-thm n32p-of-asm-lh-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *lh-funct3* 12)
                  (ash k    7)
                  *lh-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-lh
  (n32p (asm-lh rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-lh)
		  :use ((:instance n32p-of-asm-lh-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-lh-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *lh-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lh-opcode* )
				    127)) 
		*lh-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-lh-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *lh-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lh-opcode* ))
			
		*lh-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-i-imm-of-asm-lh-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *lh-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lh-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-lh
  (equal (get-opcode (asm-lh i j k)) *lh-opcode*)
  :hints (("Goal" :in-theory (enable asm-lh)
                  :use ((:instance get-opcode-of-asm-lh-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-lh 
  (equal (get-funct3 (asm-lh i j k)) *lh-funct3*)
  :hints (("Goal" :in-theory (enable asm-lh)
                  :use ((:instance get-funct3-of-asm-lh-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-lh
  (equal (get-i-imm (asm-lh i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-lh)
                  :use ((:instance get-i-imm-of-asm-lh-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-lh-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *lh-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *lh-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-lh
  (equal (get-rs1 (asm-lh rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-lh)
		  :use ((:instance get-rs1-of-asm-lh-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-lh-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *lh-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *lh-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-lh
  (equal (get-rd (asm-lh rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-lh)
		  :use ((:instance get-rd-of-asm-lh-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; LW Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; LW constants
(defconst *lw-opcode* #b11)
(defconst *lw-funct3* #x2)

(define asm-lw ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *lw-funct3* 12)
            (ash (n05 rd)       7)
                 *lw-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *lw-funct3* 12)
           (ash rd             7)
           	*lw-opcode*   )))

(gl::def-gl-thm n32p-of-asm-lw-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *lw-funct3* 12)
                  (ash k    7)
                  *lw-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-lw
  (n32p (asm-lw rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-lw)
		  :use ((:instance n32p-of-asm-lw-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-lw-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *lw-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lw-opcode* )
				    127)) 
		*lw-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-lw-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *lw-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lw-opcode* ))
			
		*lw-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-i-imm-of-asm-lw-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *lw-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lw-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-lw
  (equal (get-opcode (asm-lw i j k)) *lw-opcode*)
  :hints (("Goal" :in-theory (enable asm-lw)
                  :use ((:instance get-opcode-of-asm-lw-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-lw 
  (equal (get-funct3 (asm-lw i j k)) *lw-funct3*)
  :hints (("Goal" :in-theory (enable asm-lw)
                  :use ((:instance get-funct3-of-asm-lw-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-lw
  (equal (get-i-imm (asm-lw i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-lw)
                  :use ((:instance get-i-imm-of-asm-lw-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-lw-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *lw-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *lw-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-lw
  (equal (get-rs1 (asm-lw rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-lw)
		  :use ((:instance get-rs1-of-asm-lw-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-lw-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *lw-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *lw-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-lw
  (equal (get-rd (asm-lw rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-lw)
		  :use ((:instance get-rd-of-asm-lw-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; LBU Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; LBU constants
(defconst *lbu-opcode* #b11)
(defconst *lbu-funct3* #x4)

(define asm-lbu ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *lbu-funct3* 12)
            (ash (n05 rd)       7)
                 *lbu-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *lbu-funct3* 12)
           (ash rd             7)
           	*lbu-opcode*   )))

(gl::def-gl-thm n32p-of-asm-lbu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *lbu-funct3* 12)
                  (ash k    7)
                  *lbu-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-lbu
  (n32p (asm-lbu rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-lbu)
		  :use ((:instance n32p-of-asm-lbu-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-lbu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *lbu-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lbu-opcode* )
				    127)) 
		*lbu-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-lbu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *lbu-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lbu-opcode* ))
			
		*lbu-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))


(gl::def-gl-thm get-i-imm-of-asm-lbu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *lbu-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lbu-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-lbu
  (equal (get-opcode (asm-lbu i j k)) *lbu-opcode*)
  :hints (("Goal" :in-theory (enable asm-lbu)
                  :use ((:instance get-opcode-of-asm-lbu-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-lbu 
  (equal (get-funct3 (asm-lbu i j k)) *lbu-funct3*)
  :hints (("Goal" :in-theory (enable asm-lbu)
                  :use ((:instance get-funct3-of-asm-lbu-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-lbu
  (equal (get-i-imm (asm-lbu i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-lbu)
                  :use ((:instance get-i-imm-of-asm-lbu-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-lbu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *lbu-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *lbu-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-lbu
  (equal (get-rs1 (asm-lbu rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-lbu)
		  :use ((:instance get-rs1-of-asm-lbu-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-lbu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *lbu-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *lbu-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-lbu
  (equal (get-rd (asm-lbu rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-lbu)
		  :use ((:instance get-rd-of-asm-lbu-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; LHU Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; LHU constants
(defconst *lhu-opcode* #b11)
(defconst *lhu-funct3* #x5)

(define asm-lhu ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *lhu-funct3* 12)
            (ash (n05 rd)       7)
                 *lhu-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *lhu-funct3* 12)
           (ash rd             7)
           	*lhu-opcode*   )))

(gl::def-gl-thm n32p-of-asm-lhu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *lhu-funct3* 12)
                  (ash k    7)
                  *lhu-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-lhu
  (n32p (asm-lhu rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-lhu)
		  :use ((:instance n32p-of-asm-lhu-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-lhu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *lhu-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lhu-opcode* )
				    127)) 
		*lhu-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-lhu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *lhu-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lhu-opcode* ))
			
		*lhu-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-i-imm-of-asm-lhu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *lhu-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lhu-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-lhu
  (equal (get-opcode (asm-lhu i j k)) *lhu-opcode*)
  :hints (("Goal" :in-theory (enable asm-lhu)
                  :use ((:instance get-opcode-of-asm-lhu-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-lhu 
  (equal (get-funct3 (asm-lhu i j k)) *lhu-funct3*)
  :hints (("Goal" :in-theory (enable asm-lhu)
                  :use ((:instance get-funct3-of-asm-lhu-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-lhu
  (equal (get-i-imm (asm-lhu i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-lhu)
                  :use ((:instance get-i-imm-of-asm-lhu-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-lhu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *lhu-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *lhu-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-lhu
  (equal (get-rs1 (asm-lhu rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-lhu)
		  :use ((:instance get-rs1-of-asm-lhu-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-lhu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *lhu-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *lhu-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-lhu
  (equal (get-rd (asm-lhu rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-lhu)
		  :use ((:instance get-rd-of-asm-lhu-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))
