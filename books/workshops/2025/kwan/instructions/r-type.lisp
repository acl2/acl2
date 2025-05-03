(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "../operations")
(include-book "../rv-state")
(include-book "../decode")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;					      ;;
;;    Integer Register-Register Operations    ;;
;;					      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Format for RISC-V R-type operations
;;
;;   31          25 24      20 19      15 14  12 11       7 6            0
;;  |--------------|----------|----------|------|----------|--------------|
;;  |    funct7    |   rs2    |   rs1    |funct3|    rd    |    opcode    |
;;  |--------------|----------|----------|------|----------|--------------|
;;       7 bits       5 bits     5 bits   3 bits   5 bits       7 bits
;;		       src2       src1              dest          OP
;;

;;
;; Addition
;;
(define rv32-ADD ((rv32 rv32p))
 :returns (rv32 rv32p :hyp :guard)
 (b* (;; Get PC
      (PC (xpc rv32))

      ;; Memory probe
      ((if (< *2^32-5* PC))
       (!ms (list :at-location  PC
       	   :instruction  'ADD
       	   :memory-probe nil)
            rv32))

      ;; Get instr
      (instr  (rm32 PC rv32))
      ;; Decode registers from instr
      (rs1   (get-rs1 instr))
      (rs2   (get-rs2 instr))
      (rd    (get-rd  instr))

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
      (rs2-val (rgfi rs2 rv32))
       
      ;; Compute result
      (result  (n32+ rs1-val rs2-val))
       
      ;; Store result
      (rv32 (!rgfi rd result rv32))

      ;; Update PC
      (rv32 (!xpc (+ PC 4) rv32)))
     rv32))

;;
;; Subtraction
;;
(define rv32-SUB ((rv32 rv32p))
 :returns (rv32 rv32p :hyp :guard)
 (b* (;; Get PC
      (PC (xpc rv32))

      ;; Memory probe
      ((if (< *2^32-5* PC))
       (!ms (list :at-location  PC
       	   :instruction  'SUB
       	   :memory-probe nil)
            rv32))

      ;; Get instr
      (instr  (rm32 PC rv32))
      ;; Decode registers from instr
      (rs1   (get-rs1 instr))
      (rs2   (get-rs2 instr))
      (rd    (get-rd  instr))

      ;; x0 is hardwired 0, writes to it are discarded
      ;; but an exception must still be raised
      ;; See RISC-V ISA Spec, section 2.6
      ((unless (< 0 rd))
       (!ms (list :at-location PC
       	   :instruction 'SUB
       	   :destination-register-x0 t)
            rv32))

      ;; Fetch values from registers
      (rs1-val (rgfi rs1 rv32))
      (rs2-val (rgfi rs2 rv32))
       
      ;; Compute result
      (result  (n32- rs1-val rs2-val))
       
      ;; Store result
      (rv32 (!rgfi rd result rv32))

      ;; Update PC
      (rv32 (!xpc (+ PC 4) rv32)))
     rv32))

;;
;; Xor
;;
(define rv32-XOR ((rv32 rv32p))
 :returns (rv32 rv32p :hyp :guard)
 (b* (;; Get PC
      (PC (xpc rv32))

      ;; Memory probe
      ((if (< *2^32-5* PC))
       (!ms (list :at-location  PC
       	   :instruction  'XOR
       	   :memory-probe nil)
            rv32))

      ;; Get instr
      (instr  (rm32 PC rv32))
      ;; Decode registers from instr
      (rs1   (get-rs1 instr))
      (rs2   (get-rs2 instr))
      (rd    (get-rd  instr))

      ;; x0 is hardwired 0, writes to it are discarded
      ;; but an exception must still be raised
      ;; See RISC-V ISA Spec, section 2.6
      ((unless (< 0 rd))
       (!ms (list :at-location PC
       	   :instruction 'XOR
       	   :destination-register-x0 t)
            rv32))

      ;; Fetch values from registers
      (rs1-val (rgfi rs1 rv32))
      (rs2-val (rgfi rs2 rv32))
       
      ;; Compute result
      (result  (logxor rs1-val rs2-val))
       
      ;; Store result
      (rv32 (!rgfi rd result rv32))

      ;; Update PC
      (rv32 (!xpc (+ PC 4) rv32)))
     rv32))

;;
;; Or
;;
(define rv32-OR ((rv32 rv32p))
 :returns (rv32 rv32p :hyp :guard)
 (b* (;; Get PC
      (PC (xpc rv32))

      ;; Memory probe
      ((if (< *2^32-5* PC))
       (!ms (list :at-location  PC
       	   :instruction  'OR
       	   :memory-probe nil)
            rv32))

      ;; Get instr
      (instr  (rm32 PC rv32))
      ;; Decode registers from instr
      (rs1   (get-rs1 instr))
      (rs2   (get-rs2 instr))
      (rd    (get-rd  instr))

      ;; x0 is hardwired 0, writes to it are discarded
      ;; but an exception must still be raised
      ;; See RISC-V ISA Spec, section 2.6
      ((unless (< 0 rd))
       (!ms (list :at-location PC
       	   :instruction 'OR
       	   :destination-register-x0 t)
            rv32))

      ;; Fetch values from registers
      (rs1-val (rgfi rs1 rv32))
      (rs2-val (rgfi rs2 rv32))
       
      ;; Compute result
      (result  (logior rs1-val rs2-val))
       
      ;; Store result
      (rv32 (!rgfi rd result rv32))

      ;; Update PC
      (rv32 (!xpc (+ PC 4) rv32)))
     rv32))

;;
;; And
;;
(define rv32-AND ((rv32 rv32p))
 :returns (rv32 rv32p :hyp :guard)
 (b* (;; Get PC
      (PC (xpc rv32))

      ;; Memory probe
      ((if (< *2^32-5* PC))
       (!ms (list :at-location  PC
       	   :instruction  'AND
       	   :memory-probe nil)
            rv32))

      ;; Get instr
      (instr  (rm32 PC rv32))
      ;; Decode registers from instr
      (rs1   (get-rs1 instr))
      (rs2   (get-rs2 instr))
      (rd    (get-rd  instr))

      ;; x0 is hardwired 0, writes to it are discarded
      ;; but an exception must still be raised
      ;; See RISC-V ISA Spec, section 2.6
      ((unless (< 0 rd))
       (!ms (list :at-location PC
       	   :instruction 'AND
       	   :destination-register-x0 t)
            rv32))

      ;; Fetch values from registers
      (rs1-val (rgfi rs1 rv32))
      (rs2-val (rgfi rs2 rv32))
       
      ;; Compute result
      (result  (logand rs1-val rs2-val))
       
      ;; Store result
      (rv32 (!rgfi rd result rv32))

      ;; Update PC
      (rv32 (!xpc (+ PC 4) rv32)))
     rv32))

;;
;; Shift Left Logical
;;
(define rv32-SLL ((rv32 rv32p))
 :returns (rv32 rv32p :hyp :guard)
 (b* (;; Get PC
      (PC (xpc rv32))

      ;; Memory probe
      ((if (< *2^32-5* PC))
       (!ms (list :at-location  PC
       	   :instruction  'SLL
       	   :memory-probe nil)
            rv32))

      ;; Get instr
      (instr  (rm32 PC rv32))
      ;; Decode registers from instr
      (rs1   (get-rs1 instr))
      (rs2   (get-rs2 instr))
      (rd    (get-rd  instr))

      ;; x0 is hardwired 0, writes to it are discarded
      ;; but an exception must still be raised
      ;; See RISC-V ISA Spec, section 2.6
      ((unless (< 0 rd))
       (!ms (list :at-location PC
       	   :instruction 'SLL
       	   :destination-register-x0 t)
            rv32))

      ;; Fetch values from registers
      (rs1-val (rgfi rs1 rv32))
      (rs2-val (n05 (rgfi rs2 rv32)))
       
      ;; Compute result
      (result  (n32 (ash rs1-val rs2-val)))
       
      ;; Store result
      (rv32 (!rgfi rd result rv32))

      ;; Update PC
      (rv32 (!xpc (+ PC 4) rv32)))
     rv32))

;;
;; Shift Right Logical
;;
(define rv32-SRL ((rv32 rv32p))
 :returns (rv32 rv32p :hyp :guard)
 (b* (;; Get PC
      (PC (xpc rv32))

      ;; Memory probe
      ((if (< *2^32-5* PC))
       (!ms (list :at-location  PC
       	   :instruction  'SRL
       	   :memory-probe nil)
            rv32))

      ;; Get instr
      (instr  (rm32 PC rv32))
      ;; Decode registers from instr
      (rs1   (get-rs1 instr))
      (rs2   (get-rs2 instr))
      (rd    (get-rd  instr))

      ;; x0 is hardwired 0, writes to it are discarded
      ;; but an exception must still be raised
      ;; See RISC-V ISA Spec, section 2.6
      ((unless (< 0 rd))
       (!ms (list :at-location PC
       	   :instruction 'SRL
       	   :destination-register-x0 t)
            rv32))

      ;; Fetch values from registers
      (rs1-val (rgfi rs1 rv32))
      (rs2-val (n05 (rgfi rs2 rv32)))
       
      ;; Compute result
      (result  (n32 (ash rs1-val (- rs2-val))))
       
      ;; Store result
      (rv32 (!rgfi rd result rv32))

      ;; Update PC
      (rv32 (!xpc (+ PC 4) rv32)))
     rv32))

;;
;; Shift Right Arithmetic
;;
(define rv32-SRA ((rv32 rv32p))
 :returns (rv32 rv32p :hyp :guard)
 (b* (;; Get PC
      (PC (xpc rv32))

      ;; Memory probe
      ((if (< *2^32-5* PC))
       (!ms (list :at-location  PC
       	   :instruction  'SRA
       	   :memory-probe nil)
            rv32))

      ;; Get instr
      (instr  (rm32 PC rv32))
      ;; Decode registers from instr
      (rs1   (get-rs1 instr))
      (rs2   (get-rs2 instr))
      (rd    (get-rd  instr))

      ;; x0 is hardwired 0, writes to it are discarded
      ;; but an exception must still be raised
      ;; See RISC-V ISA Spec, section 2.6
      ((unless (< 0 rd))
       (!ms (list :at-location PC
       	   :instruction 'SRA
       	   :destination-register-x0 t)
            rv32))

      ;; Fetch values from registers
      (rs1-val (logext 32 (rgfi rs1 rv32)))
      (rs2-val (n05 (rgfi rs2 rv32)))
       
      ;; Compute result
      (result  (n32 (ash rs1-val (- rs2-val))))
       
      ;; Store result
      (rv32 (!rgfi rd result rv32))

      ;; Update PC
      (rv32 (!xpc (+ PC 4) rv32)))
     rv32))

;;
;; Set Less Than
;;
(define rv32-SLT ((rv32 rv32p))
 :returns (rv32 rv32p :hyp :guard)
 (b* (;; Get PC
      (PC (xpc rv32))

      ;; Memory probe
      ((if (< *2^32-5* PC))
       (!ms (list :at-location  PC
       	   :instruction  'SLT
       	   :memory-probe nil)
            rv32))

      ;; Get instr
      (instr  (rm32 PC rv32))
      ;; Decode registers from instr
      (rs1   (get-rs1 instr))
      (rs2   (get-rs2 instr))
      (rd    (get-rd  instr))

      ;; x0 is hardwired 0, writes to it are discarded
      ;; but an exception must still be raised
      ;; See RISC-V ISA Spec, section 2.6
      ((unless (< 0 rd))
       (!ms (list :at-location PC
       	   :instruction 'SLT
       	   :destination-register-x0 t)
            rv32))

      ;; Fetch values from registers
      (rs1-val (logext 32 (rgfi rs1 rv32)))
      (rs2-val (logext 32 (rgfi rs2 rv32)))
       
      ;; Compute result
      (result  (if (< rs1-val rs2-val) 1 0))
       
      ;; Store result
      (rv32 (!rgfi rd result rv32))

      ;; Update PC
      (rv32 (!xpc (+ PC 4) rv32)))
     rv32))

;;
;; Set Less Than Unsigned
;;
(define rv32-SLTU ((rv32 rv32p))
 :returns (rv32 rv32p :hyp :guard)
 (b* (;; Get PC
      (PC (xpc rv32))

      ;; Memory probe
      ((if (< *2^32-5* PC))
       (!ms (list :at-location  PC
       	   :instruction  'SLTU
       	   :memory-probe nil)
            rv32))

      ;; Get instr
      (instr  (rm32 PC rv32))
      ;; Decode registers from instr
      (rs1   (get-rs1 instr))
      (rs2   (get-rs2 instr))
      (rd    (get-rd  instr))

      ;; x0 is hardwired 0, writes to it are discarded
      ;; but an exception must still be raised
      ;; See RISC-V ISA Spec, section 2.6
      ((unless (< 0 rd))
       (!ms (list :at-location PC
       	   :instruction 'SLTU
       	   :destination-register-x0 t)
            rv32))

      ;; Fetch values from registers
      (rs1-val (rgfi rs1 rv32))
      (rs2-val (rgfi rs2 rv32))
       
      ;; Compute result
      (result  (if (< rs1-val rs2-val) 1 0))
       
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

;; Recall: R-type instruction format
;;  [ funct7 | rs2 | rs1 | funct3 | rd | op ]

(local (include-book "centaur/gl/gl" :dir :system))

(gl::def-gl-thm n05-of-n05p
  :hyp (n05p x) 
  :concl (equal (n05 x) x)
  :g-bindings (gl::auto-bindings (:nat x 5)))


;; Add disassembly / assembly theorems

;; Add constants
(defconst *add-opcode* #b00110011)
(defconst *add-funct3* #x0)
(defconst *add-funct7* #x0)

(define asm-add ((rs1 n05p) (rs2 n05p) (rd n05p))
 (mbe
  :logic (+ (ash *add-funct7* 25) 
            (ash (n05 rs2)    20)
            (ash (n05 rs1)    15)
            (ash *add-funct3* 12)
            (ash (n05 rd)      7)
                 *add-opcode*   )
  :exec (+ (ash *add-funct7* 25)
           (ash rs2          20)
           (ash rs1          15)
           (ash *add-funct3* 12)
           (ash rd            7)
           	*add-opcode*   )))

(gl::def-gl-thm n32p-of-asm-add-lemma-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (n32p (+ (ash *add-funct7* 25)
                  (ash j    20)
                  (ash i    15)
                  (ash *add-funct3* 12)
                  (ash k    7)
                  *add-opcode*))
  :g-bindings (gl::auto-bindings (:mix (:nat i 5) (:nat j 5) (:nat k 5))))

(defthm n32p-of-asm-add
  (n32p (asm-add rs1 rs2 rd))
  :hints (("Goal" :in-theory (enable asm-add)
		  :use ((:instance n32p-of-asm-add-lemma-gl (i (n05 rs1)) (j (n05 rs2)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-add-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-opcode (logand (+ 51 (ash k 7) (ash i 15) (ash j 20)) 127)) #b0110011)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct7-of-asm-add-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct7 (+ 51 (ash k 7) (ash i 15) (ash j 20))) #x0)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-add-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct3 (+ 51 (ash k 7) (ash i 15) (ash j 20))) #x0)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-opcode-of-asm-add 
  (equal (get-opcode (asm-add i j k)) #b0110011)
  :hints (("Goal" :in-theory (enable asm-add)
                  :use ((:instance get-opcode-of-asm-add-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-add 
  (equal (get-funct3 (asm-add i j k)) #x0)
  :hints (("Goal" :in-theory (enable asm-add)
                  :use ((:instance get-funct3-of-asm-add-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct7-of-asm-add 
  (equal (get-funct7 (asm-add i j k)) #x0)
  :hints (("Goal" :in-theory (enable asm-add)
                  :use ((:instance get-funct7-of-asm-add-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-add-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs1 (+ 51 (ash k 7) (ash i 15) (ash j 20))) i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs1-of-asm-add
  (equal (get-rs1 (asm-add rs1 rs2 rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-add))))

(gl::def-gl-thm get-rs2-of-asm-add-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs2 (+ 51 (ash k 7) (ash i 15) (ash j 20))) j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs2-of-asm-add
  (equal (get-rs2 (asm-add rs1 rs2 rd)) (n05 rs2))
  :hints (("Goal" :in-theory (enable asm-add))))

(gl::def-gl-thm get-rd-of-asm-add-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rd (+ 51 (ash k 7) (ash i 15) (ash j 20))) k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(local (in-theory (enable asm-add)))

(defthm get-rd-of-asm-add (equal (get-rd (asm-add rs1 rs2 rd)) (n05 rd)))

(local (in-theory (disable asm-add)))


;; Add disassembly / assembly theorems

;; SUB constants
(defconst *SUB-opcode* *ADD-opcode*)
(defconst *SUB-funct3* #x00)
(defconst *SUB-funct7* #x20)

(define asm-sub ((rs1 n05p) (rs2 n05p) (rd n05p))
 (mbe
  :logic (+ (ash *sub-funct7* 25)
            (ash (n05 rs2)    20)
            (ash (n05 rs1)    15)
            (ash *sub-funct3* 12)
            (ash (n05 rd)      7)
                 *sub-opcode*   )
  :exec (+ (ash *sub-funct7* 25)
           (ash rs2          20)
           (ash rs1          15)
           (ash *sub-funct3* 12)
           (ash rd            7)
           	*sub-opcode*   )))

(gl::def-gl-thm n32p-of-asm-sub-lemma-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (n32p (+ (ash *sub-funct7* 25)
                  (ash j    20)
                  (ash i    15)
                  (ash *sub-funct3* 12)
                  (ash k    7)
                  *sub-opcode*))
  :g-bindings (gl::auto-bindings (:mix (:nat i 5) (:nat j 5) (:nat k 5))))

(defthm n32p-of-asm-sub
  (n32p (asm-sub rs1 rs2 rd))
  :hints (("Goal" :in-theory (enable asm-sub)
		  :use ((:instance n32p-of-asm-sub-lemma-gl (i (n05 rs1)) (j (n05 rs2)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-sub-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-opcode (logand (+ 1073741875 (ash k 7) (ash i 15) (ash j 20)) 127)) #b0110011)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct7-of-asm-sub-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct7 (+ 1073741875 (ash k 7) (ash i 15) (ash j 20))) #x20)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-sub-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct3 (+ 1073741875 (ash k 7) (ash i 15) (ash j 20))) #x0)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-opcode-of-asm-sub 
  (equal (get-opcode (asm-sub i j k)) #b0110011)
  :hints (("Goal" :in-theory (enable asm-sub)
                  :use ((:instance get-opcode-of-asm-sub-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-sub 
  (equal (get-funct3 (asm-sub i j k)) #x0)
  :hints (("Goal" :in-theory (enable asm-sub)
                  :use ((:instance get-funct3-of-asm-sub-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct7-of-asm-sub 
  (equal (get-funct7 (asm-sub i j k)) #x20)
  :hints (("Goal" :in-theory (enable asm-sub)
                  :use ((:instance get-funct7-of-asm-sub-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-sub-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs1 (+ 1073741875 (ash k 7) (ash i 15) (ash j 20))) i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs1-of-asm-sub
  (equal (get-rs1 (asm-sub rs1 rs2 rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-sub))))

(gl::def-gl-thm get-rs2-of-asm-sub-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs2 (+ 1073741875 (ash k 7) (ash i 15) (ash j 20))) j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs2-of-asm-sub
  (equal (get-rs2 (asm-sub rs1 rs2 rd)) (n05 rs2))
  :hints (("Goal" :in-theory (enable asm-sub))))

(gl::def-gl-thm get-rd-of-asm-sub-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rd (+ 1073741875 (ash k 7) (ash i 15) (ash j 20))) k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rd-of-asm-sub
  (equal (get-rd (asm-sub rs1 rs2 rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-sub))))


;; Xor disassembly / assembly theorems

;; Xor constants
(defconst *xor-opcode* *add-opcode*)
(defconst *xor-funct3* #x04)
(defconst *xor-funct7* #x0)

(define asm-xor ((rs1 n05p) (rs2 n05p) (rd n05p))
 (mbe
  :logic (+ (ash *xor-funct7* 25)
            (ash (n05 rs2)    20)
            (ash (n05 rs1)    15)
            (ash *xor-funct3* 12)
            (ash (n05 rd)      7)
                 *xor-opcode*   )
  :exec (+ (ash *xor-funct7* 25)
           (ash rs2          20)
           (ash rs1          15)
           (ash *xor-funct3* 12)
           (ash rd            7)
           	*xor-opcode*   )))

(gl::def-gl-thm n32p-of-asm-xor-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (n32p (+ (ash *xor-funct7* 25)
                  (ash j    20)
                  (ash i    15)
                  (ash *xor-funct3* 12)
                  (ash k    7)
                  *xor-opcode*))
  :g-bindings (gl::auto-bindings (:mix (:nat i 5) (:nat j 5) (:nat k 5))))

(defthm n32p-of-asm-xor
  (n32p (asm-xor rs1 rs2 rd))
  :hints (("Goal" :in-theory (enable asm-xor)
		  :use ((:instance n32p-of-asm-xor-gl (i (n05 rs1)) (j (n05 rs2)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-xor-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-opcode (logand (+ 16435 (ash k 7) (ash i 15) (ash j 20)) 127)) #b0110011)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct7-of-asm-xor-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct7 (+ 16435 (ash k 7) (ash i 15) (ash j 20))) #x0)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-xor-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct3 (+ 16435 (ash k 7) (ash i 15) (ash j 20))) #x4)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-opcode-of-asm-xor
  (equal (get-opcode (asm-xor i j k)) #b0110011)
  :hints (("Goal" :in-theory (enable asm-xor)
                  :use ((:instance get-opcode-of-asm-xor-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-xor
  (equal (get-funct3 (asm-xor i j k)) #x4)
  :hints (("Goal" :in-theory (enable asm-xor)
                  :use ((:instance get-funct3-of-asm-xor-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct7-of-asm-xor
  (equal (get-funct7 (asm-xor i j k)) #x0)
  :hints (("Goal" :in-theory (enable asm-xor)
                  :use ((:instance get-funct7-of-asm-xor-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-xor-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs1 (+ 16435 (ash k 7) (ash i 15) (ash j 20))) i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs1-of-asm-xor
  (equal (get-rs1 (asm-xor rs1 rs2 rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-xor))))

(gl::def-gl-thm get-rs2-of-asm-xor-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs2 (+ 16435 (ash k 7) (ash i 15) (ash j 20))) j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs2-of-asm-xor
  (equal (get-rs2 (asm-xor rs1 rs2 rd)) (n05 rs2))
  :hints (("Goal" :in-theory (enable asm-xor ))))

(gl::def-gl-thm get-rd-of-asm-xor-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rd (+ 16435 (ash k 7) (ash i 15) (ash j 20))) k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rd-of-asm-xor
  (equal (get-rd (asm-xor rs1 rs2 rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-xor))))


;; Or disassembly / assembly theorems

;; Or constants
(defconst *or-opcode* *add-opcode*)
(defconst *or-funct3* #x06)
(defconst *or-funct7* #x0)

(define asm-or ((rs1 n05p) (rs2 n05p) (rd n05p))
 (mbe
  :logic (+ (ash *or-funct7* 25)
            (ash (n05 rs2)    20)
            (ash (n05 rs1)    15)
            (ash *or-funct3* 12)
            (ash (n05 rd)      7)
                 *or-opcode*   )
  :exec (+ (ash *or-funct7* 25)
           (ash rs2          20)
           (ash rs1          15)
           (ash *or-funct3* 12)
           (ash rd            7)
           	*or-opcode*   )))

(gl::def-gl-thm n32p-of-asm-or-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (n32p (+ (ash *or-funct7* 25)
                  (ash j    20)
                  (ash i    15)
                  (ash *or-funct3* 12)
                  (ash k    7)
                  *or-opcode*))
  :g-bindings (gl::auto-bindings (:mix (:nat i 5) (:nat j 5) (:nat k 5))))

(defthm n32p-of-asm-or
  (n32p (asm-or rs1 rs2 rd))
  :hints (("Goal" :in-theory (enable asm-or)
		  :use ((:instance n32p-of-asm-or-gl (i (n05 rs1)) (j (n05 rs2)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-or-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-opcode (logand (+ 24627 (ash k 7) (ash i 15) (ash j 20)) 127)) #b0110011)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct7-of-asm-or-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct7 (+ 24627 (ash k 7) (ash i 15) (ash j 20))) #x0)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-or-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct3 (+ 24627 (ash k 7) (ash i 15) (ash j 20))) #x6)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-opcode-of-asm-or
  (equal (get-opcode (asm-or i j k)) #b0110011)
  :hints (("Goal" :in-theory (enable asm-or)
                  :use ((:instance get-opcode-of-asm-or-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-or
  (equal (get-funct3 (asm-or i j k)) #x6)
  :hints (("Goal" :in-theory (enable asm-or)
                  :use ((:instance get-funct3-of-asm-or-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct7-of-asm-or
  (equal (get-funct7 (asm-or i j k)) #x0)
  :hints (("Goal" :in-theory (enable asm-or)
                  :use ((:instance get-funct7-of-asm-or-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-or-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs1 (+ 24627 (ash k 7) (ash i 15) (ash j 20))) i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs1-of-asm-or
  (equal (get-rs1 (asm-or rs1 rs2 rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-or))))

(gl::def-gl-thm get-rs2-of-asm-or-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs2 (+ 24627 (ash k 7) (ash i 15) (ash j 20))) j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs2-of-asm-or
  (equal (get-rs2 (asm-or rs1 rs2 rd)) (n05 rs2))
  :hints (("Goal" :in-theory (enable asm-or ))))

(gl::def-gl-thm get-rd-of-asm-or-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rd (+ 24627 (ash k 7) (ash i 15) (ash j 20))) k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rd-of-asm-or
  (equal (get-rd (asm-or rs1 rs2 rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-or))))


;; And disassembly / assembly theorems

;; And constants
(defconst *and-opcode* *add-opcode*)
(defconst *and-funct3* #x07)
(defconst *and-funct7* #x0)

(define asm-and ((rs1 n05p) (rs2 n05p) (rd n05p))
 (mbe
  :logic (+ (ash *and-funct7* 25)
            (ash (n05 rs2)    20)
            (ash (n05 rs1)    15)
            (ash *and-funct3* 12)
            (ash (n05 rd)      7)
                 *and-opcode*   )
  :exec (+ (ash *and-funct7* 25)
           (ash rs2          20)
           (ash rs1          15)
           (ash *and-funct3* 12)
           (ash rd            7)
           	*and-opcode*   )))

(gl::def-gl-thm n32p-of-asm-and-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (n32p (+ (ash *and-funct7* 25)
                  (ash j    20)
                  (ash i    15)
                  (ash *and-funct3* 12)
                  (ash k    7)
                  *and-opcode*))
  :g-bindings (gl::auto-bindings (:mix (:nat i 5) (:nat j 5) (:nat k 5))))

(defthm n32p-of-asm-and
  (n32p (asm-and rs1 rs2 rd))
  :hints (("Goal" :in-theory (enable asm-and)
		  :use ((:instance n32p-of-asm-and-gl (i (n05 rs1)) (j (n05 rs2)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-and-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-opcode (logand (+ 28723 (ash k 7) (ash i 15) (ash j 20)) 127)) #b0110011)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct7-of-asm-and-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct7 (+ 28723 (ash k 7) (ash i 15) (ash j 20))) #x0)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-and-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct3 (+ 28723 (ash k 7) (ash i 15) (ash j 20))) #x7)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-opcode-of-asm-and
  (equal (get-opcode (asm-and i j k)) #b0110011)
  :hints (("Goal" :in-theory (enable asm-and)
                  :use ((:instance get-opcode-of-asm-and-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-and
  (equal (get-funct3 (asm-and i j k)) #x7)
  :hints (("Goal" :in-theory (enable asm-and)
                  :use ((:instance get-funct3-of-asm-and-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct7-of-asm-and
  (equal (get-funct7 (asm-and i j k)) #x0)
  :hints (("Goal" :in-theory (enable asm-and)
                  :use ((:instance get-funct7-of-asm-and-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-and-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs1 (+ 28723 (ash k 7) (ash i 15) (ash j 20))) i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs1-of-asm-and
  (equal (get-rs1 (asm-and rs1 rs2 rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-and))))

(gl::def-gl-thm get-rs2-of-asm-and-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs2 (+ 28723 (ash k 7) (ash i 15) (ash j 20))) j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs2-of-asm-and
  (equal (get-rs2 (asm-and rs1 rs2 rd)) (n05 rs2))
  :hints (("Goal" :in-theory (enable asm-and ))))

(gl::def-gl-thm get-rd-of-asm-and-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rd (+ 28723 (ash k 7) (ash i 15) (ash j 20))) k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rd-of-asm-and
  (equal (get-rd (asm-and rs1 rs2 rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-and))))


;; Shift Left Logical disassembly / assembly theorems

;; Sll constants
(defconst *sll-opcode* *add-opcode*)
(defconst *sll-funct3* #x1)
(defconst *sll-funct7* #x0)

(define asm-sll ((rs1 n05p) (rs2 n05p) (rd n05p))
 (mbe
  :logic (+ (ash *sll-funct7* 25)
            (ash (n05 rs2)    20)
            (ash (n05 rs1)    15)
            (ash *sll-funct3* 12)
            (ash (n05 rd)      7)
                 *sll-opcode*   )
  :exec (+ (ash *sll-funct7* 25)
           (ash rs2          20)
           (ash rs1          15)
           (ash *sll-funct3* 12)
           (ash rd            7)
           	*sll-opcode*   )))

(gl::def-gl-thm n32p-of-asm-sll-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (n32p (+ (ash *sll-funct7* 25)
                  (ash j    20)
                  (ash i    15)
                  (ash *sll-funct3* 12)
                  (ash k    7)
                  *sll-opcode*))
  :g-bindings (gl::auto-bindings (:mix (:nat i 5) (:nat j 5) (:nat k 5))))

(defthm n32p-of-asm-sll
  (n32p (asm-sll rs1 rs2 rd))
  :hints (("Goal" :in-theory (enable asm-sll)
		  :use ((:instance n32p-of-asm-sll-gl (i (n05 rs1)) (j (n05 rs2)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-sll-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-opcode (logand (+ 4147 (ash k 7) (ash i 15) (ash j 20)) 127)) #b0110011)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct7-of-asm-sll-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct7 (+ 4147 (ash k 7) (ash i 15) (ash j 20))) #x0)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-sll-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct3 (+ 4147 (ash k 7) (ash i 15) (ash j 20))) #x1)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-opcode-of-asm-sll
  (equal (get-opcode (asm-sll i j k)) #b0110011)
  :hints (("Goal" :in-theory (enable asm-sll)
                  :use ((:instance get-opcode-of-asm-sll-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-sll
  (equal (get-funct3 (asm-sll i j k)) #x1)
  :hints (("Goal" :in-theory (enable asm-sll)
                  :use ((:instance get-funct3-of-asm-sll-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct7-of-asm-sll
  (equal (get-funct7 (asm-sll i j k)) #x0)
  :hints (("Goal" :in-theory (enable asm-sll)
                  :use ((:instance get-funct7-of-asm-sll-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-sll-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs1 (+ 4147 (ash k 7) (ash i 15) (ash j 20))) i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs1-of-asm-sll
  (equal (get-rs1 (asm-sll rs1 rs2 rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-sll))))

(gl::def-gl-thm get-rs2-of-asm-sll-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs2 (+ 4147 (ash k 7) (ash i 15) (ash j 20))) j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs2-of-asm-sll
  (equal (get-rs2 (asm-sll rs1 rs2 rd)) (n05 rs2))
  :hints (("Goal" :in-theory (enable asm-sll ))))

(gl::def-gl-thm get-rd-of-asm-sll-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rd (+ 4147 (ash k 7) (ash i 15) (ash j 20))) k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rd-of-asm-sll
  (equal (get-rd (asm-sll rs1 rs2 rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-sll))))


;; Shift Right Logical disassembly / assembly theorems

;; Shift Right Logical constants
(defconst *srl-opcode* *add-opcode*)
(defconst *srl-funct3* #x5)
(defconst *srl-funct7* #x0)

(define asm-srl ((rs1 n05p) (rs2 n05p) (rd n05p))
 (mbe
  :logic (+ (ash *srl-funct7* 25)
            (ash (n05 rs2)    20)
            (ash (n05 rs1)    15)
            (ash *srl-funct3* 12)
            (ash (n05 rd)      7)
                 *srl-opcode*   )
  :exec (+ (ash *srl-funct7* 25)
           (ash rs2          20)
           (ash rs1          15)
           (ash *srl-funct3* 12)
           (ash rd            7)
           	*srl-opcode*   )))

(gl::def-gl-thm n32p-of-asm-srl-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (n32p (+ (ash *srl-funct7* 25)
                  (ash j    20)
                  (ash i    15)
                  (ash *srl-funct3* 12)
                  (ash k    7)
                  *srl-opcode*))
  :g-bindings (gl::auto-bindings (:mix (:nat i 5) (:nat j 5) (:nat k 5))))

(defthm n32p-of-asm-srl
  (n32p (asm-srl rs1 rs2 rd))
  :hints (("Goal" :in-theory (enable asm-srl)
		  :use ((:instance n32p-of-asm-srl-gl (i (n05 rs1)) (j (n05 rs2)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-srl-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-opcode (logand (+ 20531 (ash k 7) (ash i 15) (ash j 20)) 127)) #b0110011)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct7-of-asm-srl-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct7 (+ 20531 (ash k 7) (ash i 15) (ash j 20))) #x0)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-srl-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct3 (+ 20531 (ash k 7) (ash i 15) (ash j 20))) #x5)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-opcode-of-asm-srl
  (equal (get-opcode (asm-srl i j k)) #b0110011)
  :hints (("Goal" :in-theory (enable asm-srl)
                  :use ((:instance get-opcode-of-asm-srl-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-srl
  (equal (get-funct3 (asm-srl i j k)) #x5)
  :hints (("Goal" :in-theory (enable asm-srl)
                  :use ((:instance get-funct3-of-asm-srl-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct7-of-asm-srl
  (equal (get-funct7 (asm-srl i j k)) #x0)
  :hints (("Goal" :in-theory (enable asm-srl)
                  :use ((:instance get-funct7-of-asm-srl-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-srl-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs1 (+ 20531 (ash k 7) (ash i 15) (ash j 20))) i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs1-of-asm-srl
  (equal (get-rs1 (asm-srl rs1 rs2 rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-srl))))

(gl::def-gl-thm get-rs2-of-asm-srl-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs2 (+ 20531 (ash k 7) (ash i 15) (ash j 20))) j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs2-of-asm-srl
  (equal (get-rs2 (asm-srl rs1 rs2 rd)) (n05 rs2))
  :hints (("Goal" :in-theory (enable asm-srl ))))

(gl::def-gl-thm get-rd-of-asm-srl-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rd (+ 20531 (ash k 7) (ash i 15) (ash j 20))) k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rd-of-asm-srl
  (equal (get-rd (asm-srl rs1 rs2 rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-srl))))


;; Shift Right Arithmetic disassembly / assembly theorems

;; Shift Right Arithmetic constants
(defconst *sra-opcode* *add-opcode*)
(defconst *sra-funct3* #x5)
(defconst *sra-funct7* #x20)

(define asm-sra ((rs1 n05p) (rs2 n05p) (rd n05p))
 (mbe
  :logic (+ (ash *sra-funct7* 25)
            (ash (n05 rs2)    20)
            (ash (n05 rs1)    15)
            (ash *sra-funct3* 12)
            (ash (n05 rd)      7)
                 *sra-opcode*   )
  :exec (+ (ash *sra-funct7* 25)
           (ash rs2          20)
           (ash rs1          15)
           (ash *sra-funct3* 12)
           (ash rd            7)
           	*sra-opcode*   )))

(gl::def-gl-thm n32p-of-asm-sra-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (n32p (+ (ash *sra-funct7* 25)
                  (ash j    20)
                  (ash i    15)
                  (ash *sra-funct3* 12)
                  (ash k    7)
                  *sra-opcode*))
  :g-bindings (gl::auto-bindings (:mix (:nat i 5) (:nat j 5) (:nat k 5))))

(defthm n32p-of-asm-sra
  (n32p (asm-sra rs1 rs2 rd))
  :hints (("Goal" :in-theory (enable asm-sra)
		  :use ((:instance n32p-of-asm-sra-gl (i (n05 rs1)) (j (n05 rs2)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-sra-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-opcode (logand (+ 1073762355 (ash k 7) (ash i 15) (ash j 20)) 127)) #b0110011)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct7-of-asm-sra-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct7 (+ 1073762355 (ash k 7) (ash i 15) (ash j 20))) #x20)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-sra-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct3 (+ 1073762355 (ash k 7) (ash i 15) (ash j 20))) #x5)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-opcode-of-asm-sra
  (equal (get-opcode (asm-sra i j k)) #b0110011)
  :hints (("Goal" :in-theory (enable asm-sra)
                  :use ((:instance get-opcode-of-asm-sra-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-sra
  (equal (get-funct3 (asm-sra i j k)) #x5)
  :hints (("Goal" :in-theory (enable asm-sra)
                  :use ((:instance get-funct3-of-asm-sra-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct7-of-asm-sra
  (equal (get-funct7 (asm-sra i j k)) #x20)
  :hints (("Goal" :in-theory (enable asm-sra)
                  :use ((:instance get-funct7-of-asm-sra-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-sra-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs1 (+ 1073762355 (ash k 7) (ash i 15) (ash j 20))) i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs1-of-asm-sra
  (equal (get-rs1 (asm-sra rs1 rs2 rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-sra))))

(gl::def-gl-thm get-rs2-of-asm-sra-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs2 (+ 1073762355 (ash k 7) (ash i 15) (ash j 20))) j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs2-of-asm-sra
  (equal (get-rs2 (asm-sra rs1 rs2 rd)) (n05 rs2))
  :hints (("Goal" :in-theory (enable asm-sra ))))

(gl::def-gl-thm get-rd-of-asm-sra-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rd (+ 1073762355 (ash k 7) (ash i 15) (ash j 20))) k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rd-of-asm-sra
  (equal (get-rd (asm-sra rs1 rs2 rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-sra))))


;; Set Less Than (Signed) disassembly / assembly theorems

;; Set Less Than (Signed) constants
(defconst *slt-opcode* *add-opcode*)
(defconst *slt-funct3* #x2)
(defconst *slt-funct7* #x0)

(define asm-slt ((rs1 n05p) (rs2 n05p) (rd n05p))
 (mbe
  :logic (+ (ash *slt-funct7* 25)
            (ash (n05 rs2)    20)
            (ash (n05 rs1)    15)
            (ash *slt-funct3* 12)
            (ash (n05 rd)      7)
                 *slt-opcode*   )
  :exec (+ (ash *slt-funct7* 25)
           (ash rs2          20)
           (ash rs1          15)
           (ash *slt-funct3* 12)
           (ash rd            7)
           	*slt-opcode*   )))

(gl::def-gl-thm n32p-of-asm-slt-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (n32p (+ (ash *slt-funct7* 25)
                  (ash j    20)
                  (ash i    15)
                  (ash *slt-funct3* 12)
                  (ash k    7)
                  *slt-opcode*))
  :g-bindings (gl::auto-bindings (:mix (:nat i 5) (:nat j 5) (:nat k 5))))

(defthm n32p-of-asm-slt
  (n32p (asm-slt rs1 rs2 rd))
  :hints (("Goal" :in-theory (enable asm-slt)
		  :use ((:instance n32p-of-asm-slt-gl (i (n05 rs1)) (j (n05 rs2)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-slt-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-opcode (logand (+ 8243 (ash k 7) (ash i 15) (ash j 20)) 127)) #b0110011)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct7-of-asm-slt-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct7 (+ 8243 (ash k 7) (ash i 15) (ash j 20))) #x00)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-slt-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct3 (+ 8243 (ash k 7) (ash i 15) (ash j 20))) #x2)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-opcode-of-asm-slt
  (equal (get-opcode (asm-slt i j k)) #b0110011)
  :hints (("Goal" :in-theory (enable asm-slt)
                  :use ((:instance get-opcode-of-asm-slt-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-slt
  (equal (get-funct3 (asm-slt i j k)) #x2)
  :hints (("Goal" :in-theory (enable asm-slt)
                  :use ((:instance get-funct3-of-asm-slt-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct7-of-asm-slt
  (equal (get-funct7 (asm-slt i j k)) #x00)
  :hints (("Goal" :in-theory (enable asm-slt)
                  :use ((:instance get-funct7-of-asm-slt-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-slt-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs1 (+ 8243 (ash k 7) (ash i 15) (ash j 20))) i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs1-of-asm-slt
  (equal (get-rs1 (asm-slt rs1 rs2 rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-slt))))

(gl::def-gl-thm get-rs2-of-asm-slt-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs2 (+ 8243 (ash k 7) (ash i 15) (ash j 20))) j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs2-of-asm-slt
  (equal (get-rs2 (asm-slt rs1 rs2 rd)) (n05 rs2))
  :hints (("Goal" :in-theory (enable asm-slt ))))

(gl::def-gl-thm get-rd-of-asm-slt-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rd (+ 8243 (ash k 7) (ash i 15) (ash j 20))) k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rd-of-asm-slt
  (equal (get-rd (asm-slt rs1 rs2 rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-slt))))


;; Set Less Than (unsigned) disassembly / assembly theorems

;; Set Less Than (Unsigned) constants
(defconst *sltu-opcode* *add-opcode*)
(defconst *sltu-funct3* #x3)
(defconst *sltu-funct7* #x0)

(define asm-sltu ((rs1 n05p) (rs2 n05p) (rd n05p))
 (mbe
  :logic (+ (ash *sltu-funct7* 25)
            (ash (n05 rs2)    20)
            (ash (n05 rs1)    15)
            (ash *sltu-funct3* 12)
            (ash (n05 rd)      7)
                 *sltu-opcode*   )
  :exec (+ (ash *sltu-funct7* 25)
           (ash rs2          20)
           (ash rs1          15)
           (ash *sltu-funct3* 12)
           (ash rd            7)
           	*sltu-opcode*   )))

(gl::def-gl-thm n32p-of-asm-sltu-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (n32p (+ (ash *sltu-funct7* 25)
                  (ash j    20)
                  (ash i    15)
                  (ash *sltu-funct3* 12)
                  (ash k    7)
                  *sltu-opcode*))
  :g-bindings (gl::auto-bindings (:mix (:nat i 5) (:nat j 5) (:nat k 5))))

(defthm n32p-of-asm-sltu
  (n32p (asm-sltu rs1 rs2 rd))
  :hints (("Goal" :in-theory (enable asm-sltu)
		  :use ((:instance n32p-of-asm-sltu-gl (i (n05 rs1)) (j (n05 rs2)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-sltu-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-opcode (logand (+ 12339 (ash k 7) (ash i 15) (ash j 20)) 127)) #b0110011)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct7-of-asm-sltu-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct7 (+ 12339 (ash k 7) (ash i 15) (ash j 20))) #x00)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-sltu-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct3 (+ 12339 (ash k 7) (ash i 15) (ash j 20))) #x3)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-opcode-of-asm-sltu
  (equal (get-opcode (asm-sltu i j k)) #b0110011)
  :hints (("Goal" :in-theory (enable asm-sltu)
                  :use ((:instance get-opcode-of-asm-sltu-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-sltu
  (equal (get-funct3 (asm-sltu i j k)) #x3)
  :hints (("Goal" :in-theory (enable asm-sltu)
                  :use ((:instance get-funct3-of-asm-sltu-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct7-of-asm-sltu
  (equal (get-funct7 (asm-sltu i j k)) #x00)
  :hints (("Goal" :in-theory (enable asm-sltu)
                  :use ((:instance get-funct7-of-asm-sltu-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-sltu-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs1 (+ 12339 (ash k 7) (ash i 15) (ash j 20))) i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs1-of-asm-sltu
  (equal (get-rs1 (asm-sltu rs1 rs2 rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-sltu))))

(gl::def-gl-thm get-rs2-of-asm-sltu-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs2 (+ 12339 (ash k 7) (ash i 15) (ash j 20))) j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs2-of-asm-sltu
  (equal (get-rs2 (asm-sltu rs1 rs2 rd)) (n05 rs2))
  :hints (("Goal" :in-theory (enable asm-sltu ))))

(gl::def-gl-thm get-rd-of-asm-sltu-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rd (+ 12339 (ash k 7) (ash i 15) (ash j 20))) k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rd-of-asm-sltu
  (equal (get-rd (asm-sltu rs1 rs2 rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-sltu))))
