(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "../operations")
(include-book "../rv-state")
(include-book "../decode")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;			   ;;
;;    Branch Operations    ;;
;;			   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Format for RISC-V B-type operations
;;
;;   31        25 24        20 19      15 14  12 11       7 6            0
;;  |------------|------------|----------|------|----------|--------------|
;;  |imm[12|10:5]|    rs2     |   rs1    |funct3|im[4:1|11]|    opcode    |
;;  |------------|------------|----------|------|----------|--------------|
;;      7 bits       5 bits      5 bits   3 bits   5 bits       7 bits
;;	              src2        src1                            OP
;;

;;
;; Branch if equal
;; 
;;  PC = rs1==rs2 ? PC+imm : PC
(local
  (defthm guard-lemma
    (n08p (n08 x))))
(define rv32-BEQ ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  :guard-hints (("Goal" :in-theory (disable logext)))
  (b* (;; Get PC
       (PC (xpc rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1   instr))
       (rs2   (get-rs2   instr))
       (imm   (logext 13 (get-b-imm instr)))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
       (rs2-val (rgfi rs2 rv32))

       ;; Compute new PC
       (PC (if (equal rs1-val rs2-val) (+ PC imm) (+ PC 4)))

       ;; Memory probe -- check if 
       ((if (not (n32p PC)))
	(!ms (list :at-location  PC
		   :instruction  'beq
		   :memory-probe nil)
	     rv32))
	
       ;; Update PC
       (rv32 (!xpc PC rv32)))
      rv32))


;;
;; Branch if not equal
;;
(define rv32-BNE ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  :guard-hints (("Goal" :in-theory (disable logext)))
  (b* (;; Get PC
       (PC (xpc rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1   instr))
       (rs2   (get-rs2   instr))
       (imm   (logext 13 (get-b-imm instr)))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
       (rs2-val (rgfi rs2 rv32))

       ;; Compute new PC
       (PC (if (not (equal rs1-val rs2-val)) (+ PC imm) (+ PC 4)))

       ;; Memory probe -- check if 
       ((if (not (n32p PC)))
	(!ms (list :at-location  PC
		   :instruction  'bne
		   :memory-probe nil)
	     rv32))
	
       ;; Update PC
       (rv32 (!xpc PC rv32)))
      rv32))

;;
;; Branch Less Than
;;
(define rv32-BLT ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  :guard-hints (("Goal" :in-theory (disable logext)))
  (b* (((unless (rv32p rv32))
	(!ms (list :instruction 'blt
		   :rv32p	nil)
	     rv32))
       ;; Get PC
       (PC (xpc rv32))
       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'blt
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1   instr))
       (rs2   (get-rs2   instr))
       (imm   (logext 13 (get-b-imm instr)))

       ;; Fetch values from registers
       (rs1-val (logext 32 (rgfi rs1 rv32)))
       (rs2-val (logext 32 (rgfi rs2 rv32)))

       ;; Compute new PC
       (PC (if (< rs1-val rs2-val) (+ PC imm) (+ PC 4)))

       ;; Memory probe -- check if 
       ((if (not (n32p PC)))
	(!ms (list :at-location  PC
		   :instruction  'blt
		   :memory-probe nil)
	     rv32))
	
       ;; Update PC
       (rv32 (!xpc PC rv32)))
      rv32))

;; 
;; Branch Greater than or Equal
;;
(define rv32-BGE ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  :guard-hints (("Goal" :in-theory (disable logext)))
  (b* (;; Get PC
       (PC (xpc rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1   instr))
       (rs2   (get-rs2   instr))
       (imm   (logext 13 (get-b-imm instr)))

       ;; Fetch values from registers
       (rs1-val (logext 32 (rgfi rs1 rv32)))
       (rs2-val (logext 32 (rgfi rs2 rv32)))

       ;; Compute new PC
       (PC (if (>= rs1-val rs2-val) (+ PC imm) (+ PC 4)))

       ;; Memory probe -- check if 
       ((if (not (n32p PC)))
	(!ms (list :at-location  PC
		   :instruction  'bge
		   :memory-probe nil)
	     rv32))
	
       ;; Update PC
       (rv32 (!xpc PC rv32)))
      rv32))

;;
;; Branch Less Than (Unsigned)
;;
(define rv32-BLTU ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  :guard-hints (("Goal" :in-theory (disable logext)))
  (b* (((unless (rv32p rv32))
	(!ms (list :instruction 'bltu
		   :rv32p	nil)
	     rv32))
       ;; Get PC
       (PC (xpc rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1   instr))
       (rs2   (get-rs2   instr))
       (imm   (logext 13 (get-b-imm instr)))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
       (rs2-val (rgfi rs2 rv32))

       ;; Compute new PC
       (PC (if (< rs1-val rs2-val) (+ PC imm) (+ PC 4)))

       ;; Memory probe -- check if 
       ((if (not (n32p PC)))
	(!ms (list :at-location  PC
		   :instruction  'bltu
		   :memory-probe nil)
	     rv32))
	
       ;; Update PC
       (rv32 (!xpc PC rv32)))
      rv32))

;;
;; Branch Greater than or Equal (Unsigned)
;;
(define rv32-BGEU ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  :guard-hints (("Goal" :in-theory (disable logext)))
  (b* (;; Get PC
       (PC (xpc rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1   instr))
       (rs2   (get-rs2   instr))
       (imm   (logext 13 (get-b-imm instr)))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
       (rs2-val (rgfi rs2 rv32))

       ;; Compute new PC
       (PC (if (>= rs1-val rs2-val) (+ PC imm) (+ PC 4)))

       ;; Memory probe -- check if 
       ((if (not (n32p PC)))
	(!ms (list :at-location  PC
		   :instruction  'bgeu
		   :memory-probe nil)
	     rv32))
       (rv32 (!xpc PC rv32)))
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

(gl::def-gl-thm n12-of-nl2
  :hyp (n12p x) 
  :concl (equal (n12 x) x)
  :g-bindings (gl::auto-bindings (:nat x 12)))

(gl::def-gl-thm n07p-of-n07
  :hyp (n07p x) 
  :concl (equal (n07 x) x)
  :g-bindings (gl::auto-bindings (:nat x 7)))

(gl::def-gl-thm get-s-imm-lemma
 :hyp (n12p imm)
 :concl (equal (+ (ash (n07 (ash imm -5)) 5)
		       (n05      imm  ))
		imm)
 :g-bindings (gl::auto-bindings (:nat imm 12)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; BEQ Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; BEQ constants
(defconst *beq-opcode* #b1100011)
(defconst *beq-funct3* 0)

(define asm-beq ((rs1 n05p) (rs2 n05p) (imm n13p))
      (+ (ash (n01 (ash imm -12)) 31)
	 (ash (n06 (ash imm -5 )) 25)
         (ash (n05      rs2     ) 20)
         (ash (n05      rs1     ) 15)
         (ash *beq-funct3*        12)
         (ash (n04 (ash imm -1 ))  8)
         (ash (n01 (ash imm -11))  7)
              *beq-opcode*         ))

(gl::def-gl-thm n32p-of-asm-beq-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (n32p (+ (ash k12          31)
	          (ash k10-5        25)
                  (ash j            20)
                  (ash i            15)
                  (ash *beq-funct3* 12)
                  (ash k4-1          8)
                  (ash k11           7)
                       *beq-opcode*   ))
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm n32p-of-asm-beq
  (n32p (asm-beq rs1 rs2 imm))
  :hints (("Goal" :in-theory (enable asm-beq)
		  :use ((:instance n32p-of-asm-beq-gl (i     (n05 rs1)) 
						      (j     (n05 rs2))
						      (k12   (n01 (ash imm -12)))
						      (k11   (n01 (ash imm -11)))
						      (k10-5 (n06 (ash imm -5 )))
						      (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-opcode-of-asm-beq-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-opcode (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *beq-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *beq-opcode*   ))
		*beq-opcode*)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-opcode-of-asm-beq
  (equal (get-opcode (asm-beq rs1 rs2 imm)) *beq-opcode*)
  :hints (("Goal" :in-theory (enable asm-beq)
       		  :use ((:instance get-opcode-of-asm-beq-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-funct3-of-asm-beq-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-funct3 (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *beq-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *beq-opcode*   ))
		*beq-funct3*)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-funct3-of-asm-beq
  (equal (get-funct3 (asm-beq rs1 rs2 imm)) *beq-funct3*)
  :hints (("Goal" :in-theory (enable asm-beq)
       		  :use ((:instance get-funct3-of-asm-beq-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-rs1-of-asm-beq-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-rs1 (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *beq-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *beq-opcode*   ))
		i)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-rs1-of-asm-beq
  (equal (get-rs1 (asm-beq rs1 rs2 imm)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-beq)
       		  :use ((:instance get-rs1-of-asm-beq-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-rs2-of-asm-beq-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-rs2 (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *beq-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *beq-opcode*   ))
		j)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-rs2-of-asm-beq
  (equal (get-rs2 (asm-beq rs1 rs2 imm)) (n05 rs2))
  :hints (("Goal" :in-theory (enable asm-beq)
       		  :use ((:instance get-rs2-of-asm-beq-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-b-imm-of-asm-beq-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-b-imm (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *beq-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *beq-opcode*   ))
		(n13 (+ (ash k12   12)
		        (ash k11   11)
		        (ash k10-5  5)
		        (ash k4-1   1))))
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(gl::def-gl-thm get-b-imm-asm-beq-gl-2
 :hyp 	   (and (zerop (n01 imm)) (n13p imm) (n05p i) (n05p j))
 :concl    (equal (get-b-imm (+ (ash (n01 (ash imm -12)) 31)
 	                        (ash (n06 (ash imm -5 )) 25)
                                (ash j            20)
                                (ash i            15)
                                (ash *beq-funct3* 12)
                                (ash (n04 (ash imm -1 ))  8)
                                (ash (n01 (ash imm -11))  7)
                                     *beq-opcode*   ))
 		  imm)
   :g-bindings (gl::auto-bindings (:nat i     5) 
 				 (:nat j     5)
 			         (:nat imm  13)))

(defthm n13p-of-n13
  (n13p (n13 x)))

(defthm get-b-imm-of-asm-beq
  (implies (and (zerop (n01 imm)) (n13p imm))
	   (equal (get-b-imm (asm-beq rs1 rs2 imm)) imm))
  :hints (("Goal" :in-theory (enable asm-beq)
       		  :use ((:instance get-b-imm-asm-beq-gl-2 (i (n05 rs1)) (j (n05 rs2)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; BNE Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; BNE constants
(defconst *bne-opcode* #b1100011)
(defconst *bne-funct3* #x1)

(define asm-bne ((rs1 n05p) (rs2 n05p) (imm n13p))
      (+ (ash (n01 (ash imm -12)) 31)
	 (ash (n06 (ash imm -5 )) 25)
         (ash (n05      rs2     ) 20)
         (ash (n05      rs1     ) 15)
         (ash *bne-funct3*        12)
         (ash (n04 (ash imm -1 ))  8)
         (ash (n01 (ash imm -11))  7)
              *bne-opcode*         ))

(gl::def-gl-thm n32p-of-asm-bne-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (n32p (+ (ash k12          31)
	          (ash k10-5        25)
                  (ash j            20)
                  (ash i            15)
                  (ash *bne-funct3* 12)
                  (ash k4-1          8)
                  (ash k11           7)
                       *bne-opcode*   ))
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm n32p-of-asm-bne
  (n32p (asm-bne rs1 rs2 imm))
  :hints (("Goal" :in-theory (enable asm-bne)
		  :use ((:instance n32p-of-asm-bne-gl (i     (n05 rs1)) 
						      (j     (n05 rs2))
						      (k12   (n01 (ash imm -12)))
						      (k11   (n01 (ash imm -11)))
						      (k10-5 (n06 (ash imm -5 )))
						      (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-opcode-of-asm-bne-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-opcode (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *bne-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *bne-opcode*   ))
		*bne-opcode*)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-opcode-of-asm-bne
  (equal (get-opcode (asm-bne rs1 rs2 imm)) *bne-opcode*)
  :hints (("Goal" :in-theory (enable asm-bne)
       		  :use ((:instance get-opcode-of-asm-bne-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-funct3-of-asm-bne-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-funct3 (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *bne-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *bne-opcode*   ))
		*bne-funct3*)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-funct3-of-asm-bne
  (equal (get-funct3 (asm-bne rs1 rs2 imm)) *bne-funct3*)
  :hints (("Goal" :in-theory (enable asm-bne)
       		  :use ((:instance get-funct3-of-asm-bne-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-rs1-of-asm-bne-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-rs1 (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *bne-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *bne-opcode*   ))
		i)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-rs1-of-asm-bne
  (equal (get-rs1 (asm-bne rs1 rs2 imm)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-bne)
       		  :use ((:instance get-rs1-of-asm-bne-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-rs2-of-asm-bne-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-rs2 (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *bne-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *bne-opcode*   ))
		j)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-rs2-of-asm-bne
  (equal (get-rs2 (asm-bne rs1 rs2 imm)) (n05 rs2))
  :hints (("Goal" :in-theory (enable asm-bne)
       		  :use ((:instance get-rs2-of-asm-bne-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-b-imm-asm-bne-gl
 :hyp 	   (and (zerop (n01 imm)) (n13p imm) (n05p i) (n05p j))
 :concl    (equal (get-b-imm (+ (ash (n01 (ash imm -12)) 31)
 	                        (ash (n06 (ash imm -5 )) 25)
                                (ash j            20)
                                (ash i            15)
                                (ash *bne-funct3* 12)
                                (ash (n04 (ash imm -1 ))  8)
                                (ash (n01 (ash imm -11))  7)
                                     *bne-opcode*   ))
 		  imm)
   :g-bindings (gl::auto-bindings (:nat i     5) 
 				 (:nat j     5)
 			         (:nat imm  13)))

(defthm get-b-imm-of-asm-bne
  (implies (and (zerop (n01 imm)) (n13p imm))
	   (equal (get-b-imm (asm-bne rs1 rs2 imm)) imm))
  :hints (("Goal" :in-theory (enable asm-bne)
       		  :use ((:instance get-b-imm-asm-bne-gl (i (n05 rs1)) (j (n05 rs2)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; BLT Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; BNE constants
(defconst *blt-opcode* #b1100011)
(defconst *blt-funct3* #x4)

(define asm-blt ((rs1 n05p) (rs2 n05p) (imm n13p))
      (+ (ash (n01 (ash imm -12)) 31)
	 (ash (n06 (ash imm -5 )) 25)
         (ash (n05      rs2     ) 20)
         (ash (n05      rs1     ) 15)
         (ash *blt-funct3*        12)
         (ash (n04 (ash imm -1 ))  8)
         (ash (n01 (ash imm -11))  7)
              *blt-opcode*         ))

(gl::def-gl-thm n32p-of-asm-blt-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (n32p (+ (ash k12          31)
	          (ash k10-5        25)
                  (ash j            20)
                  (ash i            15)
                  (ash *blt-funct3* 12)
                  (ash k4-1          8)
                  (ash k11           7)
                       *blt-opcode*   ))
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm n32p-of-asm-blt
  (n32p (asm-blt rs1 rs2 imm))
  :hints (("Goal" :in-theory (enable asm-blt)
		  :use ((:instance n32p-of-asm-blt-gl (i     (n05 rs1)) 
						      (j     (n05 rs2))
						      (k12   (n01 (ash imm -12)))
						      (k11   (n01 (ash imm -11)))
						      (k10-5 (n06 (ash imm -5 )))
						      (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-opcode-of-asm-blt-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-opcode (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *blt-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *blt-opcode*   ))
		*blt-opcode*)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-opcode-of-asm-blt
  (equal (get-opcode (asm-blt rs1 rs2 imm)) *blt-opcode*)
  :hints (("Goal" :in-theory (enable asm-blt)
       		  :use ((:instance get-opcode-of-asm-blt-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-funct3-of-asm-blt-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-funct3 (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *blt-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *blt-opcode*   ))
		*blt-funct3*)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-funct3-of-asm-blt
  (equal (get-funct3 (asm-blt rs1 rs2 imm)) *blt-funct3*)
  :hints (("Goal" :in-theory (enable asm-blt)
       		  :use ((:instance get-funct3-of-asm-blt-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-rs1-of-asm-blt-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-rs1 (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *blt-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *blt-opcode*   ))
		i)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-rs1-of-asm-blt
  (equal (get-rs1 (asm-blt rs1 rs2 imm)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-blt)
       		  :use ((:instance get-rs1-of-asm-blt-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-rs2-of-asm-blt-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-rs2 (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *blt-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *blt-opcode*   ))
		j)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-rs2-of-asm-blt
  (equal (get-rs2 (asm-blt rs1 rs2 imm)) (n05 rs2))
  :hints (("Goal" :in-theory (enable asm-blt)
       		  :use ((:instance get-rs2-of-asm-blt-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-b-imm-asm-blt-gl
 :hyp 	   (and (zerop (n01 imm)) (n13p imm) (n05p i) (n05p j))
 :concl    (equal (get-b-imm (+ (ash (n01 (ash imm -12)) 31)
 	                        (ash (n06 (ash imm -5 )) 25)
                                (ash j            20)
                                (ash i            15)
                                (ash *blt-funct3* 12)
                                (ash (n04 (ash imm -1 ))  8)
                                (ash (n01 (ash imm -11))  7)
                                     *blt-opcode*   ))
 		  imm)
   :g-bindings (gl::auto-bindings (:nat i     5) 
 				 (:nat j     5)
 			         (:nat imm  13)))

(defthm get-b-imm-of-asm-blt
  (implies (and (zerop (n01 imm)) (n13p imm))
	   (equal (get-b-imm (asm-blt rs1 rs2 imm)) imm))
  :hints (("Goal" :in-theory (enable asm-blt)
       		  :use ((:instance get-b-imm-asm-blt-gl (i (n05 rs1)) (j (n05 rs2)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; BGE Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; BGE constants
(defconst *bge-opcode* #b1100011)
(defconst *bge-funct3* #x5)

(define asm-bge ((rs1 n05p) (rs2 n05p) (imm n13p))
      (+ (ash (n01 (ash imm -12)) 31)
	 (ash (n06 (ash imm -5 )) 25)
         (ash (n05      rs2     ) 20)
         (ash (n05      rs1     ) 15)
         (ash *bge-funct3*        12)
         (ash (n04 (ash imm -1 ))  8)
         (ash (n01 (ash imm -11))  7)
              *bge-opcode*         ))

(gl::def-gl-thm n32p-of-asm-bge-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (n32p (+ (ash k12          31)
	          (ash k10-5        25)
                  (ash j            20)
                  (ash i            15)
                  (ash *bge-funct3* 12)
                  (ash k4-1          8)
                  (ash k11           7)
                       *bge-opcode*   ))
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm n32p-of-asm-bge
  (n32p (asm-bge rs1 rs2 imm))
  :hints (("Goal" :in-theory (enable asm-bge)
		  :use ((:instance n32p-of-asm-bge-gl (i     (n05 rs1)) 
						      (j     (n05 rs2))
						      (k12   (n01 (ash imm -12)))
						      (k11   (n01 (ash imm -11)))
						      (k10-5 (n06 (ash imm -5 )))
						      (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-opcode-of-asm-bge-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-opcode (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *bge-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *bge-opcode*   ))
		*bge-opcode*)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-opcode-of-asm-bge
  (equal (get-opcode (asm-bge rs1 rs2 imm)) *bge-opcode*)
  :hints (("Goal" :in-theory (enable asm-bge)
       		  :use ((:instance get-opcode-of-asm-bge-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-funct3-of-asm-bge-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-funct3 (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *bge-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *bge-opcode*   ))
		*bge-funct3*)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-funct3-of-asm-bge
  (equal (get-funct3 (asm-bge rs1 rs2 imm)) *bge-funct3*)
  :hints (("Goal" :in-theory (enable asm-bge)
       		  :use ((:instance get-funct3-of-asm-bge-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-rs1-of-asm-bge-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-rs1 (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *bge-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *bge-opcode*   ))
		i)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-rs1-of-asm-bge
  (equal (get-rs1 (asm-bge rs1 rs2 imm)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-bge)
       		  :use ((:instance get-rs1-of-asm-bge-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-rs2-of-asm-bge-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-rs2 (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *bge-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *bge-opcode*   ))
		j)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-rs2-of-asm-bge
  (equal (get-rs2 (asm-bge rs1 rs2 imm)) (n05 rs2))
  :hints (("Goal" :in-theory (enable asm-bge)
       		  :use ((:instance get-rs2-of-asm-bge-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-b-imm-asm-bge-gl
 :hyp 	   (and (zerop (n01 imm)) (n13p imm) (n05p i) (n05p j))
 :concl    (equal (get-b-imm (+ (ash (n01 (ash imm -12)) 31)
 	                        (ash (n06 (ash imm -5 )) 25)
                                (ash j            20)
                                (ash i            15)
                                (ash *bge-funct3* 12)
                                (ash (n04 (ash imm -1 ))  8)
                                (ash (n01 (ash imm -11))  7)
                                     *bge-opcode*   ))
 		  imm)
   :g-bindings (gl::auto-bindings (:nat i     5) 
 				 (:nat j     5)
 			         (:nat imm  13)))

(defthm get-b-imm-of-asm-bge
  (implies (and (zerop (n01 imm)) (n13p imm))
	   (equal (get-b-imm (asm-bge rs1 rs2 imm)) imm))
  :hints (("Goal" :in-theory (enable asm-bge)
       		  :use ((:instance get-b-imm-asm-bge-gl (i (n05 rs1)) (j (n05 rs2)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; BLTU Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; BLTU constants
(defconst *bltu-opcode* #b1100011)
(defconst *bltu-funct3* #x6)

(define asm-bltu ((rs1 n05p) (rs2 n05p) (imm n13p))
      (+ (ash (n01 (ash imm -12)) 31)
	 (ash (n06 (ash imm -5 )) 25)
         (ash (n05      rs2     ) 20)
         (ash (n05      rs1     ) 15)
         (ash *bltu-funct3*        12)
         (ash (n04 (ash imm -1 ))  8)
         (ash (n01 (ash imm -11))  7)
              *bltu-opcode*         ))

(gl::def-gl-thm n32p-of-asm-bltu-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (n32p (+ (ash k12          31)
	          (ash k10-5        25)
                  (ash j            20)
                  (ash i            15)
                  (ash *bltu-funct3* 12)
                  (ash k4-1          8)
                  (ash k11           7)
                       *bltu-opcode*   ))
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm n32p-of-asm-bltu
  (n32p (asm-bltu rs1 rs2 imm))
  :hints (("Goal" :in-theory (enable asm-bltu)
		  :use ((:instance n32p-of-asm-bltu-gl (i     (n05 rs1)) 
						      (j     (n05 rs2))
						      (k12   (n01 (ash imm -12)))
						      (k11   (n01 (ash imm -11)))
						      (k10-5 (n06 (ash imm -5 )))
						      (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-opcode-of-asm-bltu-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-opcode (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *bltu-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *bltu-opcode*   ))
		*bltu-opcode*)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-opcode-of-asm-bltu
  (equal (get-opcode (asm-bltu rs1 rs2 imm)) *bltu-opcode*)
  :hints (("Goal" :in-theory (enable asm-bltu)
       		  :use ((:instance get-opcode-of-asm-bltu-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-funct3-of-asm-bltu-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-funct3 (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *bltu-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *bltu-opcode*   ))
		*bltu-funct3*)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-funct3-of-asm-bltu
  (equal (get-funct3 (asm-bltu rs1 rs2 imm)) *bltu-funct3*)
  :hints (("Goal" :in-theory (enable asm-bltu)
       		  :use ((:instance get-funct3-of-asm-bltu-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-rs1-of-asm-bltu-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-rs1 (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *bltu-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *bltu-opcode*   ))
		i)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-rs1-of-asm-bltu
  (equal (get-rs1 (asm-bltu rs1 rs2 imm)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-bltu)
       		  :use ((:instance get-rs1-of-asm-bltu-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-rs2-of-asm-bltu-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-rs2 (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *bltu-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *bltu-opcode*   ))
		j)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-rs2-of-asm-bltu
  (equal (get-rs2 (asm-bltu rs1 rs2 imm)) (n05 rs2))
  :hints (("Goal" :in-theory (enable asm-bltu)
       		  :use ((:instance get-rs2-of-asm-bltu-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-b-imm-asm-bltu-gl
 :hyp 	   (and (zerop (n01 imm)) (n13p imm) (n05p i) (n05p j))
 :concl    (equal (get-b-imm (+ (ash (n01 (ash imm -12)) 31)
 	                        (ash (n06 (ash imm -5 )) 25)
                                (ash j            20)
                                (ash i            15)
                                (ash *bltu-funct3* 12)
                                (ash (n04 (ash imm -1 ))  8)
                                (ash (n01 (ash imm -11))  7)
                                     *bltu-opcode*   ))
 		  imm)
   :g-bindings (gl::auto-bindings (:nat i     5) 
 				 (:nat j     5)
 			         (:nat imm  13)))

(defthm get-b-imm-of-asm-bltu
  (implies (and (zerop (n01 imm)) (n13p imm))
	   (equal (get-b-imm (asm-bltu rs1 rs2 imm)) imm))
  :hints (("Goal" :in-theory (enable asm-bltu)
       		  :use ((:instance get-b-imm-asm-bltu-gl (i (n05 rs1)) (j (n05 rs2)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; BGEU Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; BGEU constants
(defconst *bgeu-opcode* #b1100011)
(defconst *bgeu-funct3* #x7)

(define asm-bgeu ((rs1 n05p) (rs2 n05p) (imm n13p))
      (+ (ash (n01 (ash imm -12)) 31)
	 (ash (n06 (ash imm -5 )) 25)
         (ash (n05      rs2     ) 20)
         (ash (n05      rs1     ) 15)
         (ash *bgeu-funct3*        12)
         (ash (n04 (ash imm -1 ))  8)
         (ash (n01 (ash imm -11))  7)
              *bgeu-opcode*         ))

(gl::def-gl-thm n32p-of-asm-bgeu-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (n32p (+ (ash k12          31)
	          (ash k10-5        25)
                  (ash j            20)
                  (ash i            15)
                  (ash *bgeu-funct3* 12)
                  (ash k4-1          8)
                  (ash k11           7)
                       *bgeu-opcode*   ))
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm n32p-of-asm-bgeu
  (n32p (asm-bgeu rs1 rs2 imm))
  :hints (("Goal" :in-theory (enable asm-bgeu)
		  :use ((:instance n32p-of-asm-bgeu-gl (i     (n05 rs1)) 
						      (j     (n05 rs2))
						      (k12   (n01 (ash imm -12)))
						      (k11   (n01 (ash imm -11)))
						      (k10-5 (n06 (ash imm -5 )))
						      (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-opcode-of-asm-bgeu-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-opcode (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *bgeu-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *bgeu-opcode*   ))
		*bgeu-opcode*)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-opcode-of-asm-bgeu
  (equal (get-opcode (asm-bgeu rs1 rs2 imm)) *bgeu-opcode*)
  :hints (("Goal" :in-theory (enable asm-bgeu)
       		  :use ((:instance get-opcode-of-asm-bgeu-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-funct3-of-asm-bgeu-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-funct3 (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *bgeu-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *bgeu-opcode*   ))
		*bgeu-funct3*)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-funct3-of-asm-bgeu
  (equal (get-funct3 (asm-bgeu rs1 rs2 imm)) *bgeu-funct3*)
  :hints (("Goal" :in-theory (enable asm-bgeu)
       		  :use ((:instance get-funct3-of-asm-bgeu-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-rs1-of-asm-bgeu-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-rs1 (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *bgeu-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *bgeu-opcode*   ))
		i)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-rs1-of-asm-bgeu
  (equal (get-rs1 (asm-bgeu rs1 rs2 imm)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-bgeu)
       		  :use ((:instance get-rs1-of-asm-bgeu-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-rs2-of-asm-bgeu-gl
  :hyp (and (n05p i) (n05p j) (n01p k12) (n01p k11) (n04p k4-1) (n06p k10-5))
  :concl (equal (get-rs2 (+ (ash k12          31)
	                       (ash k10-5        25)
                               (ash j            20)
                               (ash i            15)
                               (ash *bgeu-funct3* 12)
                               (ash k4-1          8)
                               (ash k11           7)
                                    *bgeu-opcode*   ))
		j)
  :g-bindings (gl::auto-bindings (:nat i     5) 
				 (:nat j     5)
			         (:nat k12   1)
			         (:nat k11   1)
			         (:nat k10-5 6)
			         (:nat k4-1  4)))

(defthm get-rs2-of-asm-bgeu
  (equal (get-rs2 (asm-bgeu rs1 rs2 imm)) (n05 rs2))
  :hints (("Goal" :in-theory (enable asm-bgeu)
       		  :use ((:instance get-rs2-of-asm-bgeu-gl (i     (n05 rs1)) 
						            (j     (n05 rs2))
						            (k12   (n01 (ash imm -12)))
						            (k11   (n01 (ash imm -11)))
						            (k10-5 (n06 (ash imm -5 )))
						            (k4-1  (n04 (ash imm -1 ))))))))

(gl::def-gl-thm get-b-imm-asm-bgeu-gl
 :hyp 	   (and (zerop (n01 imm)) (n13p imm) (n05p i) (n05p j))
 :concl    (equal (get-b-imm (+ (ash (n01 (ash imm -12)) 31)
 	                        (ash (n06 (ash imm -5 )) 25)
                                (ash j            20)
                                (ash i            15)
                                (ash *bgeu-funct3* 12)
                                (ash (n04 (ash imm -1 ))  8)
                                (ash (n01 (ash imm -11))  7)
                                     *bgeu-opcode*   ))
 		  imm)
   :g-bindings (gl::auto-bindings (:nat i     5) 
 				 (:nat j     5)
 			         (:nat imm  13)))

(defthm get-b-imm-of-asm-bgeu
  (implies (and (zerop (n01 imm)) (n13p imm))
	   (equal (get-b-imm (asm-bgeu rs1 rs2 imm)) imm))
  :hints (("Goal" :in-theory (enable asm-bgeu)
       		  :use ((:instance get-b-imm-asm-bgeu-gl (i (n05 rs1)) (j (n05 rs2)))))))
