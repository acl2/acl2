(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "../operations")
(include-book "../rv-state")
(include-book "../decode")

;; Note: Techinically, JAL is J-type and JALR is I-type
;; TODO: Move JALR to i-type.lisp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;		                  ;;
;;    Jump And Link Operations    ;;
;;			          ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; JAL Jump and Link
;; rd = PC + 4
;; PC = PC + imm
(define rv32-jal ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (xpc rv32))
       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rd    (get-rd    instr))
       (imm   (logext 21 (get-j-imm instr)))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but no exeption raised for JAL instr. Plain unconditional jumps 
       ;; assembler pseudoinstruction J) are encoded as JAL with rd=x0
       ;; See RISC-V ISA Spec, section 2.5.1
       ;; Update register
       (rv32 (if (zerop rd)
		 rv32
		 (!rgfi rd (n32+ PC 4) rv32)))

       ;; Compute new PC
       (PC (+ PC imm))
       ;; Memory probe
       ((if (not (n32p PC)))
	(!ms (list :at-location  PC
		   :instruction  'auipc
		   :memory-probe nil)
	     rv32))

       ;; TODO: JAL should return an instruction-misaligned exception if the
       ;;       target address is not aligned to a four-byte boundary

       ;; Update PC
       (rv32 (!xpc PC rv32)))
      rv32))


;; JALR Jump and Link Register
;; rd = PC + 4
;; PC = rs1 + imm
(define rv32-JALR ((rv32 rv32p))
 :returns (rv32 rv32p :hyp :guard)
 (b* (;; Get PC
      (PC (xpc rv32))
      ;; Get instr
      (instr   (rm32 PC rv32))
      ;; Decode registers from instr
      (rs1     (get-rs1              instr))
      (rd      (get-rd               instr))
      (imm     (logext 12 (get-i-imm instr)))
      ;; Load register value
      (rs1-val (rgfi rs1 rv32))

      ;; x0 is hardwired 0, writes to it are discarded
      ;; but no exeption raised for JAL instr. Plain unconditional jumps 
      ;; assembler pseudoinstruction J are encoded as JAL with rd=x0
      ;; See RISC-V ISA Spec, section 2.5.1
      ;; Update register
      (rv32 (if (zerop rd)
       	 rv32
       	 (!rgfi rd (n32+ PC 4) rv32)))

      ;; Compute new PC
      (PC (+ rs1-val imm))
      ;; Memory probe
      ((if (not (n32p PC)))
       (!ms (list :at-location  PC
       	   :instruction  'auipc
       	   :memory-probe nil)
            rv32))

      ;; TODO: JAL should return an instruction-misaligned exception if the
      ;;       target address is not aligned to a four-byte boundary

      ;; Update PC
      (rv32 (!xpc PC rv32)))
     rv32))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;			   ;;
;;    Assembly Functions   ;;
;;			   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;
;; Lemmas ;;
;;;;;;;;;;;;

(local (include-book "centaur/gl/gl" :dir :system))

(gl::def-gl-thm n05-when-n05p
  :hyp (n05p x) 
  :concl (equal (n05 x) x)
  :g-bindings (gl::auto-bindings (:nat x 5)))

(gl::def-gl-thm n12-when-n12p
  :hyp (n12p x) 
  :concl (equal (n12 x) x)
  :g-bindings (gl::auto-bindings (:nat x 12)))

(gl::def-gl-thm n20-when-n20p
  :hyp (n20p x) 
  :concl (equal (n20 x) x)
  :g-bindings (gl::auto-bindings (:nat x 20)))

(defthm n05p-of-n05
 (n05p (n05 x)))

(defthm n10p-of-n10
 (n10p (n10 x)))

(defthm n01p-of-n01
 (n01p (n01 x)))

(defthm n08p-of-n08
 (n08p (n08 x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; JAL Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;
;; JAL constants ;;
;;;;;;;;;;;;;;;;;;;
(defconst *jal-opcode* #b1101111)

(define asm-jal ((imm n21p) (rd n05p))
 :guard (equal (n01 imm) 0)
  (+ (ash (n01 (ash imm -20)) 31)
     (ash (n10 (ash imm -1 )) 21)
     (ash (n01 (ash imm -11)) 20)
     (ash (n08 (ash imm -12)) 12)
     (ash (n05      rd      )  7)
     *jal-opcode*		 ))

(gl::def-gl-thm n32p-of-asm-jal-gl
  :hyp (and (n01p i20) (n10p i10-1) (n01p i11) (n08p i19-12) (n05p k))
  :concl (n32p (+  (ash i20    31)
                   (ash i10-1  21)
                   (ash i11    20)
                   (ash i19-12 12)
                   (ash k       7)
                   *jal-opcode*   ))
  :g-bindings (gl::auto-bindings (:nat i20 1) (:nat i10-1 10) (:nat i11 1) (:nat i19-12 8) (:nat k 5)))

(defthm n32p-of-asm-jal
  (n32p (asm-jal imm rd))
  :hints (("Goal" :in-theory (enable asm-jal)
		  :use ((:instance n32p-of-asm-jal-gl (i20    (n01 (ash imm -20)))
                                                      (i10-1  (n10 (ash imm -1 )))
                                                      (i11    (n01 (ash imm -11)))
                                                      (i19-12 (n08 (ash imm -12)))
                                                      (k      (n05      rd      )))))))
			;(:instance n01p-of-n01 (x (ash imm -20)))
			;(:instance n01p-of-n01 (x (ash imm -11)))
			;(:instance n08p-of-n08 (x (ash imm -12)))
			;(:instance n10p-of-n10 (x (ash imm -1 )))
			;(:instance n05p-of-n05 (x      rd      ))))))

(gl::def-gl-thm get-opcode-of-asm-jal-gl
  :hyp (and (n01p i20) (n10p i10-1) (n01p i11) (n08p i19-12) (n05p k))
  :concl (equal (get-opcode (+  (ash i20    31)
                                (ash i10-1  21)
                                (ash i11    20)
                                (ash i19-12 12)
                                (ash k       7)
                                *jal-opcode*   ))
		*jal-opcode*)
  :g-bindings (gl::auto-bindings (:nat i20 1) (:nat i10-1 10) (:nat i11 1) (:nat i19-12 8) (:nat k 5)))

(defthm get-opcode-of-asm-jal
  (equal (get-opcode (asm-jal imm rd)) *jal-opcode*)
  :hints (("Goal" :in-theory (enable asm-jal)
       		  :use ((:instance get-opcode-of-asm-jal-gl (i20    (n01 (ash imm -20)))
                                                            (i10-1  (n10 (ash imm -1 )))
                                                            (i11    (n01 (ash imm -11)))
                                                            (i19-12 (n08 (ash imm -12)))
                                                            (k      (n05      rd      )))))))

(gl::def-gl-thm get-j-imm-of-asm-jal-gl
  :hyp (and (equal (n01 i) 0) (n21p i) (n05p k))
  :concl (equal (get-j-imm (+ (ash (n01 (ash i -20)) 31)
                              (ash (n10 (ash i -1 )) 21)
                              (ash (n01 (ash i -11)) 20)
                              (ash (n08 (ash i -12)) 12)
                              (ash k 7)
                              *jal-opcode*		 ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 21) (:nat k 5)))

(defthm get-j-imm-of-asm-jal
  (implies (and (equal (n01 imm) 0) (n21p imm))
	   (equal (get-j-imm (asm-jal imm rd)) imm))
  :hints (("Goal" :in-theory (enable asm-jal)
                  :use ((:instance get-j-imm-of-asm-jal-gl (i imm) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-jal-gl
  :hyp (and (n01p i20) (n10p i10-1) (n01p i11) (n08p i19-12) (n05p k))
  :concl (equal (get-rd     (+  (ash i20    31)
                                (ash i10-1  21)
                                (ash i11    20)
                                (ash i19-12 12)
                                (ash k       7)
                                *jal-opcode*   ))
		k)
  :g-bindings (gl::auto-bindings (:nat i20 1) (:nat i10-1 10) (:nat i11 1) (:nat i19-12 8) (:nat k 5)))

(defthm get-rd-of-asm-jal
  (equal (get-rd (asm-jal imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-jal)
     		  :use ((:instance get-rd-of-asm-jal-gl     (i20    (n01 (ash imm -20)))
                                                            (i10-1  (n10 (ash imm -1 )))
                                                            (i11    (n01 (ash imm -11)))
                                                            (i19-12 (n08 (ash imm -12)))
                                                            (k      (n05      rd      )))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; JALR Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; JALR constants
(defconst *jalr-opcode* #b1100111)
(defconst *jalr-funct3* #x0)

(define asm-jalr ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *jalr-funct3* 12)
            (ash (n05 rd)       7)
                 *jalr-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *jalr-funct3* 12)
           (ash rd             7)
                *jalr-opcode*   )))

(gl::def-gl-thm n32p-of-asm-jalr-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *jalr-funct3* 12)
                  (ash k    7)
                  *jalr-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-jalr
  (n32p (asm-jalr rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-jalr)
                  :use ((:instance n32p-of-asm-jalr-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-jalr-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
                                       (ash *jalr-funct3* 12)
                                       (ash i 15)
                                       (ash k 7)
                                       *jalr-opcode* )
                                    127))
                *jalr-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-jalr-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
                                       (ash *jalr-funct3* 12)
                                       (ash i 15)
                                       (ash k 7)
                                       *jalr-opcode* ))

                *jalr-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-i-imm-of-asm-jalr-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
                                       (ash *jalr-funct3* 12)
                                       (ash i 15)
                                       (ash k 7)
                                       *jalr-opcode* ))

                j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-jalr
  (equal (get-opcode (asm-jalr i j k)) *jalr-opcode*)
  :hints (("Goal" :in-theory (enable asm-jalr)
                  :use ((:instance get-opcode-of-asm-jalr-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-jalr
  (equal (get-funct3 (asm-jalr i j k)) *jalr-funct3*)
  :hints (("Goal" :in-theory (enable asm-jalr)
                  :use ((:instance get-funct3-of-asm-jalr-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-jalr
  (equal (get-i-imm (asm-jalr i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-jalr)
                  :use ((:instance get-i-imm-of-asm-jalr-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-jalr-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
                             (ash *jalr-funct3* 12)
                             (ash i 15)
                             (ash k 7)
                             *jalr-opcode* ))
                i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-jalr
  (equal (get-rs1 (asm-jalr rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-jalr)
                  :use ((:instance get-rs1-of-asm-jalr-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-jalr-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
                             (ash *jalr-funct3* 12)
                             (ash i 15)
                             (ash k 7)
                             *jalr-opcode* ))
                k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-jalr
  (equal (get-rd (asm-jalr rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-jalr)
                  :use ((:instance get-rd-of-asm-jalr-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))
