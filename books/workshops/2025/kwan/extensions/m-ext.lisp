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

;; DIV
(define rv32-DIV ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (((unless (rv32p rv32))
	(!ms (list :instruction 'DIV
		   :rv32p	nil)
	     rv32))
       ;; Get PC
       (PC (xpc rv32))
       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'DIV
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
		   :instruction 'DIV
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (logext 32 (rgfi rs1 rv32)))
       (rs2-val (logext 32 (rgfi rs2 rv32)))
	
       ;; Compute result
       (result (if (= rs2-val 0) 
	   	   (n32 -1)
	   	   (n32 (floor rs1-val rs2-val))))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!xpc (+ PC 4) rv32)))
      rv32))

;; DIV (UNSIGNED)
(define rv32-DIVU ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (((unless (rv32p rv32))
	(!ms (list :instruction 'DIVU
		   :rv32p	nil)
	     rv32))
       ;; Get PC
       (PC (xpc rv32))
       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'DIVU
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
		   :instruction 'DIVU
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
       (rs2-val (rgfi rs2 rv32))
	
       ;; Compute result
       (result (if (= rs2-val 0) 
	   	   (n32 -1)
	   	   (n32 (floor rs1-val rs2-val))))
	
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

(local (include-book "centaur/gl/gl" :dir :system))

(gl::def-gl-thm n05-of-n05p
  :hyp (n05p x) 
  :concl (equal (n05 x) x)
  :g-bindings (gl::auto-bindings (:nat x 5)))

;; Divide (Signed)
(defconst *div-opcode* #b0110011)
(defconst *div-funct3* #x04)
(defconst *div-funct7* #x01)

(define asm-div ((rs1 n05p) (rs2 n05p) (rd n05p))
 (mbe
  :logic (+ (ash *div-funct7* 25)
            (ash (n05 rs2)    20)
            (ash (n05 rs1)    15)
            (ash *div-funct3* 12)
            (ash (n05 rd)      7)
                 *div-opcode*   )
  :exec (+ (ash *div-funct7* 25)
           (ash rs2          20)
           (ash rs1          15)
           (ash *div-funct3* 12)
           (ash rd            7)
           	*div-opcode*   )))

(gl::def-gl-thm n32p-of-asm-div-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (n32p (+ (ash *div-funct7* 25)
                  (ash j    20)
                  (ash i    15)
                  (ash *div-funct3* 12)
                  (ash k    7)
                  *div-opcode*))
  :g-bindings (gl::auto-bindings (:mix (:nat i 5) (:nat j 5) (:nat k 5))))

(defthm n32p-of-asm-div
  (n32p (asm-div rs1 rs2 rd))
  :hints (("Goal" :in-theory (enable asm-div)
		  :use ((:instance n32p-of-asm-div-gl (i (n05 rs1)) (j (n05 rs2)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-div-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-opcode (+ (ash *div-funct7* 25)
                  	       (ash j    20)
                  	       (ash i    15)
                  	       (ash *div-funct3* 12)
                  	       (ash k    7)
                  	       *div-opcode*))
		*div-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct7-of-asm-div-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct7 (+ (ash *div-funct7* 25)
                  	       (ash j    20)
                  	       (ash i    15)
                  	       (ash *div-funct3* 12)
                  	       (ash k    7)
                  	       *div-opcode*))
		*div-funct7*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-div-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash *div-funct7* 25)
                  	       (ash j    20)
                  	       (ash i    15)
                  	       (ash *div-funct3* 12)
                  	       (ash k    7)
                  	       *div-opcode*))
		*div-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-opcode-of-asm-div
  (equal (get-opcode (asm-div i j k)) #b0110011)
  :hints (("Goal" :in-theory (enable asm-div)
                  :use ((:instance get-opcode-of-asm-div-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-div
  (equal (get-funct3 (asm-div i j k)) *div-funct3*)
  :hints (("Goal" :in-theory (enable asm-div)
                  :use ((:instance get-funct3-of-asm-div-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct7-of-asm-div
  (equal (get-funct7 (asm-div i j k)) *div-funct7*)
  :hints (("Goal" :in-theory (enable asm-div)
                  :use ((:instance get-funct7-of-asm-div-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-div-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs1    (+ (ash *div-funct7* 25)
                  	       (ash j    20)
                  	       (ash i    15)
                  	       (ash *div-funct3* 12)
                  	       (ash k    7)
                  	       *div-opcode*))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs1-of-asm-div
  (equal (get-rs1 (asm-div rs1 rs2 rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-div)
		  :use ((:instance get-rs1-of-asm-div-gl (i (n05 rs1)) (j (n05 rs2)) (k (n05 rd)))))))

(gl::def-gl-thm get-rs2-of-asm-div-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs2    (+ (ash *div-funct7* 25)
                  	       (ash j    20)
                  	       (ash i    15)
                  	       (ash *div-funct3* 12)
                  	       (ash k    7)
                  	       *div-opcode*))
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs2-of-asm-div
  (equal (get-rs2 (asm-div rs1 rs2 rd)) (n05 rs2))
  :hints (("Goal" :in-theory (enable asm-div )
		  :use ((:instance get-rs2-of-asm-div-gl (i (n05 rs1)) (j (n05 rs2)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-div-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rd     (+ (ash *div-funct7* 25)
                  	       (ash j    20)
                  	       (ash i    15)
                  	       (ash *div-funct3* 12)
                  	       (ash k    7)
                  	       *div-opcode*))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rd-of-asm-div
  (equal (get-rd (asm-div rs1 rs2 rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-div)
		  :use ((:instance get-rd-of-asm-div-gl (i (n05 rs1)) (j (n05 rs2)) (k (n05 rd)))))))



;; Divide (Signed)
(defconst *divu-opcode* #b0110011)
(defconst *divu-funct3* #x05)
(defconst *divu-funct7* #x01)

(define asm-divu ((rs1 n05p) (rs2 n05p) (rd n05p))
 (mbe
  :logic (+ (ash *divu-funct7* 25)
            (ash (n05 rs2)    20)
            (ash (n05 rs1)    15)
            (ash *divu-funct3* 12)
            (ash (n05 rd)      7)
                 *divu-opcode*   )
  :exec (+ (ash *divu-funct7* 25)
           (ash rs2          20)
           (ash rs1          15)
           (ash *divu-funct3* 12)
           (ash rd            7)
           	*divu-opcode*   )))

(gl::def-gl-thm n32p-of-asm-divu-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (n32p (+ (ash *divu-funct7* 25)
                  (ash j    20)
                  (ash i    15)
                  (ash *divu-funct3* 12)
                  (ash k    7)
                  *divu-opcode*))
  :g-bindings (gl::auto-bindings (:mix (:nat i 5) (:nat j 5) (:nat k 5))))

(defthm n32p-of-asm-divu
  (n32p (asm-divu rs1 rs2 rd))
  :hints (("Goal" :in-theory (enable asm-divu)
		  :use ((:instance n32p-of-asm-divu-gl (i (n05 rs1)) (j (n05 rs2)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-divu-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-opcode (+ (ash *divu-funct7* 25)
                  	       (ash j    20)
                  	       (ash i    15)
                  	       (ash *divu-funct3* 12)
                  	       (ash k    7)
                  	       *divu-opcode*))
		*divu-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct7-of-asm-divu-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct7 (+ (ash *divu-funct7* 25)
                  	       (ash j    20)
                  	       (ash i    15)
                  	       (ash *divu-funct3* 12)
                  	       (ash k    7)
                  	       *divu-opcode*))
		*divu-funct7*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-divu-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash *divu-funct7* 25)
                  	       (ash j    20)
                  	       (ash i    15)
                  	       (ash *divu-funct3* 12)
                  	       (ash k    7)
                  	       *divu-opcode*))
		*divu-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-opcode-of-asm-divu
  (equal (get-opcode (asm-divu i j k)) #b0110011)
  :hints (("Goal" :in-theory (enable asm-divu)
                  :use ((:instance get-opcode-of-asm-divu-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-divu
  (equal (get-funct3 (asm-divu i j k)) *divu-funct3*)
  :hints (("Goal" :in-theory (enable asm-divu)
                  :use ((:instance get-funct3-of-asm-divu-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct7-of-asm-divu
  (equal (get-funct7 (asm-divu i j k)) *divu-funct7*)
  :hints (("Goal" :in-theory (enable asm-divu)
                  :use ((:instance get-funct7-of-asm-divu-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-divu-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs1    (+ (ash *divu-funct7* 25)
                  	       (ash j    20)
                  	       (ash i    15)
                  	       (ash *divu-funct3* 12)
                  	       (ash k    7)
                  	       *divu-opcode*))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs1-of-asm-divu
  (equal (get-rs1 (asm-divu rs1 rs2 rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-divu)
		  :use ((:instance get-rs1-of-asm-divu-gl (i (n05 rs1)) (j (n05 rs2)) (k (n05 rd)))))))

(gl::def-gl-thm get-rs2-of-asm-divu-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs2    (+ (ash *divu-funct7* 25)
                  	       (ash j    20)
                  	       (ash i    15)
                  	       (ash *divu-funct3* 12)
                  	       (ash k    7)
                  	       *divu-opcode*))
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rs2-of-asm-divu
  (equal (get-rs2 (asm-divu rs1 rs2 rd)) (n05 rs2))
  :hints (("Goal" :in-theory (enable asm-divu )
		  :use ((:instance get-rs2-of-asm-divu-gl (i (n05 rs1)) (j (n05 rs2)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-divu-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rd     (+ (ash *divu-funct7* 25)
                  	       (ash j    20)
                  	       (ash i    15)
                  	       (ash *divu-funct3* 12)
                  	       (ash k    7)
                  	       *divu-opcode*))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 5) (:nat k 5)))

(defthm get-rd-of-asm-divu
  (equal (get-rd (asm-divu rs1 rs2 rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-divu)
		  :use ((:instance get-rd-of-asm-divu-gl (i (n05 rs1)) (j (n05 rs2)) (k (n05 rd)))))))


