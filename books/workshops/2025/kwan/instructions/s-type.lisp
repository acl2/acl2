(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
;(include-book "models/y86/y86-basic/common/operations" :dir :system)
(include-book "../operations")
(include-book "../rv-state")
(include-book "../decode")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;			  ;;
;;    Store Operations    ;;
;;			  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Format for RISC-V S-type operations
;;
;;   31        25 24        20 19      15 14  12 11       7 6            0
;;  |------------|------------|----------|------|----------|--------------|
;;  |  imm[11:5] |    rs2     |   rs1    |funct3| imm[4:0] |    opcode    |
;;  |------------|------------|----------|------|----------|--------------|
;;      7 bits       5 bits      5 bits   3 bits   5 bits       7 bits
;;	              src2        src1                            OP
;;

;;
;; Store Byte
;; 
;;  m[rs1 + imm][0:7] = rs2[0:7]
(define rv32-SB ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (xpc rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'sb
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1   instr))
       (rs2   (get-rs2   instr))
       (imm   (get-s-imm instr))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
       (rs2-val (n08 (rgfi rs2 rv32)))
	
       ;; Compute address
       (addr (n32+ rs1-val imm))

       ;; Store rs2-val
       (rv32 (wm08 addr rs2-val rv32))

       ;; Update PC
       (rv32 (!xpc (+ PC 4) rv32)))
      rv32))

;;
;; Store Half
;; 
;;  m[rs1 + imm][0:7] = rs2[0:7]
(define rv32-SH ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (xpc rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'sh
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1   instr))
       (rs2   (get-rs2   instr))
       (imm   (get-s-imm instr))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
       (v-lo	(n08 (rgfi rs2 rv32)))
       (v-hi	(n08 (ash (rgfi rs2 rv32) -8)))
	
       ;; Compute address
       (addr (n32+ rs1-val imm))

       ;; Memory probe
       ((if (< *2^32-2* addr))
	(!ms (list :at-location  PC
		   :instruction  'sh
		   :write-addr   addr
		   :memory-probe nil)
	     rv32))

       ;; Store rs2-val
       (rv32 (wm08     addr  v-hi rv32))
       (rv32 (wm08 (1+ addr) v-lo rv32))

       ;; Update PC
       (rv32 (!xpc (+ PC 4) rv32)))
      rv32))

;;
;; Store Word
;; 
;;  m[rs1 + imm][0:7] = rs2[0:7]
(local
  (defthm rv32-SH-guard-lemma
    (n08p (n08 x))))

(define rv32-SW ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (xpc rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'sw
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1   instr))
       (rs2   (get-rs2   instr))
       (imm   (get-s-imm instr))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
       (rs2-val	(n32 (rgfi rs2 rv32)))
	
       ;; Compute address
       (addr (n32+ rs1-val imm))

       ;; Memory probe
       ((if (< *2^32-5* addr))
	(!ms (list :at-location  PC
		   :instruction  'sw
		   :write-addr   addr
		   :memory-probe nil)
	     rv32))

       ;; Store rs2-val
       (rv32 (wm32 addr rs2-val rv32))

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; SB Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; SB constants
(defconst *sb-opcode* #b100011)
(defconst *sb-funct3* 0)

(define asm-sb ((rs1 n05p) (rs2 n05p) (imm n12p))
  (b* ((imm (n12 imm)))
      (+ (ash (n07 (ash imm -5)) 25)
         (ash (n05      rs2   ) 20)
         (ash (n05      rs1   ) 15)
         (ash *sb-funct3*       12)
         (ash (n05      imm   )  7)
              *sb-opcode*         )))

(gl::def-gl-thm n32p-of-asm-sb-gl
  :hyp (and (n05p i) (n05p k) (n05p j) (n07p l))
  :concl (n32p (+ (ash           l   25)
                  (ash           j   20)
                  (ash           i   15)
                  (ash *sb-funct3*   12)
                  (ash           k   7)
                       *sb-opcode*         ))
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat l 7) (:mix (:nat i 5) (:nat j 5))))

(defthm n32p-of-asm-sb
  (n32p (asm-sb rs1 rs2 imm))
  :hints (("Goal" :in-theory (enable asm-sb)
		  :use ((:instance n32p-of-asm-sb-gl (i (n05 rs1)) (k (n05 (n12 imm))) (l (n07 (ash (n12 imm) -5))) (j (n05 rs2)))))))

(gl::def-gl-thm get-opcode-of-asm-sb-gl
  :hyp (and (n05p i) (n05p k) (n05p j) (n07p l))
  :concl (equal (get-opcode (+ (ash           l   25)
                               (ash           j   20)
                               (ash           i   15)
                               (ash *sb-funct3*   12)
                               (ash           k   7)
                                    *sb-opcode*         ))
		*sb-opcode*)
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat l 7) (:mix (:nat i 5) (:nat j 5))))

(defthm get-opcode-of-asm-sb
  (equal (get-opcode (asm-sb rs1 rs2 imm)) *sb-opcode*)
  :hints (("Goal" :in-theory (enable asm-sb)
                  :use ((:instance get-opcode-of-asm-sb-gl  (i (n05 rs1)) (k (n05 (n12 imm))) (l (n07 (ash (n12 imm) -5))) (j (n05 rs2)))))))

(gl::def-gl-thm get-funct3-of-asm-sb-gl
  :hyp (and (n05p i) (n05p k) (n05p j) (n07p l))
  :concl (equal (get-funct3 (+ (ash           l   25)
                               (ash           j   20)
                               (ash           i   15)
                               (ash *sb-funct3*   12)
                               (ash           k   7)
                                    *sb-opcode*         ))
		*sb-funct3*)
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat l 7) (:mix (:nat i 5) (:nat j 5))))

(defthm get-funct3-of-asm-sb 
  (equal (get-funct3 (asm-sb rs1 rs2 imm)) *sb-funct3*)
  :hints (("Goal" :in-theory (enable asm-sb)
                  :use ((:instance get-funct3-of-asm-sb-gl  (i (n05 rs1)) (k (n05 (n12 imm))) (l (n07 (ash (n12 imm) -5))) (j (n05 rs2)))))))

(gl::def-gl-thm get-rd-of-asm-sb-gl
  :hyp (and (n05p i) (n05p k) (n05p j) (n07p l))
  :concl (equal (get-rd     (+ (ash           l   25)
                               (ash           j   20)
                               (ash           i   15)
                               (ash *sb-funct3*   12)
                               (ash           k   7)
                                    *sb-opcode*         ))
		k)
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat l 7) (:mix (:nat i 5) (:nat j 5))))

(defthm get-rd-of-asm-sb
  (equal (get-rd (asm-sb rs1 rs2 imm)) (n05 (n12 imm)))
  :hints (("Goal" :in-theory (enable asm-sb)
                  :use ((:instance get-rd-of-asm-sb-gl  (i (n05 rs1)) (k (n05 (n12 imm))) (l (n07 (ash (n12 imm) -5))) (j (n05 rs2)))))))

(gl::def-gl-thm get-s-imm-of-asm-sb-gl
  :hyp (and (n05p i) (n05p k) (n05p j) (n07p l))
  :concl (equal (get-s-imm  (+ (ash           l   25)
                               (ash           j   20)
                               (ash           i   15)
                               (ash *sb-funct3*   12)
                               (ash           k   7)
                                    *sb-opcode*         ))
		(+ (ash l 5) k))
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat l 7) (:mix (:nat i 5) (:nat j 5))))

(defthm get-s-imm-of-asm-sb
  (equal (get-s-imm (asm-sb rs1 rs2 imm)) 
	 (n12 imm))
  :hints (("Goal" :expand (asm-sb rs1 rs2 imm)
                  :in-theory (e/d () (get-s-imm))
		  :use ((:instance get-s-imm-of-asm-sb-gl  (i (n05 rs1)) (k (n05 (n12 imm))) (l (n07 (ash (n12 imm) -5))) (j (n05 rs2)))))))

(gl::def-gl-thm get-rs1-of-asm-sb-gl
  :hyp (and (n05p i) (n05p k) (n05p j) (n07p l))
  :concl (equal (get-rs1    (+ (ash           l   25)
                               (ash           j   20)
                               (ash           i   15)
                               (ash *sb-funct3*   12)
                               (ash           k   7)
                                    *sb-opcode*         ))
		i)
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat l 7) (:mix (:nat i 5) (:nat j 5))))

(defthm get-rs1-of-asm-sb
  (equal (get-rs1 (asm-sb rs1 rs2 imm)) (n05 rs1))
  :hints (("Goal" :in-theory (e/d (asm-sb))
		  :use ((:instance get-rs1-of-asm-sb-gl  (i (n05 rs1)) (k (n05 (n12 imm))) (l (n07 (ash (n12 imm) -5))) (j (n05 rs2)))))))

(gl::def-gl-thm get-rs2-of-asm-sb-gl
  :hyp (and (n05p i) (n05p k) (n05p j) (n07p l))
  :concl (equal (get-rs2    (+ (ash           l   25)
                               (ash           j   20)
                               (ash           i   15)
                               (ash *sb-funct3*   12)
                               (ash           k   7)
                                    *sb-opcode*         ))
		j)
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat l 7) (:mix (:nat i 5) (:nat j 5))))

(defthm get-rs2-of-asm-sb
  (equal (get-rs2 (asm-sb rs1 rs2 imm)) (n05 rs2))
  :hints (("Goal" :in-theory (e/d (asm-sb))
		  :use ((:instance get-rs2-of-asm-sb-gl  (i (n05 rs1)) (k (n05 (n12 imm))) (l (n07 (ash (n12 imm) -5))) (j (n05 rs2)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; SH Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; SH constants
(defconst *sh-opcode* #b100011)
(defconst *sh-funct3* #x1)

(define asm-sh ((rs1 n05p) (rs2 n05p) (imm n12p))
  (b* ((imm (n12 imm)))
      (+ (ash (n07 (ash imm -5)) 25)
         (ash (n05      rs2   ) 20)
         (ash (n05      rs1   ) 15)
         (ash *sh-funct3*       12)
         (ash (n05      imm   )  7)
              *sh-opcode*         )))

(gl::def-gl-thm n32p-of-asm-sh-gl
  :hyp (and (n05p i) (n05p k) (n05p j) (n07p l))
  :concl (n32p (+ (ash           l   25)
                  (ash           j   20)
                  (ash           i   15)
                  (ash *sh-funct3*   12)
                  (ash           k   7)
                       *sh-opcode*         ))
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat l 7) (:mix (:nat i 5) (:nat j 5))))

(defthm n32p-of-asm-sh
  (n32p (asm-sh rs1 rs2 imm))
  :hints (("Goal" :in-theory (enable asm-sh)
		  :use ((:instance n32p-of-asm-sh-gl (i (n05 rs1)) (k (n05 (n12 imm))) (l (n07 (ash (n12 imm) -5))) (j (n05 rs2)))))))

(gl::def-gl-thm get-opcode-of-asm-sh-gl
  :hyp (and (n05p i) (n05p k) (n05p j) (n07p l))
  :concl (equal (get-opcode (+ (ash           l   25)
                               (ash           j   20)
                               (ash           i   15)
                               (ash *sh-funct3*   12)
                               (ash           k   7)
                                    *sh-opcode*         ))
		*sh-opcode*)
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat l 7) (:mix (:nat i 5) (:nat j 5))))

(defthm get-opcode-of-asm-sh
  (equal (get-opcode (asm-sh rs1 rs2 imm)) *sh-opcode*)
  :hints (("Goal" :in-theory (enable asm-sh)
                  :use ((:instance get-opcode-of-asm-sh-gl  (i (n05 rs1)) (k (n05 (n12 imm))) (l (n07 (ash (n12 imm) -5))) (j (n05 rs2)))))))

(gl::def-gl-thm get-funct3-of-asm-sh-gl
  :hyp (and (n05p i) (n05p k) (n05p j) (n07p l))
  :concl (equal (get-funct3 (+ (ash           l   25)
                               (ash           j   20)
                               (ash           i   15)
                               (ash *sh-funct3*   12)
                               (ash           k   7)
                                    *sh-opcode*         ))
		*sh-funct3*)
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat l 7) (:mix (:nat i 5) (:nat j 5))))

(defthm get-funct3-of-asm-sh 
  (equal (get-funct3 (asm-sh rs1 rs2 imm)) *sh-funct3*)
  :hints (("Goal" :in-theory (enable asm-sh)
                  :use ((:instance get-funct3-of-asm-sh-gl  (i (n05 rs1)) (k (n05 (n12 imm))) (l (n07 (ash (n12 imm) -5))) (j (n05 rs2)))))))


(gl::def-gl-thm get-rd-of-asm-sh-gl
  :hyp (and (n05p i) (n05p k) (n05p j) (n07p l))
  :concl (equal (get-rd     (+ (ash           l   25)
                               (ash           j   20)
                               (ash           i   15)
                               (ash *sh-funct3*   12)
                               (ash           k   7)
                                    *sh-opcode*         ))
		k)
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat l 7) (:mix (:nat i 5) (:nat j 5))))

(defthm get-rd-of-asm-sh
  (equal (get-rd (asm-sh rs1 rs2 imm)) (n05 (n12 imm)))
  :hints (("Goal" :in-theory (enable asm-sh)
                  :use ((:instance get-rd-of-asm-sh-gl  (i (n05 rs1)) (k (n05 (n12 imm))) (l (n07 (ash (n12 imm) -5))) (j (n05 rs2)))))))

(gl::def-gl-thm get-s-imm-of-asm-sh-gl
  :hyp (and (n05p i) (n05p k) (n05p j) (n07p l))
  :concl (equal (get-s-imm  (+ (ash           l   25)
                               (ash           j   20)
                               (ash           i   15)
                               (ash *sh-funct3*   12)
                               (ash           k   7)
                                    *sh-opcode*         ))
		(+ (ash l 5) k))
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat l 7) (:mix (:nat i 5) (:nat j 5))))

(defthm get-s-imm-of-asm-sh
  (equal (get-s-imm (asm-sh rs1 rs2 imm)) 
	 (n12 imm))
  :hints (("Goal" :expand (asm-sh rs1 rs2 imm)
                  :in-theory (e/d () (get-s-imm))
		  :use ((:instance get-s-imm-of-asm-sh-gl  (i (n05 rs1)) (k (n05 (n12 imm))) (l (n07 (ash (n12 imm) -5))) (j (n05 rs2)))))))

(gl::def-gl-thm get-rs1-of-asm-sh-gl
  :hyp (and (n05p i) (n05p k) (n05p j) (n07p l))
  :concl (equal (get-rs1    (+ (ash           l   25)
                               (ash           j   20)
                               (ash           i   15)
                               (ash *sh-funct3*   12)
                               (ash           k   7)
                                    *sh-opcode*         ))
		i)
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat l 7) (:mix (:nat i 5) (:nat j 5))))

(defthm get-rs1-of-asm-sh
  (equal (get-rs1 (asm-sh rs1 rs2 imm)) (n05 rs1))
  :hints (("Goal" :in-theory (e/d (asm-sh))
		  :use ((:instance get-rs1-of-asm-sh-gl  (i (n05 rs1)) (k (n05 (n12 imm))) (l (n07 (ash (n12 imm) -5))) (j (n05 rs2)))))))

(gl::def-gl-thm get-rs2-of-asm-sh-gl
  :hyp (and (n05p i) (n05p k) (n05p j) (n07p l))
  :concl (equal (get-rs2    (+ (ash           l   25)
                               (ash           j   20)
                               (ash           i   15)
                               (ash *sh-funct3*   12)
                               (ash           k   7)
                                    *sh-opcode*         ))
		j)
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat l 7) (:mix (:nat i 5) (:nat j 5))))

(defthm get-rs2-of-asm-sh
  (equal (get-rs2 (asm-sh rs1 rs2 imm)) (n05 rs2))
  :hints (("Goal" :in-theory (e/d (asm-sh))
		  :use ((:instance get-rs2-of-asm-sh-gl  (i (n05 rs1)) (k (n05 (n12 imm))) (l (n07 (ash (n12 imm) -5))) (j (n05 rs2)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; SW Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; SW constants
(defconst *sw-opcode* #b100011)
(defconst *sw-funct3* #x2)

(define asm-sw ((rs1 n05p) (rs2 n05p) (imm n12p))
  (b* ((imm (n12 imm)))
      (+ (ash (n07 (ash imm -5)) 25)
         (ash (n05      rs2   ) 20)
         (ash (n05      rs1   ) 15)
         (ash *sw-funct3*       12)
         (ash (n05      imm   )  7)
              *sw-opcode*         )))

(gl::def-gl-thm n32p-of-asm-sw-gl
  :hyp (and (n05p i) (n05p k) (n05p j) (n07p l))
  :concl (n32p (+ (ash           l   25)
                  (ash           j   20)
                  (ash           i   15)
                  (ash *sw-funct3*   12)
                  (ash           k   7)
                       *sw-opcode*         ))
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat l 7) (:mix (:nat i 5) (:nat j 5))))

(defthm n32p-of-asm-sw
  (n32p (asm-sw rs1 rs2 imm))
  :hints (("Goal" :in-theory (enable asm-sw)
		  :use ((:instance n32p-of-asm-sw-gl (i (n05 rs1)) (k (n05 (n12 imm))) (l (n07 (ash (n12 imm) -5))) (j (n05 rs2)))))))

(gl::def-gl-thm get-opcode-of-asm-sw-gl
  :hyp (and (n05p i) (n05p k) (n05p j) (n07p l))
  :concl (equal (get-opcode (+ (ash           l   25)
                               (ash           j   20)
                               (ash           i   15)
                               (ash *sw-funct3*   12)
                               (ash           k   7)
                                    *sw-opcode*         ))
		*sw-opcode*)
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat l 7) (:mix (:nat i 5) (:nat j 5))))

(defthm get-opcode-of-asm-sw
  (equal (get-opcode (asm-sw rs1 rs2 imm)) *sw-opcode*)
  :hints (("Goal" :in-theory (enable asm-sw)
                  :use ((:instance get-opcode-of-asm-sw-gl  (i (n05 rs1)) (k (n05 (n12 imm))) (l (n07 (ash (n12 imm) -5))) (j (n05 rs2)))))))


(gl::def-gl-thm get-funct3-of-asm-sw-gl
  :hyp (and (n05p i) (n05p k) (n05p j) (n07p l))
  :concl (equal (get-funct3 (+ (ash           l   25)
                               (ash           j   20)
                               (ash           i   15)
                               (ash *sw-funct3*   12)
                               (ash           k   7)
                                    *sw-opcode*         ))
		*sw-funct3*)
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat l 7) (:mix (:nat i 5) (:nat j 5))))

(defthm get-funct3-of-asm-sw 
  (equal (get-funct3 (asm-sw rs1 rs2 imm)) *sw-funct3*)
  :hints (("Goal" :in-theory (enable asm-sw)
                  :use ((:instance get-funct3-of-asm-sw-gl  (i (n05 rs1)) (k (n05 (n12 imm))) (l (n07 (ash (n12 imm) -5))) (j (n05 rs2)))))))

(gl::def-gl-thm get-rd-of-asm-sw-gl
  :hyp (and (n05p i) (n05p k) (n05p j) (n07p l))
  :concl (equal (get-rd     (+ (ash           l   25)
                               (ash           j   20)
                               (ash           i   15)
                               (ash *sw-funct3*   12)
                               (ash           k   7)
                                    *sw-opcode*         ))
		k)
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat l 7) (:mix (:nat i 5) (:nat j 5))))

(defthm get-rd-of-asm-sw
  (equal (get-rd (asm-sw rs1 rs2 imm)) (n05 (n12 imm)))
  :hints (("Goal" :in-theory (enable asm-sw)
                  :use ((:instance get-rd-of-asm-sw-gl  (i (n05 rs1)) (k (n05 (n12 imm))) (l (n07 (ash (n12 imm) -5))) (j (n05 rs2)))))))

(gl::def-gl-thm get-s-imm-of-asm-sw-gl
  :hyp (and (n05p i) (n05p k) (n05p j) (n07p l))
  :concl (equal (get-s-imm  (+ (ash           l   25)
                               (ash           j   20)
                               (ash           i   15)
                               (ash *sw-funct3*   12)
                               (ash           k   7)
                                    *sw-opcode*         ))
		(+ (ash l 5) k))
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat l 7) (:mix (:nat i 5) (:nat j 5))))

(defthm get-s-imm-of-asm-sw
  (equal (get-s-imm (asm-sw rs1 rs2 imm)) 
	 (n12 imm))
  :hints (("Goal" :expand (asm-sw rs1 rs2 imm)
                  :in-theory (e/d () (get-s-imm))
		  :use ((:instance get-s-imm-of-asm-sw-gl  (i (n05 rs1)) (k (n05 (n12 imm))) (l (n07 (ash (n12 imm) -5))) (j (n05 rs2)))))))

(gl::def-gl-thm get-rs1-of-asm-sw-gl
  :hyp (and (n05p i) (n05p k) (n05p j) (n07p l))
  :concl (equal (get-rs1    (+ (ash           l   25)
                               (ash           j   20)
                               (ash           i   15)
                               (ash *sw-funct3*   12)
                               (ash           k   7)
                                    *sw-opcode*         ))
		i)
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat l 7) (:mix (:nat i 5) (:nat j 5))))

(defthm get-rs1-of-asm-sw
  (equal (get-rs1 (asm-sw rs1 rs2 imm)) (n05 rs1))
  :hints (("Goal" :in-theory (e/d (asm-sw))
		  :use ((:instance get-rs1-of-asm-sw-gl  (i (n05 rs1)) (k (n05 (n12 imm))) (l (n07 (ash (n12 imm) -5))) (j (n05 rs2)))))))

(gl::def-gl-thm get-rs2-of-asm-sw-gl
  :hyp (and (n05p i) (n05p k) (n05p j) (n07p l))
  :concl (equal (get-rs2    (+ (ash           l   25)
                               (ash           j   20)
                               (ash           i   15)
                               (ash *sw-funct3*   12)
                               (ash           k   7)
                                    *sw-opcode*         ))
		j)
  :g-bindings (gl::auto-bindings (:nat k 5) (:nat l 7) (:mix (:nat i 5) (:nat j 5))))

(defthm get-rs2-of-asm-sw
  (equal (get-rs2 (asm-sw rs1 rs2 imm)) (n05 rs2))
  :hints (("Goal" :in-theory (e/d (asm-sw))
		  :use ((:instance get-rs2-of-asm-sw-gl  (i (n05 rs1)) (k (n05 (n12 imm))) (l (n07 (ash (n12 imm) -5))) (j (n05 rs2)))))))
