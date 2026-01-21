(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "../operations")
(include-book "../rv-state")
(include-book "../decode")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;					       ;;
;;    Load / Add Upper Immediate Operations    ;;
;;					       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Format for RISC-V U-type operations
;;
;;   31                                       12 11       7 6            0
;;  |-------------------------------------------|----------|--------------|
;;  |                imm[31:12]                 |    rd    |    opcode    |
;;  |-------------------------------------------|----------|--------------|
;;                    20 bits                      5 bits       7 bits
;;	         I-immediate[11:0]                  dest          OP
;;

;; Load Upper Immediate
;; rd = imm << 12
;; Do not need to sign extend imm because just placing value into dest
(define rv32-lui ((rv32 rv32p))
  ;:returns (rv32 rv32p :hyp :guard)
  :verify-guards nil
  (b* (((unless (rv32p rv32))
	(!ms (list :instruction 'lui
		   :rv32p	nil)
	     rv32))
       ;; Get PC
       (PC (xpc rv32))
       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'lui
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rd    (get-rd    instr))
       (imm   (get-u-imm instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'lui
		   :destination-register-x0 t)
	     rv32))

       ;; Store result
       (rv32 (!rgfi rd (ash imm 12) rv32))

       ;; Update PC
       (rv32 (!xpc (+ PC 4) rv32)))
      rv32))


;; Add Upper Immediate to PC
;; rd = PC + (imm << 12)
;; Need to sign extend
(define rv32-AUIPC ((rv32 rv32p))
  ;:returns (rv32 rv32p :hyp :guard)
  :verify-guards nil
  (b* (((unless (rv32p rv32))
	(!ms (list :instruction 'auipc
		   :rv32p	nil)
	     rv32))
       ;; Get PC
       (PC (xpc rv32))
       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'auipc
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rd    (get-rd    instr))
       (imm   (logext 32 (ash (get-u-imm instr) 12)))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'auipc
		   :destination-register-x0 t)
	     rv32))

       ;; Store result
       (rv32 (!rgfi rd (n32+ PC imm) rv32))

       ;; Update PC
       (rv32 (!xpc (+ PC 4) rv32)))
      rv32))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;			   ;;
;;    Assembly Functions   ;;
;;			   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;
;; Lemmas ;;
;;;;;;;;;;;;

(include-book "centaur/gl/gl" :dir :system)

(gl::def-gl-thm n05-of-n05p
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

(gl::def-gl-thm n32p-of-ash-12-when-n20p
  :hyp (n20p x)                   
  :concl (n32p (ash x 12))
  :g-bindings (gl::auto-bindings (:nat x 20)))

(defthm n32p-of-ash-get-u-imm-12
  (n32p (ash (get-u-imm instr) 12)))

(defthm rv32p-of-rv32-lui-when-rv32p
  (implies (rv32p rv32) (rv32p (rv32-lui rv32)))
  :hints (("Goal" :in-theory (enable rv32-lui))))

(verify-guards rv32-lui)

(defthm rv32p-of-rv32-auipc-when-rv32p
  (implies (rv32p rv32) (rv32p (rv32-auipc rv32)))
  :hints (("Goal" :in-theory (enable rv32-auipc))))

(verify-guards rv32-auipc)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; LUI Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; LUI constants
(defconst *lui-opcode* #b0110111)

(define asm-lui ((imm n20p) (rd n05p))
 (mbe
  :logic (+ (ash (n20 imm)     12)
            (ash (n05 rd)       7)
                 *lui-opcode*   )
  :exec (+ (ash imm           12)
           (ash rd             7)
           	*lui-opcode*   )))

(gl::def-gl-thm n32p-of-asm-lui-gl
  :hyp (and (n20p j) (n05p k))
  :concl (n32p (+ (ash j    12)
                  (ash k    7)
                  *lui-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 20) (:nat k 5)))

(defthm n32p-of-asm-lui
  (n32p (asm-lui imm rd))
  :hints (("Goal" :in-theory (enable asm-lui)
		  :use ((:instance n32p-of-asm-lui-gl (j (n20 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-lui-gl
  :hyp (and (n20p j) (n05p k))
  :concl (equal (get-opcode (+ (ash j 12)
                               (ash k 7)
                               *lui-opcode*))
		*lui-opcode*)
  :g-bindings (gl::auto-bindings (:nat j 20) (:nat k 5)))

(defthm get-opcode-of-asm-lui
  (equal (get-opcode (asm-lui imm rd)) *lui-opcode*)
  :hints (("Goal" :in-theory (enable asm-lui)
                  :use ((:instance get-opcode-of-asm-lui-gl (j (n20 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-u-imm-of-asm-lui-gl
  :hyp (and (n20p j) (n05p k))
  :concl (equal (get-u-imm  (+ (ash j 12)
                               (ash k 7)
                               *lui-opcode*))
		j)
  :g-bindings (gl::auto-bindings (:nat j 20) (:nat k 5)))

(defthm get-u-imm-of-asm-lui
  (equal (get-u-imm (asm-lui imm rd)) (n20 imm))
  :hints (("Goal" :in-theory (enable asm-lui)
                  :use ((:instance get-u-imm-of-asm-lui-gl (j (n20 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-lui-gl
  :hyp (and (n20p j) (n05p k))
  :concl (equal (get-rd     (+ (ash j 12)
                               (ash k 7)
                               *lui-opcode*))
		k)
  :g-bindings (gl::auto-bindings (:nat j 20) (:nat k 5)))

(defthm get-rd-of-asm-lui
  (equal (get-rd (asm-lui imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-lui)
		  :use ((:instance get-rd-of-asm-lui-gl (j (n20 imm)) (k (n05 rd)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; AUIPC Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; AUIPC constants
(defconst *auipc-opcode* #b0010111)

(define asm-auipc ((imm n20p) (rd n05p))
 (mbe
  :logic (+ (ash (n20 imm)     12)
            (ash (n05 rd)       7)
                 *auipc-opcode*   )
  :exec (+ (ash imm           12)
           (ash rd             7)
           	*auipc-opcode*   )))

(gl::def-gl-thm n32p-of-asm-auipc-gl
  :hyp (and (n20p j) (n05p k))
  :concl (n32p (+ (ash j    12)
                  (ash k    7)
                  *auipc-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 20) (:nat k 5)))

(defthm n32p-of-asm-auipc
  (n32p (asm-auipc imm rd))
  :hints (("Goal" :in-theory (enable asm-auipc)
		  :use ((:instance n32p-of-asm-auipc-gl (j (n20 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-auipc-gl
  :hyp (and (n20p j) (n05p k))
  :concl (equal (get-opcode (+ (ash j 12)
                               (ash k 7)
                               *auipc-opcode*))
		*auipc-opcode*)
  :g-bindings (gl::auto-bindings (:nat j 20) (:nat k 5)))

(defthm get-opcode-of-asm-auipc
  (equal (get-opcode (asm-auipc imm rd)) *auipc-opcode*)
  :hints (("Goal" :in-theory (enable asm-auipc)
                  :use ((:instance get-opcode-of-asm-auipc-gl (j (n20 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-u-imm-of-asm-auipc-gl
  :hyp (and (n20p j) (n05p k))
  :concl (equal (get-u-imm  (+ (ash j 12)
                               (ash k 7)
                               *auipc-opcode*))
		j)
  :g-bindings (gl::auto-bindings (:nat j 20) (:nat k 5)))

(defthm get-u-imm-of-asm-auipc
  (equal (get-u-imm (asm-auipc imm rd)) (n20 imm))
  :hints (("Goal" :in-theory (enable asm-auipc)
                  :use ((:instance get-u-imm-of-asm-auipc-gl (j (n20 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-auipc-gl
  :hyp (and (n20p j) (n05p k))
  :concl (equal (get-rd     (+ (ash j 12)
                               (ash k 7)
                               *auipc-opcode*))
		k)
  :g-bindings (gl::auto-bindings (:nat j 20) (:nat k 5)))

(defthm get-rd-of-asm-auipc
  (equal (get-rd (asm-auipc imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-auipc)
		  :use ((:instance get-rd-of-asm-auipc-gl (j (n20 imm)) (k (n05 rd)))))))
