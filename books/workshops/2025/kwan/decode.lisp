;; Book for decoding RV32 instructions

(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "operations")
(include-book "rv-state")

;; Format for RISC-V R-type operations
;;
;;   31          25 24      20 19      15 14  12 11       7 6            0
;;  |--------------|----------|----------|------|----------|--------------|
;;  |    funct7    |   rs2    |   rs1    |funct3|    rd    |    opcode    |
;;  |--------------|----------|----------|------|----------|--------------|
;;       7 bits       5 bits     5 bits   3 bits   5 bits       7 bits
;;		       src2       src1              dest          OP

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;				    ;;
;;   Register Decoding Functions    ;;
;;				    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; From The RISC-V Instruction Set Manual Volume I:
;; "The RISC-V ISA keeps the source (rs1 and rs2) and destination (rd)
;;  registers at the same position in all formats to simplify decoding."

;; So we write functions that grab the desired registers for any 32-bit
;; instruction.

;; Source register 1 is always bits 	15 -- 19
;; Source register 2 is always bits 	20 -- 24
;; Destination  register is always bits  7 -- 11

;; Using bitops to simplify bit selection since registers are not in locations
;; easily "rm"-able

(define get-rd ((instr n32p))
  :returns (rd n05p)
  (n05 (ash instr -7)))

(define get-rs1 ((instr n32p))
  :returns (rs1 n05p)
  (n05 (ash instr -15)))

(define get-rs2 ((instr n32p))
  :returns (rs2 n05p)
  (n05 (ash instr -20)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;				       ;;
;;   Instruction Decoding Functions    ;;
;;				       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Get opcode
(define get-opcode ((instr n32p))
  :returns (op n07p)
  :enabled t
  (n07 instr))

(define get-funct3 ((instr n32p))
  :returns (op n03p)
  :enabled t
  (n03 (ash instr -12)))

(define get-funct7 ((instr n32p))
  :returns (op n07p)
  :enabled t
  (n07 (ash instr -25)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;				 ;;
;;   I-type Decoding Functions   ;;
;;				 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; For I-type
(define get-i-imm ((instr n32p))
  :returns (imm n12p)
  (n12 (ash instr -20)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;				 ;;
;;   S-type Decoding Functions   ;;
;;				 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-s-imm ((instr n32p))
  :returns (imm n12p)
  (n12 (logext 12 (+ (ash (get-funct7 instr) 5) 
			  (get-rd     instr   )))))
	     
     
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;				 ;;
;;   B-type Decoding Functions   ;;
;;				 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-b-imm ((instr n32p))
  :returns (imm n13p)
  (b*  ((imm-hi    (n07 (ash instr -25)))  ;; imm[12|10:5]
	(imm-lo    (n05 (ash instr  -7))) ;; imm[4:1|11]
	(imm12	   (n01 (ash imm-hi -6))) 
	(imm11 	   (n01 imm-lo))
	(imm10-5   (n06 imm-hi))
	(imm4-1    (n04 (ash imm-lo -1))))
       (n13 (+ (ash imm12   12)
	       (ash imm11   11)
	       (ash imm10-5  5)
	       (ash imm4-1   1)))))
	
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;				 ;;
;;   U-type Decoding Functions   ;;
;;				 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-u-imm ((instr n32p))
  :returns (imm n20p)
  (n20 (ash instr -12)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;				 ;;
;;   J-type Decoding Functions   ;;
;;				 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-j-imm ((instr n32p))
  :returns (imm n21p)
  (n21 (+ (ash (n01 (ash instr -31)) 20)
          (ash (n08 (ash instr -12)) 12)
          (ash (n01 (ash instr -20)) 11)
          (ash (n10 (ash instr -21))  1))))
