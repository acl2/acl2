#|$ACL2s-Preamble$;
;; Copyright (C) 2015, Julien Schmaltz.
;;
;; License: (An MIT/X11-style license)
;;
;;   Permission is hereby granted, free of charge, to any person obtaining a
;;   copy of this software and associated documentation files (the "Software"),
;;   to deal in the Software without restriction, including without limitation
;;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;;   and/or sell copies of the Software, and to permit persons to whom the
;;   Software is furnished to do so, subject to the following conditions:
;;
;;   The above copyright notice and this permission notice shall be included in
;;   all copies or substantial portions of the Software.
;;
;;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;;   DEALINGS IN THE SOFTWARE.
;;
;; Original author: Julien Schmaltz <julien.schmaltz@gmail.com>
;;
;; Julien Schmaltz
;; Formal model of the ISA of the AVR 8-bit controller.
;; This is a very partial model but enough to server the 
;; purpose of verifying the multiplication algorithm 
;; presented in the paper. 
;; 
;; 27 September 2013 (updated 24.05.15 for ACL2 paper)
;; 
;; (Model without using STOBJ's)
;; This file conclude with avr-step (modeling one step)
;; and avr-run which runs a program according to some schedule.
;;
;; This version does not handle flags except for the carry flag. 
;; Note that this is the only relevant flags. Abstracting away from 
;; flags improve performance.
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "ihs/ihs-definitions" :dir :system)

;; macro getting the first 8 bits of the result
;; (taken from Y86 model in the books)
(defmacro n01 (x) `(logand ,x ,(1- (expt 2  1))))
(defmacro n08 (x) `(logand ,x ,(1- (expt 2  8))))

(defun byte_i (i x)
  ;; select byte i of x
  ;; I defined wi somewhere else. They both do the same!
  (n08 (logtail (* i 8) x)))

(defun make-state (pc regs flags stack program memory)
;; FLAGS is a list of 8 flags
;; each flag is 1 for true and 0 for false
;; regs is a list of 32 registers
;; each register is an integer (assumed to be 8-bits, but unbounded for now.)
;; memory is an alist (addr val) representing the memory. Every addres is an integer. 
;; We currently do not distinguish between data and program space or between I/, RAM, etc.
  (list pc regs flags stack program memory))

(defconst *R0* 0)
(defconst *R1* 1)
(defconst *R2* 2)
(defconst *R3* 3)
(defconst *R4* 4)
(defconst *R5* 5)
(defconst *R6* 6)
(defconst *R7* 7)
(defconst *R8* 8)
(defconst *R9* 9)
(defconst *R10* 10)
(defconst *R11* 11)
(defconst *R12* 12)
(defconst *R13* 13)
(defconst *R14* 14)
(defconst *R15* 15)
(defconst *R16* 16)
(defconst *R17* 17)
(defconst *R18* 18)
(defconst *R19* 19)
(defconst *R20* 20)
(defconst *R21* 21)
(defconst *R22* 22)
(defconst *R23* 23)
(defconst *R24* 24)
(defconst *R25* 25)
(defconst *R26* 26) ;; X[0] 
(defconst *R27* 27) ;; X[1]
(defconst *R28* 28) ;; Y[0]
(defconst *R29* 29) ;; Y[1]
(defconst *R30* 30) ;; Z[0]
(defconst *R31* 31) ;; Z[1]

(defun int-list-p (x)
  (if (endp x)
      t
    (and (integerp (car x))
	 (int-list-p (cdr x)))))

(defun read_reg (pos regs)
  (n08 (nth pos regs)))
  
;; modelling of indirect addressing
;; We model the X, Y, and Z pointers 
;; as an append of two registers.
(defun X_val (regs)
  (logapp 8 (read_reg *R26* regs) (read_reg *R27* regs)))

(defun store_X (regs val_16)
  (let ((x_low  (byte_i 0 val_16))
        (x_high (byte_i 1 val_16)))
    (update-nth *R26* x_low (update-nth *R27* x_high regs))))

(defun incr_X (regs)
  (store_X regs (+ 1 (X_val regs))))

(defun add_x (q regs)
  (store_X regs (+ q (X_val regs))))

(defun Y_val (regs)
  (logapp 8 (read_reg *R28* regs) (read_reg *R29* regs)))

(defun store_Y (regs val_16)
  (let ((y_low  (byte_i 0 val_16))
        (y_high (byte_i 1 val_16)))
    (update-nth *R28* y_low (update-nth *R29* y_high regs))))

(defun incr_Y (regs)
  (store_Y regs (+ 1 (Y_val regs))))

(defun add_y (q regs)
  (store_Y regs (+ q (Y_val regs))))

(defun Z_val (regs)
  (logapp 8 (read_reg *R30* regs) (read_reg *R31* regs)))

(defun store_Z (regs val_16)
  (let ((z_low  (byte_i 0 val_16))
        (z_high (byte_i 1 val_16)))
    (update-nth *R30* z_low (update-nth *R31* z_high regs))))

(defun incr_Z (regs)
  (store_Z regs (+ 1 (Z_val regs))))

(defun add_z (q regs)
  (store_Z regs (+ q (Z_val regs))))


(defun apc (s) (nth 0 s))
(defun regs (s) (nth 1 s))
(defun flags (s) (nth 2 s)) ;; flags is a list of 8 bits
(defun stack (s) (nth 3 s))
(defun prg (s) (nth 4 s))
(defun memory (s) (nth 5 s))

(defun set-all-0 (n)
  (if (zp n)
    nil
    (cons 0 (set-all-0 (- n 1)))))

(defun init-regs ()
  ;; function that initializes all registers to 0
  (set-all-0 32))

;; accessors for flags / positions of the flags
(defconst *flag-I* 0)
(defconst *flag-T* 1)
(defconst *flag-H* 2)
(defconst *flag-S* 3)
(defconst *flag-V* 4)
(defconst *flag-N* 5)
(defconst *flag-Z* 6)
(defconst *flag-C* 7)

(defun init-flags ()
  (set-all-0 8))


(defun set-flag-if-cond (flg cond flags)
  ;; we hide the updating of flags in a function
  ;; we want to hide the "if" statement from the rewriter
  ;; result = useful?
  (update-nth flg (if cond 1 0) flags))

(defun next-inst (s) (nth (apc s) (prg s)))

(defun opcode (inst) (nth 0 inst))
(defun avr-arg1 (inst) (nth 1 inst)) ;; examples *R0*, *R1* etc.
(defun avr-arg2 (inst) (nth 2 inst))
(defun avr-arg3 (inst) (nth 3 inst))


;; Model of the stack (taken from M1)
(defun apush (x y) (cons x y))
(defun atop (stack) (car stack))
(defun apop (stack) (cdr stack))


;; ADC - Add with carry
;; Operation: Rd <- Rd + Rd + C
;; Syntax ADC Rd, Rr
;; Operands: 0<= d <= 31, 0<=r<=31 
;; Program counter PC <- PC + 1
;; FLAGS: 
;;  - Carry: set if carry from MSB
;;  - Z: set if result is 0
;; Result equals Rd after operation
;; 

(defun carry-check (res Rd Rr)
  ;; function checking for a carry bit.
  ;; This is the function given in the specification of the ISA of the AVR. 
  (or (and (logbitp 7 Rd)  (logbitp 7 Rr))
      (and (logbitp 7 Rr)  (not (logbitp 7 res)))
      (and (not (logbitp 7 res)) (logbitp 7 Rd))))

(defun execute-ADC (inst s)
  ;; JSZ 18.03.2014
  ;; using the carry-check function above is closer to the ISA specification of the AVR
  ;; but it is not very practical for proofs. By simply shifting and comparing to 0
  ;; I hope to get simpler proofs. 
  (let* ((Rd (nth (avr-arg1 inst) (regs s)))
         (Rr (nth (avr-arg2 inst) (regs s)))
         (c (nth *flag-C* (flags s)))
	 (res (+ c Rd Rr)))
    (make-state (+ 1 (apc s))
                (update-nth (avr-arg1 inst) ;; Rd is updated with the result of ADD
                            (n08 res) ;; we take the first 8 bits (mod)
                            (regs s)) ;; Rr = Rr + Rd
		(update-nth *flag-C* (logtail 8 res) (flags s)) 
                (stack s)
                (prg s)
                (memory s))))
					  
;; ADD - Add without carry
;; Operation: Rd <- Rd + Rr
;; Syntax ADD Rd,Rr
;; Operands: 0<= d <= 31, 0<=r<=31 
;; Program counter PC <- PC + 1
;; FLAGS 
;; Result equals Rd after operation
;; 
(defun execute-ADD (inst s)
  (let* ((Rd (nth (avr-arg1 inst) (regs s)))
         (Rr (nth (avr-arg2 inst) (regs s)))
         (res (+ Rd Rr)))
  (make-state (+ 1 (apc s))
              (update-nth (avr-arg1 inst) ;; Rd is updated with the result of ADD
                          (n08 res)
                          (regs s)) ;; Rr = Rr + Rd
	      (update-nth *flag-C* (logtail 8 res) (flags s))
              (stack s)
              (prg s)
              (memory s))))


;; ASR - Arithmetic Shift Right
;; Operation: shift by one place to the right.
;; PC <- PC + 1
;; Carry flag set if Rd0 (LSB) is set before the set.
(defun execute-ASR (inst s)
  (let* ((Rd (avr-arg1 inst))
         (Rd_v (nth Rd (regs s))))
    (make-state (+ 1 (apc s))
                (update-nth Rd (n08 (ashu 8 Rd_v -1)) (regs s))
                (update-nth *flag-C* (n01 Rd_v) (flags s))
                (stack s)
                (prg s)
                (memory s))))


;; COM - One's complement
;; Operation: Rd <- xFF - Rd
;; Compute one's complement
;; carry is set 

(defun execute-COM (inst s)
  (make-state (+ 1 (apc s))
              (update-nth (avr-arg1 inst)
                          (n08 (- 255 (nth (avr-arg1 inst) (regs s))))
                          (regs s))
              (update-nth *flag-C* 1 (flags s))
              (stack s)
              (prg s)
              (memory s)))

;; CLR - Clear Register
;; Operation: Rd <- Rd xor Rd
;; XOR a register with itself, clearing all bits that are high.
;; Syntax CLR Rd
;; Operands: 16<=d<=31 
;; Program counter PC <- PC + 1
;; FLAGS: Flag Z is set. Flags S, V, N are cleared. 
;; 
(defun execute-CLR (inst s)
  (make-state (+ 1 (apc s))
              (update-nth (avr-arg1 inst)
;                          (n08 (logxor (avr-arg1 inst)
;                                       (avr-arg1 inst)))
                          0
                          (regs s))
             
              (update-nth *flag-Z* 1 
                          (update-nth *flag-S* 0 
                                      (update-nth *flag-V* 0
                                                  (update-nth *flag-N* 0 (flags s)))))
              (stack s)
              (prg s)
              (memory s)))

;; DEC - Decrement by 1
;; Operation: Rd <- Rd - 1
;; Syntax DEC Rd
;; Operands: 0<=d<=31,
;; Program counter PC <- PC + 1
;; FLAGS: Flag Z is set if the result equals 0
;; 
(defun execute-DEC (inst s)
  (make-state (+ 1 (apc s))
              (update-nth (avr-arg1 inst) 
                          (n08 (- (nth (avr-arg1 inst) (regs s))
                                  1))
                          (regs s)) ;; Rd = Rd - 1
              (flags s)
              (stack s)
              (prg s)
              (memory s)))


;; EOR - Exclusive OR
;; Performs the logical EOR between the contents of register Rd and register 
;; Rr and places the result in the destination register Rd.
;; Rd Rd   Rr
;; EOR Rd,Rr
;; PC PC+1
(defun execute-EOR (inst s)
  (let* ((Rd (nth (avr-arg1 inst) (regs s)))
	 (Rr (nth (avr-arg2 inst) (regs s)))
	 (res (logxor Rd Rr)))
    (make-state (+ 1 (apc s))
		(update-nth (avr-arg1 inst) (n08 res) (regs s)) 
		(flags s)
		(stack s)
		(prg s)
		(memory s))))
			    
;; LDD(Y/Z) - Load Indirect with displacement
;; Operation: Rd <- Y + q
;; Syntax LDD Rd Y+q
;; Operands: 0 <= d <= 31, 0<=q<=63
;; Program counter PC <- PC + 1
;; FLAGS 
;; Result equals Rd after operation
;; 
(defun execute-LDDY (inst s)
  (let ((Rd (avr-arg1 inst))
        (q  (avr-arg2 inst)))
    (make-state (+ 1 (apc s))
                (update-nth Rd 
                            (cadr (assoc-equal (Y_val (add_y q (regs s))) (memory s)))
                            (regs s))
                (flags s) ;; we ignore the flags for now
                (stack s)
                (prg s)
                (memory s))))

(defun execute-LDDZ (inst s)
  (let ((Rd (avr-arg1 inst))
        (q  (avr-arg2 inst)))
    (make-state (+ 1 (apc s))
                (update-nth Rd 
                            (cadr (assoc-equal (Z_val (regs s)) (memory s)))
                            (add_z q (regs s)))
                (flags s) ;; we ignore the flags for now
                (stack s)
                (prg s)
                (memory s))))

;; LDI - Load Immediate
;; Operation: Rd <- K
;; Syntax LDI Rd,K
;; Operands: 16<= d <= 31, 0<=K<=255 
;; Program counter PC <- PC + 1
;; FLAGS 
;; Result equals Rd after operation
;; 
(defun execute-LDI (inst s)
  (make-state (+ 1 (apc s))
              (update-nth (avr-arg1 inst) ;; Rd gets value K
                          (avr-arg2 inst) 
                          (regs s)) ;; 
              (flags s) ;; we ignore the flags for now
              (stack s)
              (prg s)
              (memory s)))


;; LD - Load Indirect from Data Space to Register using index X
;; with post increment
;; Operation: 
;; Syntax LD Rd,X,+
;; For my model: LDX1 Rd
;; Program counter PC <- PC + 1
;; FLAGS 
;; Result equals Rd after operation
;; 

(defun execute-LDX1 (inst s)
  (let ((Rd (avr-arg1 inst)))
    (make-state (+ 1 (apc s))
                (update-nth Rd 
                            (cadr (assoc-equal (X_val (regs s)) (memory s)))
                            (incr_x (regs s)))
                (flags s) ;; we ignore the flags for now
                (stack s)
                (prg s)
                (memory s))))


(defun execute-LDY1 (inst s)
  (let ((Rd (avr-arg1 inst)))
    (make-state (+ 1 (apc s))
                (update-nth Rd 
                            (cadr (assoc-equal (Y_val (regs s)) (memory s)))
                            (incr_y (regs s)))
                (flags s) ;; we ignore the flags for now
                (stack s)
                (prg s)
                (memory s))))


;; MOV - Copy register
;; Operation: Rd <- Rr
;; Syntax MOV Rd,Rr
;; Operands: 0<= d <= 31, 0<=r<=31 
;; Program counter PC <- PC + 1
;; FLAGS 
;; Result equals Rd after operation
;; 
(defun execute-MOV (inst s)
  (make-state (+ 1 (apc s))
              (update-nth (avr-arg1 inst) ;; Rd gets value K
                          (nth (avr-arg2 inst) (regs s)) 
                          (regs s)) ;; 
              (flags s) ;; we ignore the flags for now
              (stack s)
              (prg s)
              (memory s)))

;; MOVW - Copy register word
;; Operation: Rd+1:Rd <- Rr+1:Rr
;; Syntax MOVW Rd+1:Rd,Rr+1:Rr (according to ISA)
;; From Peter's code:
;; MOVW Rd,Rr
;; Operands: d in {0,2, ...,30}, r in {0, 2, ....30}
;; Program counter PC <- PC + 1
;; FLAGS 
;; 
(defun execute-MOVW (inst s)
  (let ((Rd (avr-arg1 inst))
        (Rr (avr-arg2 inst)))
    (make-state (+ 1 (apc s))
                (update-nth Rd ;; Rd gets Rr
                            (nth Rr (regs s))
                            (update-nth (+ Rd 1)
                                        (nth (+ Rr 1) (regs s))
                                        (regs s))) ;; 
                (flags s) 
                (stack s)
                (prg s)
                (memory s))))

;; MUL - Multiply Unsigned
;; Operation: R1:R0 <- Rd * Rr
;; Syntax MUL Rd,Rr
;; Operands: 0<= d <= 31, 0<=r<=31 
;; Program counter PC <- PC + 1
;; FLAGS 
;; Result equals Rd after operation
;; 
;; For now, we assume unbounded integers and no modulo arithmetic. 


(defun execute-MUL (inst s)
  (let* ((res (* (nth (avr-arg1 inst) (regs s)) 
                 (nth (avr-arg2 inst) (regs s))))
         (low (byte_i 0 res))
         (high (byte_i 1 res)))
    (make-state (+ 1 (apc s))
                (update-nth *R1* high (update-nth *R0* low (regs s)))
		(update-nth *flag-C* (logtail 7 high) (flags s))
                (stack s)
                (prg s)
                (memory s))))

;; NEG - two's complement
;; Rd <- $00 - Rd
;; PC <- PC + 1
(defun execute-NEG (inst s)
  (let* ((Rd (nth (avr-arg1 inst) (regs s)))
         (res (- 0 Rd))) ; (logext 8 (- 0 Rd)))) ;; signed result
    (make-state (+ 1 (apc s))
                (update-nth (avr-arg1 inst) 
                            (n08 res)
                            (regs s)) 
                (flags s) ;; carry is ignored for now. 
                (stack s)
                (prg s)
                (memory s))))

;; NOP - No Operation
;; This instruction performs a single cycle No Operation.
;; PC   PC + 1
(defun execute-NOP (inst s)
  (declare (ignore inst))
  (make-state (+ 1 (apc s))
	      (regs s)
	      (flags s)
	      (stack s)
	      (prg s)
	      (memory s)))

;; APOP - Pop register from stack
;; Operation: Rd <- STACK
;; Syntax APOP Rd
;; Operands: 0<= d <= 31,  
;; Program counter PC <- PC + 1
;; FLAGS 
;; Result equals Rd after operation
;; STACK / SP <- SP + 1 (we ignore the stack pointer for now)
(defun execute-APOP (inst s)
  (make-state (+ 1 (apc s))
              (update-nth (avr-arg1 inst) ;; Rd gets value K
                          (atop (stack s)) 
                          (regs s)) ;; 
              (flags s) ;; we ignore the flags for now
              (apop (stack s))
              (prg s)
              (memory s)))

;; APUSH - Push register onto stack
;; Operation: STACK <- Rd
;; Syntax APUSH Rd
;; Operands: 0<= d <= 31,  
;; Program counter PC <- PC + 1
;; FLAGS 
;; Result equals Rd after operation
;; STACK / SP <- SP + 1 (we ignore the stack pointer for now)
(defun execute-APUSH (inst s)
  (make-state (+ 1 (apc s))
              (regs s) ;; 
              (flags s) ;; we ignore the flags for now
              (apush (nth (avr-arg1 inst) (regs s)) (stack s))
              (prg s)
              (memory s)))


;; STDZ - Store indirect with displacement in Rr at address pointed by Z+q
;; Syntax STDZ q Rr
;; Z is not modified. 
;; Z+q <- Rr
;; Operations: write Rr to address pointed by Z
;; FLAGS 
;; Result equals Rd after operation
;; 
(defun execute-STDZ (inst s)
  (let ((q (avr-arg1 inst))
        (Rd (avr-arg2 inst)))
    (make-state (+ 1 (apc s)) ;; increment PC by 1
                (regs s) 
                (flags s) ;; we ignore the flags for now
                (stack s)
                (prg s)
                (append 
                 (list 
                  (list (z_val (add_z q (regs s))) (nth Rd (regs s)))) 
                 (memory s))))) ;; update of the memory (note: very inefficient now)

;; STZ1 - Store result in Rr at address pointed by Z
;; Syntax STZ1 Rr
;; Z in post-incremented
;; Operations: write Rr to address pointed by Z
;; FLAGS 
;; Result equals Rd after operation
;; 
(defun execute-STZ1 (inst s)
  (let ((Rd (avr-arg1 inst)))
    (make-state (+ 1 (apc s)) ;; increment PC by 1
                (incr_z (regs s)) ;; Z is incremented
                (flags s) ;; we ignore the flags for now
                (stack s)
                (prg s)
                (append (list (list (Z_val (regs s)) (nth Rd (regs s))))
                        (memory s))))) 
;; update of the memory (note: very inefficient now)


;; SUB - Subtract without carry
;; Operation: Subtracts two registers and places the result in the destination
;; register Rd
;; Rd <- Rd - Rr
;; PC <- PC + 1
(defun execute-SUB (inst s)
  (let* ((Rd (nth (avr-arg1 inst) (regs s)))
	 (Rr (nth (avr-arg2 inst) (regs s)))
	 (res (- Rd Rr)))
    (make-state (+ 1 (apc s))
                (update-nth (avr-arg1 inst) ;; Rd is updated with the result of SBC
                            (n08 res) ;(logext 8 res) ; result 
                            (regs s)) ;; Rr = Rd - Rr
                (update-nth *flag-C* (abs (n01 (logtail 8 res))) (flags s))
                (stack s)
                (prg s)
                (memory s))))

;; SBC - Subtract with Carry
;; syntax SBC Rd, Rr
;; Operations: substract with the carry flag
;; Rd <- Rd - Rr - C
;; d and r between 0 and 31
;; PC <- PC + 1

;(defun carry-check-sbc (res Rd Rr)
;  ;; function checking for a carry bit. (from the ISA spec)
;  (or (and (not (logbitp 7 Rd))  (logbitp 7 Rr))
;      (and (logbitp 7 Rr)  (logbitp 7 res))
;      (and (logbitp 7 res) (not (logbitp 7 Rd)))))

(defun execute-SBC (inst s)
  (let* ((Rd (nth (avr-arg1 inst) (regs s)))
	 (Rr (nth (avr-arg2 inst) (regs s)))
	 (c (nth *flag-C* (flags s)))
	 (res (+ Rd (- Rr) (- c))))
    (make-state (+ 1 (apc s))
                (update-nth (avr-arg1 inst) ;; Rd is updated with the result of SBC
                            (n08 res) ; (logext 8 res) ; result 
                            (regs s)) ;; Rr = Rr + Rd
		;; carry flag is set of the absolute value of Rr + C
		;; is larger than the absolute value of Rd. Cleared otherwise.
                (update-nth *flag-C* (abs (n01 (logtail 8 res))) (flags s))
                (stack s)
                (prg s)
                (memory s))))

;; SBCI - Subtract Immediate with Carry
;; Subtracts a constant from a register and subtracts with the C 
;; Flag and places the result in the destination register Rd.
;; Rd Rd-K-C
;; PC PC+1
;; SBCIRd,K
(defun execute-SBCI (inst s)
  (let* ((Rd (nth (avr-arg1 inst) (regs s)))
	 (K (avr-arg2 inst))
	 (c (nth *flag-C* (flags s)))
	 (res (n08 (+ Rd (- K) (- c)))))
    (make-state (+ 1 (apc s))
		(update-nth (avr-arg1 inst) res (regs s))
                (flags s)
		(stack s)
                (prg s)
                (memory s))))


(defun do-inst (inst s)
  (cond ((equal (opcode inst) 'ADC)
         (execute-ADC   inst s))
        ((equal (opcode inst) 'ADD)
         (execute-ADD   inst s))
        ((equal (opcode inst) 'ASR)
         (execute-ASR inst s))
        ((equal (opcode inst) 'COM)
         (execute-COM   inst s))
        ((equal (opcode inst) 'CLR)
         (execute-CLR   inst s))
        ((equal (opcode inst) 'DEC)
         (execute-DEC   inst s))
	((equal (opcode inst) 'EOR)
         (execute-EOR   inst s))
	((equal (opcode inst) 'LDDY)
         (execute-LDDY   inst s))
        ((equal (opcode inst) 'LDI)
         (execute-LDI   inst s))
        ((equal (opcode inst) 'LDX1)
         (execute-LDX1  inst s))
        ((equal (opcode inst) 'LDY1)
         (execute-LDY1  inst s))
        ((equal (opcode inst) 'MOV)
         (execute-MOV   inst s))
        ((equal (opcode inst) 'MOVW)
         (execute-MOVW  inst s))
        ((equal (opcode inst) 'MUL)
         (execute-MUL   inst s))
	((equal (opcode inst) 'NEG)
         (execute-NEG   inst s))
	((equal (opcode inst) 'NOP)
         (execute-NOP   inst s))
        ((equal (opcode inst) 'APOP)
         (execute-APOP  inst s))
        ((equal (opcode inst) 'APUSH)
         (execute-APUSH inst s))
	((equal (opcode inst) 'SBC)
         (execute-SBC   inst s))
	((equal (opcode inst) 'SBCI)
         (execute-SBCI   inst s))
	((equal (opcode inst) 'STZ1)
         (execute-STZ1  inst s))
	((equal (opcode inst) 'STDZ)
         (execute-STDZ  inst s))
        ((equal (opcode inst) 'SUB)
         (execute-SUB   inst s))
        (t s)))

(defun avr-step (s)
     (do-inst (next-inst s) s))

(defun run (sched s)
     (if (endp sched)
         s
       (run (cdr sched) (avr-step s))))
