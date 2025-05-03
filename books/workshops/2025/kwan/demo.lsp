(include-book "init")
(in-theory (enable rv32-step rv32-add))

;; 32-bit RISC-V:
;;    program counter
;;  |-----------------|
;;  |       pc        |
;;  |-----------------|
;;   31              0 
;;
;;     register file
;;  |-----------------|
;;  |	    x0        |
;;  |-----------------|
;;  |	    x1	      |
;;  |-----------------|
;;          ... 
;;  |-----------------|
;;  |	    x31       |
;;  |-----------------|
;;   31              0 
;;  read decode execute
;;     pc 
;;     v
;;  |================= ... ==|
;;   2^32 bytes (~4GB) memory

;; Assemble machine code
;; instruction specifying 
;;   x3 <- x1 + x2 
(asm-add 1 2 3)

;; Initialize RISC-V state object
;; called rv32
(init-rv32-state nil 0 rv32)

;; place 42 into x1
(!rgfi 1 42 rv32)

;; place 3 into x2
(!rgfi 2 3 rv32)

;; place ADD machine code into memory
(wm32 0 (asm-add 1 2 3) rv32)

;; perform 1 fetch-decode-execute cycle
(rv32-step rv32)

;; read from x3
(rgfi 3 rv32)

(defmacro xpc (rv32)
 (list 'xpc rv32))


;; Theorem:
;; x3 == x1 + x2 for any x1, x2
(defthm x3=x1+x2
 (implies (and (rv32p rv32)
 	       (n32p a) ; a 32-bit vec
	       (n32p b) ; b 32-bit vec
	       (equal (rgfi 1 rv32) a)
	       (equal (rgfi 2 rv32) b)
	       (equal (xpc rv32)  0)
	       (equal (rm32 0 rv32) (asm-add 1 2 3)))
	  (equal (rgfi 3 (rv32-step rv32)) (n32+ a b))))


