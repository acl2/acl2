;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau (derived from the FM9001 work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; The ACL2 source code for the FM9001 work is available at
;; https://github.com/acl2/acl2/tree/master/books/projects/fm9001.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; January 2019

(in-package "ADE")

(include-book "alu-spec")
(include-book "memory")

;; ======================================================================

#|
   FM9001 -- a processor for a new decade.

   Instruction format:
                                                          { N/A  mode-a rn-a
                                                          {  3     2      4
unused op-code store-cc set-flags mode-b rn-b a-immediate |
  4       4       4        4        2      4        1     {    a-immediate
                                                          {         9


The A operand is a 10 bit field.  If the high order bit is set, the low order
9 bits are treated as a signed immediate.  Otherwise, the low order six bits of
the A operand are a mode/register pair identical to the B operand.

(Note:  We use "a" for "rn-a" and "b" for "rn-b" below.)

Interpretation of the OP-CODE.

 0000  b <- a             Move
 0001  b <- a + 1         Increment
 0010  b <- a + b + c     Add with carry
 0011  b <- b + a         Add
 0100  b <- 0 - a         Negation
 0101  b <- a - 1         Decrement
 0110  b <- b - a - c     Subtract with borrow
 0111  b <- b - a         Subtract
 1000  b <- a >> 1        Rotate right, shifted through carry
 1001  b <- a >> 1        Arithmetic shift right, top bit copied
 1010  b <- a >> 1        Logical shift right, top bit zero
 1011  b <- b XOR a       Exclusive or
 1100  b <- b | a         Or
 1101  b <- b & a         And
 1110  b <- ~a            Not
 1111  b <- a             Move


Interpretation of the STORE-CC field.

 0000  (~c)                          Carry clear
 0001  (c)                           Carry set
 0010  (~v)                          Overflow clear
 0011  (v)                           Overflow set
 0100  (~n)                          Plus
 0101  (n)                           Negative
 0110  (~z)                          Not equal
 0111  (z)                           Equal
 1000  (~c & ~z)                     High
 1001  (c | z)                       Low or same
 1010  (n & v | ~n & ~v)             Greater or equal
 1011  (n & ~v | ~n & v)             Less than
 1100  (n & v & ~z | ~n & ~v & ~z)   Greater than
 1101  (z | n & ~v | ~n & v)         Less or equal
 1110  (t)                           True
 1111  (nil)                         False


Flags are set conditionally based on the SET-FLAGS field.

 0000  ----
 0001  ---Z
 0010  --N-
 0011  --NZ
 0100  -V--
 0101  -V-Z
 0110  -VN-
 0111  -VNZ
 1000  C---
 1001  C--Z
 1010  C-N-
 1011  C-NZ
 1100  CV--
 1101  CV-Z
 1110  CVN-
 1111  CVNZ

Addressing Modes for "a" and "b".

 00  Register Direct
 01  Register Indirect
 10  Register Indirect with Pre-decrement
 11  Register Indirect with Post-increment


Register Numbers for "a" and "b".

 0000  Register 0
 0001  Register 1
 0010  Register 2
 0011  Register 3
 0100  Register 4
 0101  Register 5
 0110  Register 6
 0111  Register 7
 1000  Register 8
 1001  Register 9
 1010  Register 10
 1011  Register 11
 1100  Register 12
 1101  Register 13
 1110  Register 14
 1111  Register 15

|#

;; Instruction accessors

(defun reg-size ()
  (declare (xargs :guard t))
  4)

(defun a-immediate-p (instruction)
  (declare (xargs :guard (true-listp instruction)))
  (nth 9 instruction))

(defthm booleanp-a-immediate-p
  (implies (bvp ir)
           (booleanp (a-immediate-p ir)))
  :rule-classes :type-prescription)

(defun a-immediate (instruction)
  (declare (xargs :guard (true-listp instruction)))
  (subseq-list instruction 0 9))

(defthm len-a-immediate
  (equal (len (a-immediate i-reg)) 9))

(defthm bvp-a-immediate
  (implies (bvp i-reg)
           (bvp (a-immediate i-reg)))
  :rule-classes (:rewrite :type-prescription))

(defun rn-a (instruction)
  (declare (xargs :guard (true-listp instruction)))
  (subseq-list instruction 0 4))

(defthm len-rn-a
  (equal (len (rn-a i-reg)) 4))

(defthm bvp-rn-a
  (implies (bvp i-reg)
           (bvp (rn-a i-reg)))
  :rule-classes (:rewrite :type-prescription))

(defun mode-a (instruction)
  (declare (xargs :guard (true-listp instruction)))
  (subseq-list instruction 4 6))

;; (defthm true-listp-mode-a
;;   (true-listp (mode-a i-reg))
;;   :rule-classes :type-prescription)

(defthm len-mode-a
  (equal (len (mode-a i-reg)) 2))

(defthm bvp-mode-a
  (implies (bvp i-reg)
           (bvp (mode-a i-reg)))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defun rn-b (instruction)
  (declare (xargs :guard (true-listp instruction)))
  (subseq-list instruction 10 14))

(defthm len-rn-b
  (equal (len (rn-b i-reg)) 4))

(defthm bvp-rn-b
  (implies (bvp i-reg)
           (bvp (rn-b i-reg)))
  :rule-classes (:rewrite :type-prescription))

(defun mode-b (instruction)
  (declare (xargs :guard (true-listp instruction)))
  (subseq-list instruction 14 16))

(defthm len-mode-b
  (equal (len (mode-b i-reg)) 2))

(acl2::set-induction-depth-limit nil) ; 14 suffices, but 13 does not

(defthm bvp-mode-b
  (implies (bvp i-reg)
           (bvp (mode-b i-reg)))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defun set-flags (instruction)
  (declare (xargs :guard (true-listp instruction)))
  (subseq-list instruction 16 20))

(defthm len-set-flags
  (equal (len (set-flags i-reg)) 4))

(defthm bvp-set-flags
  (implies (bvp i-reg)
           (bvp (set-flags i-reg)))
  :rule-classes (:rewrite :type-prescription))

(defun store-cc (instruction)
  (declare (xargs :guard (true-listp instruction)))
  (subseq-list instruction 20 24))

(defthm len-store-cc
  (equal (len (store-cc i-reg)) 4))

(defthm bvp-store-cc
  (implies (bvp i-reg)
           (bvp (store-cc i-reg)))
  :rule-classes (:rewrite :type-prescription))

(defun op-code (instruction)
  (declare (xargs :guard (true-listp instruction)))
  (subseq-list instruction 24 28))

(defthm len-op-code
  (equal (len (op-code i-reg)) 4))

(defthm bvp-op-code
  (implies (bvp i-reg)
           (bvp (op-code i-reg)))
  :rule-classes (:rewrite :type-prescription))

(defthm unary-op-code-p-op-code->v-alu=v-alu-1
  (implies (unary-op-code-p (op-code i-reg))
           (equal (v-alu c a b (op-code i-reg))
                  (v-alu-1 c a (op-code i-reg))))
  :hints (("Goal" :in-theory (enable unary-op-code-p->v-alu=v-alu-1))))

(deftheory ir-fields-theory
  '(a-immediate-p a-immediate rn-a mode-a rn-b mode-b
                  set-flags store-cc op-code))

(in-theory (disable ir-fields-theory))

;; SET-FLAGS fields

(defun z-set (set-flags)
  (declare (xargs :guard (true-listp set-flags)))
  (nth 0 set-flags))

(defthm booleanp-z-set
  (implies (bvp set-flags)
           (booleanp (z-set set-flags)))
  :rule-classes :type-prescription)

(defun n-set (set-flags)
  (declare (xargs :guard (true-listp set-flags)))
  (nth 1 set-flags))

(defthm booleanp-n-set
  (implies (bvp set-flags)
           (booleanp (n-set set-flags)))
  :rule-classes :type-prescription)

(defun v-set (set-flags)
  (declare (xargs :guard (true-listp set-flags)))
  (nth 2 set-flags))

(defthm booleanp-v-set
  (implies (bvp set-flags)
           (booleanp (v-set set-flags)))
  :rule-classes :type-prescription)

(defun c-set (set-flags)
  (declare (xargs :guard (true-listp set-flags)))
  (nth 3 set-flags))

(defthm booleanp-c-set
  (implies (bvp set-flags)
           (booleanp (c-set set-flags)))
  :rule-classes :type-prescription)

(deftheory set-flags-theory '(z-set n-set v-set c-set))

(in-theory (disable set-flags-theory))

;; Flags fields

(defun z-flag (flags)
  (declare (xargs :guard (true-listp flags)))
  (nth 0 flags))

(defthm booleanp-z-flag
  (implies (bvp flags)
           (booleanp (z-flag flags)))
  :rule-classes :type-prescription)

(defun n-flag (flags)
  (declare (xargs :guard (true-listp flags)))
  (nth 1 flags))

(defthm booleanp-n-flag
  (implies (bvp flags)
           (booleanp (n-flag flags)))
  :rule-classes :type-prescription)

(defun v-flag (flags)
  (declare (xargs :guard (true-listp flags)))
  (nth 2 flags))

(defthm booleanp-v-flag
  (implies (bvp flags)
           (booleanp (v-flag flags)))
  :rule-classes :type-prescription)

(defun c-flag (flags)
  (declare (xargs :guard (true-listp flags)))
  (nth 3 flags))

(defthm booleanp-c-flag
  (implies (bvp flags)
           (booleanp (c-flag flags)))
  :rule-classes :type-prescription)

(deftheory flags-theory '(z-flag n-flag v-flag c-flag))

(in-theory (disable flags-theory))

;; Interpretation of accessors

(defun reg-direct-p (mode)
  (declare (xargs :guard t))
  (equal mode (list nil nil)))

(defthm booleanp-reg-direct-p
  (booleanp (reg-direct-p mode))
  :rule-classes :type-prescription)

(defun reg-indirect-p (mode)
  (declare (xargs :guard t))
  (equal mode (list t nil)))

(defthm booleanp-reg-indirect-p
  (booleanp (reg-indirect-p mode))
  :rule-classes :type-prescription)

(defun pre-dec-p (mode)
  (declare (xargs :guard t))
  (equal mode (list nil t)))

(defthm booleanp-pre-dec-p
  (booleanp (pre-dec-p mode))
  :rule-classes :type-prescription)

(defun post-inc-p (mode)
  (declare (xargs :guard t))
  (equal mode (list t t)))

(defthm booleanp-post-inc-p
  (booleanp (post-inc-p mode))
  :rule-classes :type-prescription)

(defthm reg-direct->not-reg-indirect
  (implies (reg-direct-p mode)
           (and (not (reg-indirect-p mode))
                (not (pre-dec-p mode))
                (not (post-inc-p mode)))))

(deftheory reg-mode-theory
  '(reg-direct-p reg-indirect-p pre-dec-p post-inc-p))

(in-theory (disable reg-mode-theory))

;; Interpretation of STORE-CC

(defun store-resultp (store-cc flags)
  (declare (xargs :guard (true-listp flags)))
  (let ((c (c-flag flags))
        (v (v-flag flags))
        (n (n-flag flags))
        (z (z-flag flags)))
    (let ((c~ (not c))
          (v~ (not v))
          (n~ (not n))
          (z~ (not z)))

      (cond ((equal store-cc *v0000*) c~)
            ((equal store-cc *v0001*) c)
            ((equal store-cc *v0010*) v~)
            ((equal store-cc *v0011*) v)
            ((equal store-cc *v0100*) n~)
            ((equal store-cc *v0101*) n)
            ((equal store-cc *v0110*) z~)
            ((equal store-cc *v0111*) z)
            ((equal store-cc *v1000*) (and c~ z~))
            ((equal store-cc *v1001*) (or c z))
            ((equal store-cc *v1010*) (or (and n v) (and n~ v~)))
            ((equal store-cc *v1011*) (or (and n v~) (and n~ v)))
            ((equal store-cc *v1100*) (or (and n v z~) (and n~ v~ z~)))
            ((equal store-cc *v1101*) (or z (and n v~) (and n~ v)))
            ((equal store-cc *v1110*) t)
            (t                        nil)))))

(defthm booleanp-store-resultp
  (implies (bvp flags)
           (booleanp (store-resultp store-cc flags)))
  :hints (("Goal" :in-theory (enable c-flag v-flag n-flag z-flag)))
  :rule-classes :type-prescription)

(in-theory (disable store-resultp))

;; UPDATE-FLAGS set-flags cvzbv

(defun update-flags (flags set-flags cvzbv)
  (declare (xargs :guard (and (true-listp flags)
                              (true-listp set-flags)
                              (true-listp cvzbv))))
  (list (b-if (z-set set-flags) (zb cvzbv) (z-flag flags))
        (b-if (n-set set-flags) (n  cvzbv) (n-flag flags))
        (b-if (v-set set-flags) (v  cvzbv) (v-flag flags))
        (b-if (c-set set-flags) (c  cvzbv) (c-flag flags))))

(defthm bvp-update-flags
  (bvp (update-flags flags set-flags cvzbv))
  :rule-classes (:rewrite :type-prescription))

(defthm len-update-flags
  (equal (len (update-flags flags set-flags cvzbv))
         4))

(defthm booleanp-c-flag-update-flags
  (booleanp (c-flag (update-flags flags set-flags cvzbv)))
  :rule-classes :type-prescription)

(in-theory (disable update-flags))

;; An FM9001 state is a list of two items: The processor state, which
;; consists of the register file and flags, and the memory state.

(defund regs (st)
  (declare (xargs :guard (true-listp st)))
  (nth 0 st))

(defund flags (st)
  (declare (xargs :guard (true-listp st)))
  (nth 1 st))

;; ======================================================================

;; The FM9001 instruction interpreter

;; FM9001-ALU-OPERATION -- Computes, and conditionally stores the result.

(defun fm9001-alu-operation (regs flags mem ins operand-a operand-b b-address)
  (declare (xargs :guard (and (true-listp flags)
                              (true-listp ins)
                              (consp operand-a)
                              (true-listp operand-a)
                              (consp operand-b)
                              (true-listp operand-b)
                              (true-listp b-address))))
  (let ((op-code   (op-code ins))
        (store-cc  (store-cc ins))
        (set-flags (set-flags ins))
        (mode-b    (mode-b   ins))
        (rn-b      (rn-b    ins)))
    (let ((cvzbv  (v-alu (c-flag flags) operand-a operand-b op-code))
          (storep (store-resultp store-cc flags)))
      (let ((bv (bv cvzbv)))
        (let ((new-regs   (if (and storep (reg-direct-p mode-b))
                              (write-mem rn-b regs bv)
                            regs))
              (new-flags  (update-flags flags set-flags cvzbv))
              (new-mem    (if (and storep (not (reg-direct-p mode-b)))
                              (write-mem b-address mem bv)
                            mem)))

          (list (list new-regs new-flags) new-mem))))))

;; FM9001-OPERAND-B -- Readies the B operand, and side-effects the operand B
;; register. The B-ADDRESS is held for the final stage.

(defun fm9001-operand-b (regs flags mem ins operand-a)
  (let ((mode-b (mode-b ins))
        (rn-b   (rn-b  ins)))
    (let ((reg (read-mem rn-b regs)))
      (let ((reg- (v-dec reg))
            (reg+ (v-inc reg)))
        (let ((b-address (if (pre-dec-p mode-b)
                             reg-
                           reg)))
          (let ((operand-b (if (reg-direct-p mode-b)
                               reg
                             (read-mem b-address mem)))
                (new-regs (if (pre-dec-p mode-b)
                              (write-mem rn-b regs reg-)
                            (if (post-inc-p mode-b)
                                (write-mem rn-b regs reg+)
                              regs))))

            (FM9001-alu-operation new-regs flags mem ins operand-a operand-b
                                  b-address)))))))

;; FM9001-OPERAND-A -- Readies the A operand, and side-effects the operand A
;; register.

(defun fm9001-operand-a (regs flags mem ins)
  (let ((a-immediate-p (a-immediate-p ins))
        (a-immediate   (sign-extend (a-immediate ins) 32))
        (mode-a        (mode-a ins))
        (rn-a          (rn-a  ins)))
    (let ((reg (read-mem rn-a regs)))
      (let ((reg- (v-dec reg))
            (reg+ (v-inc reg)))
        (let ((operand-a (if a-immediate-p
                             a-immediate
                           (if (reg-direct-p mode-a)
                               reg
                             (if (pre-dec-p mode-a)
                                 (read-mem reg- mem)
                               (read-mem reg mem))))))
          (let ((new-regs (if a-immediate-p
                              regs
                            (if (pre-dec-p mode-a)
                                (write-mem rn-a regs reg-)
                              (if (post-inc-p mode-a)
                                  (write-mem rn-a regs reg+)
                                regs)))))

            (FM9001-operand-b new-regs flags mem ins operand-a)))))))

;; FM9001-FETCH -- Fetches the instruction and increments the PC.

(defun FM9001-FETCH (regs flags mem pc-reg)
  (let ((pc (read-mem pc-reg regs)))
    (let ((ins (read-mem pc mem)))
      (let ((pc+1 (v-inc pc)))
        (let ((new-regs (write-mem pc-reg regs pc+1)))
          (FM9001-operand-a new-regs flags mem ins))))))

;; FM9001-STEP -- Unpacks the state.

(defund FM9001-step (st pc-reg)
  (let ((p-st (car st))
        (mem  (cadr st)))
    (FM9001-fetch (regs p-st) (flags p-st) mem pc-reg)))

;; FM9001 -- Simulates N instructions, using register 15 as the PC.

(defund FM9001 (st n)
  (if (zp n)
      st
    (FM9001 (FM9001-step st (nat-to-v 15 (reg-size)))
            (1- n))))

;; FM9001-INTERPRETER -- Simulates N instructions with a given PC.

(defun FM9001-interpreter (st pc-reg n)
  (if (zp n)
      st
    (FM9001-interpreter
     (FM9001-step st pc-reg)
     pc-reg
     (1- n))))

(defthm open-FM9001-interpreter
  (and
   (implies (zp n)
            (equal (FM9001-interpreter st pc-reg n)
                   st))
   (implies (not (zp n))
            (equal (FM9001-interpreter st pc-reg n)
                   (FM9001-interpreter
                    (FM9001-step st pc-reg)
                    pc-reg
                    (1- n))))))

(in-theory (disable FM9001-interpreter))

;; FM9001-INTR -- The PC-REG-INPUT is used to determine which register is the
;; PC.

(defund FM9001-intr (st pc-reg-input)
  (if (atom pc-reg-input)
      st
    (FM9001-intr (FM9001-step st (car pc-reg-input))
                 (cdr pc-reg-input))))


