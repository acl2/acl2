;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

;; This file contains events that lead up to the proof that the DE netlist
;; model correctly implements the high-level specification.

(in-package "FM9001")

(include-book "chip")
(include-book "expand-fm9001")

;; ======================================================================

;; OPERATING-INPUTS-P

;; This predicate recognizes mid-level input streams that do not reset the
;; machine, and do not include hold requests.

(defun operating-inputs-p (inputs n)
  (declare (xargs :guard (and (true-list-listp inputs)
                              (natp n))))
  (if (zp n)
      t
    (and (equal (reset--input (car inputs)) t)
         (equal (hold--input (car inputs)) t)
         (bvp (pc-reg-input (car inputs)))
         (equal (len (pc-reg-input (car inputs))) 4)
         (operating-inputs-p (cdr inputs) (1- n)))))

(defthm open-operating-inputs-p
  (and
   (implies (zp n)
            (equal (operating-inputs-p inputs n)
                   t))
   (implies (not (zp n))
            (equal (operating-inputs-p inputs n)
                   (and (equal (reset--input (car inputs)) t)
                        (equal (hold--input (car inputs)) t)
                        (bvp (pc-reg-input (car inputs)))
                        (equal (len (pc-reg-input (car inputs))) 4)
                        (operating-inputs-p (cdr inputs) (1- n)))))))

(in-theory (disable operating-inputs-p))

;; This lemma relates our two predicates on the input streams.

(defthm operating-inputs-p-implies-run-inputs-p
  (implies (operating-inputs-p inputs n)
           (run-inputs-p inputs n))
  :hints (("Goal" :in-theory (enable operating-inputs-p run-inputs-p))))

;; (defthm operating-inputs-p-+
;;   (implies (and (natp m)
;;                 (natp n))
;;            (equal (operating-inputs-p inputs (+ n m))
;;                   (and (operating-inputs-p inputs n)
;;                        (operating-inputs-p (nthcdr n inputs) m)))))

(defthm operating-inputs-p-plus
  (implies (and (natp m)
                (natp n))
           (equal (operating-inputs-p inputs (plus n m))
                  (and (operating-inputs-p inputs n)
                       (operating-inputs-p (nthcdr n inputs) m))))
  :hints (("Goal" :in-theory (enable plus))))

(defthm operating-inputs-p-1
  (implies (and (operating-inputs-p inputs n)
                (not (zp n)))
           (operating-inputs-p inputs 1)))

(defthm operating-inputs-p-implies-hold--input
  (implies (and (operating-inputs-p inputs n)
                (not (zp n)))
           (equal (hold--input (car inputs))
                  t)))

;; ======================================================================

;; MICROCYCLES st
;; TOTAL-MICROCYCLES st inputs n

;; Given a low-level machine state at the beginning of the instruction
;; execution cycle, MICROCYCLES computes the number of clock cycles
;; necessary to excute the instruction, given that the machine is
;; neither reset nor held.  MICROCYCLES assumes that the processor is in
;; state FETCH1.  Notice that in state FETCH1 the instruction resides in
;; memory.

;; TOTAL-MICROCYCLES computes the number of clock cycles needed to
;; execute N instructions, again assuming that the machine is neither
;; reset nor held.  Notice here that it is necessary to simulate each
;; instruction.

(defun microcycles (st)
  (let ((machine-state (caar st))
        (mem-state (caadr st)))
    (let ((regs             (car machine-state))
          (flags            (cadr machine-state))
          (pc-reg           (caddr (cddddr (cddddr machine-state))))
          (mem              (car mem-state))
          (mem-clock        (caddr mem-state)))
      (let ((instr (read-mem (read-mem (strip-cars pc-reg)
                                       (caar regs))
                             mem)))
        (t_fetch1 mem-clock instr (strip-cars flags))))))

(defun total-microcycles (st inputs n)
  (if (zp n)
      0
    (let ((microcycles (microcycles st)))
      (let ((new-state (run-fm9001 st inputs microcycles)))
        (plus microcycles
              (total-microcycles
               new-state
               (nthcdr microcycles inputs)
               (1- n)))))))

(defthm open-total-microcycles
  (and
   (implies (zp n)
            (equal (total-microcycles st inputs n)
                   0))
   (implies (not (zp n))
            (equal (total-microcycles st inputs n)
                   (let ((microcycles (microcycles st)))
                     (let ((new-state (run-fm9001 st inputs microcycles)))
                       (plus microcycles
                             (total-microcycles
                              new-state
                              (nthcdr microcycles inputs)
                              (1- n))))))))
  :hints (("Goal" :in-theory (disable microcycles))))

(in-theory (disable total-microcycles))

;; ======================================================================

;; MACROCYCLE-INVARIANT st pc

;; This is an invariant about the state of the machine at the beginning of
;; the instruction execution cycle:  all of the internal registers are
;; Boolean and properly sized; the machine is in state FETCH1 (ready to
;; execute an instruction);  the ADDR-OUT register contains the program
;; counter;  there are no pending writes in the register file;  HOLD-
;; and RESET- are not asserted;  the PC-REG is equal to (and remains equal
;; to) the specified PC; and the memory is well-formed and in a quiescent
;; state.

;; This is an important invariant; one of the more important proofs that
;; follows states that if we begin in this state, and run for
;; (MICROCYCLES state), then we will reach a state recognized by this
;; invariant.  This is the basis for the inductive proof that the
;; low-level machine implements the behavioral specification.

(defun macrocycle-invariant (st pc)
  (let ((machine-state (caar st))
        (mem-state (caadr st)))
    (b* ((regs             (car machine-state))
         (flags            (cadr machine-state))
         (a-reg            (caddr machine-state))
         (b-reg            (cadddr machine-state))
         (i-reg            (car (cddddr machine-state)))
         (data-out         (cadr (cddddr machine-state)))
         (addr-out         (caddr (cddddr machine-state)))
         (last-reset-      (cadddr (cddddr machine-state)))
         (last-dtack-      (car (cddddr (cddddr machine-state))))
         (last-hold-       (cadr (cddddr (cddddr machine-state))))
         (pc-reg           (caddr (cddddr (cddddr machine-state))))
         (cntl-state       (cadddr (cddddr (cddddr machine-state))))
         (mem              (car mem-state))
         (mem-cntl         (cadr mem-state))
         (?mem-clock       (caddr mem-state))
         (mem-count        (cadddr mem-state))
         (?mem-dtack       (car (cddddr mem-state)))
         (mem-last-rw-     (cadr (cddddr mem-state)))
         (mem-last-address (caddr (cddddr mem-state)))
         (mem-last-data    (cadddr (cddddr mem-state))))
      (b* ((regs-regs    (car regs))
           (regs-we      (cadr regs))
           (regs-data    (caddr regs))
           (regs-address (cadddr regs)))
        (and
         (all-ramp-mem 4 (car regs-regs))
         (memory-okp 4 32 (car regs-regs))
         (equal (car regs-we) nil)
         (bvp (strip-cars regs-data))
         (true-listp regs-data) (equal (len regs-data) 32)
         (bvp (strip-cars regs-address))
         (true-listp regs-address) (equal (len regs-address) 4)
         (bvp (strip-cars flags))
         (len-1-true-listp flags) (equal (len flags) 4)
         (len-1-true-listp a-reg)
         (equal a-reg (pairlis$
                       (read-regs (strip-cars pc-reg) regs)
                       nil))
         (bvp (strip-cars b-reg))
         (len-1-true-listp b-reg) (equal (len b-reg) 32)
         (bvp (strip-cars i-reg))
         (len-1-true-listp i-reg) (equal (len i-reg) 32)
         (bvp (strip-cars data-out))
         (len-1-true-listp data-out) (equal (len data-out) 32)
         ;; (len-1-true-listp addr-out)
         ;; (equal addr-out (pairlis$
         ;;                  (read-regs (strip-cars pc-reg) regs)
         ;;                  nil))
         (equal addr-out a-reg)
         (equal (car last-reset-) t)
         (booleanp (car last-dtack-))
         (equal (car last-hold-) t)
         (bvp (strip-cars pc-reg))
         (len-1-true-listp pc-reg) (equal (len pc-reg) 4)
         (equal pc-reg pc)
         (true-listp cntl-state)
         (equal cntl-state
                (pairlis$ (cv_fetch1 mem-last-rw-
                                     (strip-cars pc-reg)
                                     (strip-cars i-reg)
                                     (strip-cars flags)
                                     (strip-cars pc-reg))
                          nil))
         (memory-okp 32 32 mem)
         (equal mem-cntl 0)
         (acl2-numberp mem-count)
         (booleanp mem-last-rw-)
         (bvp mem-last-address) (equal (len mem-last-address) 32)
         (true-listp mem-last-data)
         (equal (len mem-last-data) 32))))))

(defthm len-cv_fetch1
  (equal (len (cv_fetch1 rw- regs-address i-reg flags pc-reg))
         (+ 36 (len pc-reg)))
  :hints (("Goal" :in-theory (enable cv_fetch1))))

(defthm macrocycle-invariant==>chip-system-invariant$help
  (let ((st (list (list
                   (list
                    (list regs-regs regs-we regs-data regs-address)
                    flags a-reg b-reg i-reg
                    data-out addr-out
                    last-reset- last-dtack- last-hold-
                    pc-reg cntl-state))
                  (list
                   (list mem cntl clock count dtack
                         last-rw- last-address last-data)))))
    (implies (macrocycle-invariant st pc)
             (chip-system-invariant st)))
  :hints (("Goal" :in-theory (enable chip-system-invariant))))

(defthm macrocycle-invariant==>chip-system-invariant
  (implies (and (fm9001-state-structure st)
                (macrocycle-invariant st pc))
           (chip-system-invariant st))
  :hints (("Goal"
           :in-theory (disable car-cdr-elim
                               macrocycle-invariant
                               fm9001-state-as-a-list)
           :use fm9001-state-as-a-list)))

;; MACROCYCLE-INVARIANT* is introduced to delay opening up the function
;; until the low-level machine has been completely rewritten. This should
;; save a tremendous amount of time in the coming proof.

(defun macrocycle-invariant* (st pc)
  (macrocycle-invariant st pc))

(defthm macrocycle-invariant*=macrocycle-invariant
  (equal (macrocycle-invariant* (cons x y) pc)
         (macrocycle-invariant (cons x y) pc))
  :hints (("Goal" :in-theory (disable macrocycle-invariant))))

(in-theory (disable macrocycle-invariant*))

(encapsulate
  ()

  (local
   (defthm not-caadr-write-regs-nil
     (not (caadr (write-regs nil address regs data)))
     :hints (("Goal" :in-theory (enable write-regs)))))

  (defthm macrocycle-invariant-is-invariant$help
    (let ((st (list (list
                     (list
                      (list regs-regs regs-we regs-data regs-address)
                      flags a-reg b-reg i-reg
                      data-out addr-out
                      last-reset- last-dtack- last-hold-
                      pc-reg cntl-state))
                    (list
                     (list mem cntl clock count dtack
                           last-rw- last-address last-data)))))
      (let ((microcycles (microcycles st)))
        (implies
         (and (macrocycle-invariant st pc)
              (operating-inputs-p inputs microcycles))
         (macrocycle-invariant* (run-fm9001 st inputs microcycles)
                                pc))))
    :hints (("Goal"
             :in-theory (e/d (not* binary-and* binary-or*)
                             (fm9001-step-theory
                              true-listp-read-mem-of-memory-properp-32
                              true-listp-read-mem-of-memory-properp
                              bvp-cvzbv
                              booleanp-a-immediate-p
                              acl2::true-listp-nthcdr-type-prescription
                              nthcdr-of-len-l
                              booleanp-set-some-flags
                              default-car
                              bvp-set-flags
                              default-cdr
                              nthcdr
                              true-listp
                              bvp-nthcdr
                              read-regs=read-mem-write-mem
                              (:type-prescription
                               bvp-read-mem-of-memory-okp-32)
                              bvp-read-mem-of-memory-okp
                              true-listp-write-mem
                              zp-open
                              pairlis$
                              plus (plus)
                              add1 (add1)
                              nfix
                              open-run-inputs-p
                              open-run-inputs-p-add1
                              open-operating-inputs-p))))))

(defthm macrocycle-invariant-is-invariant
  (implies
   (and (fm9001-state-structure st)
        (macrocycle-invariant st pc)
        (operating-inputs-p inputs (microcycles st)))
   (macrocycle-invariant (run-fm9001 st inputs (microcycles st))
                         pc))
  :hints (("Goal"
           :in-theory (e/d (macrocycle-invariant*)
                           (macrocycle-invariant
                            t_fetch1
                            strip-cars
                            microcycles))
           :use (:instance
                 macrocycle-invariant-is-invariant$help
                 (regs-regs        (caaaar st))
                 (regs-we          (car (cdaaar st)))
                 (regs-data        (cadr (cdaaar st)))
                 (regs-address     (caddr (cdaaar st)))
                 (flags            (cadaar st))
                 (a-reg            (car (cddaar st)))
                 (b-reg            (cadr (cddaar st)))
                 (i-reg            (caddr (cddaar st)))
                 (data-out         (cadddr (cddaar st)))
                 (addr-out         (car (cddddr (cddaar st))))
                 (last-reset-      (cadr (cddddr (cddaar st))))
                 (last-dtack-      (caddr (cddddr (cddaar st))))
                 (last-hold-       (cadddr (cddddr (cddaar st))))
                 (pc-reg           (car (cddddr (cddddr (cddaar st)))))
                 (cntl-state       (cadr (cddddr (cddddr (cddaar st)))))
                 (mem              (car (caadr st)))
                 (cntl             (car (cdaadr st)))
                 (clock            (cadr (cdaadr st)))
                 (count            (caddr (cdaadr st)))
                 (dtack            (car (cddddr (caadr st))))
                 (last-rw-         (cadr (cddddr (caadr st))))
                 (last-address     (caddr (cddddr (caadr st))))
                 (last-data        (cadddr (cddddr (caadr st))))))))

;; ======================================================================

;; MAP-UP

;; Maps a low-level state to a high-level state.

(defun p-map-up (p-st)
  (list (caar (regs p-st))
        (strip-cars (flags p-st))))

(defun mem-map-up (mem-st)
  (car mem-st))

(defun map-up (st)
  (let ((p-st   (caar  st))
        (mem-st (caadr st)))
    (list
     (p-map-up p-st)
     (mem-map-up mem-st))))

;; This rather obvious fact is stated in a non-obvious way.  We will be
;; "mapping-up" a low-level simulation, i.e., a call of RUN-FM9001.  If MAP-UP
;; opens before RUN-FM9001 is completely rewritten to a new state, i.e., a
;; CONS, then we will be rewriting RUN-FM9001 3 times for each path through the
;; state diagram.  By stating the lemma this way, we wait until RUN-FM9001 is
;; completely rewritten before extracting the 3 interesting bits, thus saving
;; massive amounts of work.

(defthm open-map-up
  (let ((st (cons x y)))
    (equal (map-up st)
           (let ((p-st (caar st))
                 (mem-st (caadr st)))
             (list
              (list (caar (regs p-st))
                    (strip-cars (flags p-st)))
              (car mem-st))))))

(in-theory (disable map-up))

;; ======================================================================

;; MIDDLE=HIGH

;; This is the proof that the architecture implements the specification for the
;; execution of a single instruction.  The time abstraction between the
;; behavioral-level specification and the implementation is a critical part of
;; this proof; that is, the implementation requires a number of clock cycles to
;; execute a single instruction while the behavioral-level specification
;; executes just one instruction.

;; FM9001-STEP* is introduced to delay opening up the high-level specification
;; until the low-level machine has been completely rewritten.  This saves a
;; fair amount of time in the coming proof.

(defun fm9001-step* (st pc-reg)
  (fm9001-step st pc-reg))

(defthm fm9001-step*-lemma
  (equal (equal (cons x y)
                (fm9001-step* st pc-reg))
         (equal (cons x y)
                (fm9001-step st pc-reg))))

(in-theory (disable fm9001-step*))

(defthm middle=high$help
  (let ((st (list (list
                   (list
                    (list regs-regs regs-we regs-data regs-address)
                    flags a-reg b-reg i-reg
                    data-out addr-out
                    last-reset- last-dtack- last-hold-
                    pc-reg cntl-state))
                  (list
                   (list mem cntl clock count dtack
                         last-rw- last-address last-data)))))
    (let ((microcycles (microcycles st)))
      (implies
       (and (macrocycle-invariant st pc-reg)
            (operating-inputs-p inputs microcycles))
       (equal (map-up
               (run-fm9001 st inputs microcycles))
              (fm9001-step* (list (list (car regs-regs)
                                        (strip-cars flags))
                                  mem)
                            (strip-cars pc-reg))))))
  :hints (("Goal"
           :in-theory
           (union-theories
            '((:COMPOUND-RECOGNIZER BOOLEANP-COMPOUND-RECOGNIZER)
              (:COMPOUND-RECOGNIZER ACL2::NATP-COMPOUND-RECOGNIZER)
              (:COMPOUND-RECOGNIZER ACL2::ZP-COMPOUND-RECOGNIZER)
              (:CONGRUENCE ACL2::IFF-IMPLIES-EQUAL-BOOL-FIX-1)
              (:DEFINITION B-AND)
              (:DEFINITION B-OR)
              (:DEFINITION BINARY-AND*)
              (:DEFINITION BINARY-OR*)
              (:DEFINITION BV2P)
              (:DEFINITION CV-HYPS)
              (:DEFINITION DOUBLE-REWRITE)
              (:DEFINITION FLAGS)
              (:DEFINITION FLAGS-HYPS)
              (:DEFINITION FM9001-ALU-OPERATION)
              (:DEFINITION FM9001-FETCH)
              (:DEFINITION FM9001-OPERAND-A)
              (:DEFINITION FM9001-OPERAND-B)
              (:DEFINITION FM9001-STEP)
              (:DEFINITION IF*)
              (:DEFINITION LEN)
              (:DEFINITION MACROCYCLE-INVARIANT)
              (:DEFINITION MICROCYCLES)
              (:DEFINITION NOT)
              (:DEFINITION NOT*)
              (:DEFINITION REGFILE-OKP)
              (:DEFINITION REGS)
              (:DEFINITION T_FETCH1)
              (:DEFINITION T_READA0)
              (:DEFINITION T_READB0)
              (:DEFINITION T_REGA)
              (:DEFINITION T_REGB)
              (:DEFINITION T_SEFA0)
              (:DEFINITION T_SEFB0)
              (:DEFINITION T_SEFB1)
              (:DEFINITION T_UPDATE)
              (:DEFINITION T_WRITE0)
              (:DEFINITION WRITE-REGS)
              (:EXECUTABLE-COUNTERPART <)
              (:EXECUTABLE-COUNTERPART B-AND)
              (:EXECUTABLE-COUNTERPART B-OR)
              (:EXECUTABLE-COUNTERPART BINARY-+)
              (:EXECUTABLE-COUNTERPART BINARY-AND*)
              (:EXECUTABLE-COUNTERPART BINARY-OR*)
              (:EXECUTABLE-COUNTERPART ACL2::BOOL-FIX$INLINE)
              (:EXECUTABLE-COUNTERPART BOOLEANP)
              (:EXECUTABLE-COUNTERPART CAR)
              (:EXECUTABLE-COUNTERPART CONS)
              (:EXECUTABLE-COUNTERPART EQUAL)
              (:EXECUTABLE-COUNTERPART F-BUF)
              (:EXECUTABLE-COUNTERPART LEN)
              (:EXECUTABLE-COUNTERPART NATP)
              (:EXECUTABLE-COUNTERPART NFIX)
              (:EXECUTABLE-COUNTERPART NOT*)
              (:REWRITE ALL-RAMP-MEM->RAMP-MEM)
              (:REWRITE ALL-RAMP-MEM-AFTER-WRITE-MEM)
              (:REWRITE ACL2::BOOL-FIX-UNDER-IFF)
              (:REWRITE BVP-BV)
              (:REWRITE BVP-IS-TRUE-LISTP)
              (:REWRITE BVP-LEN-V-INC-V-DEC)
              (:REWRITE BVP-READ-MEM-OF-MEMORY-OKP-32)
              (:REWRITE BVP-RN-A)
              (:REWRITE BVP-RN-B)
              (:REWRITE BVP-SIGN-EXTEND)
              (:REWRITE BVP-UPDATE-FLAGS)
              (:REWRITE BVP-V-ALU)
              (:REWRITE BVP-V-ALU-1)
              (:REWRITE BVP-V-FOURFIX)
              (:REWRITE CAR-CONS)
              (:REWRITE CAR-OF-CONSP-OR-NIL)
              (:REWRITE CDR-CONS)
              (:REWRITE CDR-OF-CONSP-OR-NIL)
              (:REWRITE DOUBLE-CONSP-OR-NIL-CANCELED)
              (:REWRITE FETCH0->FETCH0$SIM0)
              (:REWRITE FETCH0->FETCH0$SIM2)
              (:REWRITE FETCH1->DECODE$SIM)
              (:REWRITE FM9001-STEP*-LEMMA)
              (:REWRITE IF*-REWRITE)
              (:REWRITE LEN-1-TRUE-LISTP-PAIRLIS$-WITH-NIL)
              (:REWRITE LEN-BV)
              (:REWRITE LEN-PAIRLIS$)
              (:REWRITE LEN-READ-MEM-OF-MEMORY-PROPERP-32)
              (:REWRITE LEN-RN-A)
              (:REWRITE LEN-RN-B)
              (:REWRITE LEN-SIGN-EXTEND)
              (:REWRITE LEN-STRIP-CARS)
              (:REWRITE LEN-UPDATE-FLAGS)
              (:REWRITE LEN-V-ALU)
              (:REWRITE LEN-V-ALU-1)
              (:REWRITE MEMORY-OKP-AFTER-WRITE-MEM)
              (:REWRITE MEMORY-OKP==>MEMORY-PROPERP)
              (:REWRITE NOT-SET-SOME-FLAGS-UPDATE-FLAGS)
              (:REWRITE NTH-0-CONS)
              (:REWRITE NTH-ADD1)
              (:REWRITE OPEN-MAP-UP)
              (:REWRITE OPERATING-INPUTS-P-IMPLIES-HOLD--INPUT)
              (:REWRITE OPERATING-INPUTS-P-IMPLIES-RUN-INPUTS-P)
              (:REWRITE OPERATING-INPUTS-P-PLUS)
              (:REWRITE PAIRLIS$-STRIP-CARS)
              (:REWRITE READ-MEM-WRITE-MEM)
              (:REWRITE READ-REGS=READ-MEM)
              (:REWRITE READ-REGS=READ-MEM-WRITE-MEM)
              (:REWRITE READA0->READA3$SIM)
              (:REWRITE READB0->READB3$SIM)
              (:REWRITE REG-DIRECT->NOT-REG-INDIRECT)
              (:REWRITE REGA->REGA$SIM)
              (:REWRITE REGB->UPDATE$SIM)
              (:REWRITE RUN-FM9001-PLUS)
              (:REWRITE SEFA0->SEFA1$SIM)
              (:REWRITE SEFB0->SEFB1$SIM)
              (:REWRITE SEFB1->SEFB1$SIM)
              (:REWRITE STRIP-CARS-PAIRLIS$)
              (:REWRITE UNARY-OP-CODE-P-OP-CODE->V-ALU=V-ALU-1)
              (:REWRITE UPDATE->UPDATE$SIM)
              (:REWRITE V-IFF=EQUAL)
              (:REWRITE V-THREEFIX-IDEMPOTENCE)
              (:REWRITE WRITE-REGS-NIL-BV-CROCK)
              (:REWRITE WRITE0->WRITE3$SIM)
              (:TYPE-PRESCRIPTION ALL-RAMP-MEM)
              (:TYPE-PRESCRIPTION BOOLEANP-C-FLAG)
              (:TYPE-PRESCRIPTION BOOLEANP-POST-INC-P)
              (:TYPE-PRESCRIPTION BOOLEANP-PRE-DEC-P)
              (:TYPE-PRESCRIPTION BOOLEANP-REG-DIRECT-P)
              (:TYPE-PRESCRIPTION BOOLEANP-STORE-RESULTP)
              (:TYPE-PRESCRIPTION BOOLEANP-UNARY-OP-CODE-P)
              (:TYPE-PRESCRIPTION BVP)
              (:TYPE-PRESCRIPTION LEN-1-TRUE-LISTP)
              (:TYPE-PRESCRIPTION LEN-1-TRUE-LISTP-PAIRLIS$-WITH-NIL)
              (:TYPE-PRESCRIPTION MEMORY-OKP)
              (:TYPE-PRESCRIPTION NATP-ADD1)
              (:TYPE-PRESCRIPTION NATP-PLUS)
              (:TYPE-PRESCRIPTION NFIX)
              (:TYPE-PRESCRIPTION OPERATING-INPUTS-P)
              (:TYPE-PRESCRIPTION PAIRLIS$)
              (:TYPE-PRESCRIPTION READ-MEM)
              (:TYPE-PRESCRIPTION RN-A)
              (:TYPE-PRESCRIPTION RN-B)
              (:TYPE-PRESCRIPTION SIGN-EXTEND)
              (:TYPE-PRESCRIPTION T_READA0)
              (:TYPE-PRESCRIPTION T_READB0)
              (:TYPE-PRESCRIPTION T_REGA)
              (:TYPE-PRESCRIPTION T_SEFA0)
              (:TYPE-PRESCRIPTION T_SEFB0)
              (:TYPE-PRESCRIPTION UPDATE-FLAGS)
              (:TYPE-PRESCRIPTION V-DEC)
              (:TYPE-PRESCRIPTION V-INC))

            (theory 'minimal-theory)))))

(defthm macrocycle-invariant==>pc-reg
  (implies (macrocycle-invariant st pc-reg)
           (equal (pc-reg (caar st)) pc-reg))
  :hints (("Goal" :in-theory (enable macrocycle-invariant pc-reg))))

(local
 (defthm middle=high-aux
   (equal (nth 8 (cddr (car (car st))))
          (caddr (cddddr (cddddr (car (car st))))))))

(defthm middle=high
  (implies
   (and (fm9001-state-structure st)
        (macrocycle-invariant st pc)
        (operating-inputs-p inputs (microcycles st)))
   (equal (map-up
           (run-fm9001 st inputs (microcycles st)))
          (fm9001-step (map-up st)
                       (strip-cars pc))))
  :hints (("Goal"
           :in-theory (e/d (map-up regs flags pc-reg
                                   fm9001-step*
                                   open-nth)
                           (macrocycle-invariant
                            t_fetch1
                            microcycles))
           :use ((:instance
                  macrocycle-invariant==>pc-reg
                  (pc-reg pc))
                 (:instance
                  middle=high$help
                  (regs-regs        (caaaar st))
                  (regs-we          (car (cdaaar st)))
                  (regs-data        (cadr (cdaaar st)))
                  (regs-address     (caddr (cdaaar st)))
                  (flags            (cadaar st))
                  (a-reg            (car (cddaar st)))
                  (b-reg            (cadr (cddaar st)))
                  (i-reg            (caddr (cddaar st)))
                  (data-out         (cadddr (cddaar st)))
                  (addr-out         (car (cddddr (cddaar st))))
                  (last-reset-      (cadr (cddddr (cddaar st))))
                  (last-dtack-      (caddr (cddddr (cddaar st))))
                  (last-hold-       (cadddr (cddddr (cddaar st))))
                  (pc-reg           (car (cddddr (cddddr (cddaar st)))))
                  (cntl-state       (cadr (cddddr (cddddr (cddaar st)))))
                  (mem              (car (caadr st)))
                  (cntl             (car (cdaadr st)))
                  (clock            (cadr (cdaadr st)))
                  (count            (caddr (cdaadr st)))
                  (dtack            (car (cddddr (caadr st))))
                  (last-rw-         (cadr (cddddr (caadr st))))
                  (last-address     (caddr (cddddr (caadr st))))
                  (last-data        (cadddr (cddddr (caadr st)))))))))

;; ======================================================================

;; Final Correctness Proofs

;; The proof that the register-transfer specification implements the
;; behavioral specification.

(defthm FM9001-interpreter-correct
  (let ((clock-cycles (total-microcycles st inputs instructions)))
    (implies
     (and (fm9001-state-structure st)
          (macrocycle-invariant st pc)
          (operating-inputs-p inputs clock-cycles))
     (equal (map-up
             (run-fm9001 st inputs clock-cycles))
            (FM9001-interpreter (map-up st)
                                (strip-cars pc)
                                instructions))))
  :hints (("Goal"
           :in-theory (e/d (total-microcycles)
                           (macrocycle-invariant microcycles)))))

;; The above, and CHIP-SYSTEM=RUN-FM9001 (see "chip.lisp"), yields this
;; lemma that the DUAL-EVAL netlist implements the FM9001 specification.

(defthm chip-system=fm9001-interpreter
  (let ((rtl-inputs (map-up-inputs inputs)))
    (let ((clock-cycles (total-microcycles st rtl-inputs instructions)))
      (implies
       (and (chip-system& netlist)
            (fm9001-state-structure st)
            (macrocycle-invariant st pc)
            (chip-system-operating-inputs-p inputs clock-cycles)
            (operating-inputs-p rtl-inputs clock-cycles))
       (equal (map-up
               (de-sim-n 'chip-system inputs st netlist clock-cycles))
              (fm9001-interpreter (map-up st)
                                  (strip-cars pc)
                                  instructions)))))
  :hints (("Goal"
           :in-theory (disable macrocycle-invariant))))

;; Note that when register 15 is the program counter, FM9001-INTERPRETER
;; is the same as FM9001.

(defthm fm9001=fm9001-interpreter
  (equal (fm9001 st n)
         (fm9001-interpreter st (make-list 4 :initial-element t) n))
  :hints (("Goal" :in-theory (enable fm9001))))

;; MAP-DOWN-RELATION simply states that the register file, flags, and memory of
;; the low-level-state are equal to the corresponding things in the high-level
;; state.

(defun map-down-relation (high-level-state low-level-state)
  (let ((high-level-p-state   (car high-level-state))
        (high-level-mem-state (cadr high-level-state))
        (low-level-p-state   (caar low-level-state))
        (low-level-mem-state (caadr low-level-state)))
    (and (equal (regs high-level-p-state)
                (caar (regs low-level-p-state)))
         (equal (flags high-level-p-state)
                (strip-cars (flags low-level-p-state)))
         (equal high-level-mem-state
                (car low-level-mem-state)))))

;; A minimal hypothesis about the high-level-state.

(defun high-level-state-structure (st)
  (and (true-listp st)
       (true-listp (car st))
       (equal (len (car st)) 2)
       (equal (len st) 2)))

(defthm high-level-state-as-a-list
  (implies (high-level-state-structure st)
           (equal (list (list (caar st)
                              (cadar st))
                        (cadr st))
                  st))
  :hints (("Goal" :in-theory (enable open-len))))

(defthm map-down-relation-lemma
  (implies
   (and (high-level-state-structure high-level-state)
        (map-down-relation high-level-state low-level-state))
   (equal (map-up low-level-state)
          high-level-state))
  :hints (("Goal"
           :use (:instance high-level-state-as-a-list
                           (st high-level-state))
           :in-theory (enable map-up regs flags open-nth))))

(in-theory (disable map-down-relation high-level-state-structure))

;; These two lemmas mimic the 2 major results above, except that we use
;; MAP-DOWN-RELATION to relate the high- and low-level states rather than the
;; MAP-UP function.

(defthm FM9001-interpreter-correct$map-down
  (implies
   (and (high-level-state-structure high-level-state)
        (map-down-relation high-level-state low-level-state)
        (fm9001-state-structure low-level-state)
        (macrocycle-invariant low-level-state pc)
        (operating-inputs-p
         inputs (total-microcycles low-level-state inputs n)))
   (equal (map-up
           (run-fm9001 low-level-state
                       inputs
                       (total-microcycles low-level-state inputs n)))
          (FM9001-interpreter high-level-state
                              (strip-cars pc)
                              n)))
  :hints (("Goal"
           :in-theory (theory 'minimal-theory)
           :use (map-down-relation-lemma
                 (:instance fm9001-interpreter-correct
                            (st low-level-state)
                            (instructions n))))))

;; ======================================================================

;; FM9001=CHIP-SYSTEM

;; The proofs that follow were originally what we thought of as the "final"
;; correctness results.  On further analysis, these really aren't very
;; satisfying because they presume that any high-level state can be mapped down
;; to a very specific low-level-state.  (You *could* do it with the scan
;; chain.)  All we can really guarantee about the machine is that you can reset
;; it, and then move forward at the end of the reset sequence.  We leave these
;; events here for historical interest.

(defun fm9001-machine-statep (p-st)
  (let ((regs (car p-st))
        (flags (cadr p-st)))
    (and (true-listp p-st)
         (equal (len p-st) 2)
         (all-ramp-mem 4 regs)
         (memory-okp 4 32 regs)
         (bvp flags)
         (equal (len flags) 4))))

(defun fm9001-statep (st)
  (let ((p-st    (car  st))
        (memory  (cadr st)))
    (and (true-listp st)
         (equal (len st) 2)
         (fm9001-machine-statep p-st)
         (memory-okp 32 32 memory))))

(defthm fm9001-statep-as-a-list
  (implies (fm9001-statep st)
           (equal (list (list (caar st)
                              (cadar st))
                        (cadr st))
                  st))
  :hints (("Goal" :in-theory (enable open-len))))

(defun p-map-down (p-st)
  (let ((regs  (car  p-st))
        (flags (cadr p-st)))
    (list
     (list (list regs)
           '(nil)
           (pairlis$ (make-list 32) nil)
           (pairlis$ (make-list 4 :initial-element t) nil))
     (pairlis$ flags nil)
     (pairlis$
      (read-mem (make-list 4 :initial-element t) regs) ; a-reg
      nil)
     (pairlis$ (make-list 32) nil)  ; b-reg
     (pairlis$ (make-list 32) nil)  ; i-reg
     (pairlis$ (make-list 32) nil)  ; data-out
     (pairlis$
      (read-mem (make-list 4 :initial-element t) regs) ; addr-out
      nil)
     '(t)                                            ; reset
     '(t)                                            ; dtack
     '(t)                                            ; hold
     (pairlis$ (make-list 4 :initial-element t) nil)  ; pc-reg
     (pairlis$
      (cv_fetch1 t ; cntl-state
                 (list t t t t)
                 (make-list 32)
                 (list t nil nil nil)
                 (make-list 4 :initial-element t))
      nil))))

(defun mem-map-down (memory)
  (list memory 0 0 0 t t
        (make-list 32)
        (make-list 32 :initial-element *X*)))

(defun map-down (st)
  (let ((p-st    (car  st))
        (memory  (cadr st)))
    (list
     (list (p-map-down p-st))
     (list (mem-map-down memory)))))

(defthm map-up-inverts-map-down
  (implies (fm9001-statep st)
           (equal (map-up (map-down st)) st))
  :hints (("Goal" :in-theory (enable regs flags))))

(defthm fm9001-statep-implies-fm9001-state-structure
  (implies (fm9001-statep st)
           (fm9001-state-structure (map-down st)))
  :hints (("Goal" :in-theory (enable fm9001-state-structure))))

(defthm fm9001-statep-implies-macrocycle-invariant-lemma1
  (equal (equal (cv_fetch1 t
                           (make-list 4 :initial-element t)
                           (make-list 32)
                           x
                           (make-list 4 :initial-element t))
                (cv_fetch1 t
                           (list t t t t)
                           (make-list 32)
                           (list t nil nil nil)
                           (make-list 4 :initial-element t)))
         t)
  :hints (("Goal" :in-theory (enable cv_fetch1 carry-in-help c-flag))))

(defthm fm9001-statep-implies-macrocycle-invariant
  (implies (fm9001-statep st)
           (macrocycle-invariant
            (map-down st)
            (pairlis$ (make-list 4 :initial-element t)
                      nil)))
  :hints (("Goal"
           :use (:instance
                 fm9001-statep-implies-macrocycle-invariant-lemma1
                 (x (cadar st)))
           :in-theory (disable fm9001-statep-implies-macrocycle-invariant-lemma1))))

(defthm fm9001=chip-system
  (implies (and (chip-system& netlist)
                (fm9001-statep st)
                (chip-system-operating-inputs-p
                 inputs
                 (total-microcycles (map-down st)
                                    (map-up-inputs inputs)
                                    n))
                (operating-inputs-p
                 (map-up-inputs inputs)
                 (total-microcycles (map-down st)
                                    (map-up-inputs inputs)
                                    n)))
           (equal (fm9001 st n)
                  (map-up
                   (de-sim-n
                    'chip-system inputs
                    (map-down st)
                    netlist
                    (total-microcycles (map-down st)
                                       (map-up-inputs inputs)
                                       n)))))
  :hints (("Goal"
           :use (:instance chip-system=fm9001-interpreter
                           (st (map-down st))
                           (instructions n)
                           (pc (pairlis$
                                (make-list 4 :initial-element t)
                                nil)))
           :in-theory (union-theories
                       '(strip-cars-pairlis$
                         true-listp-make-list
                         fm9001=fm9001-interpreter
                         fm9001-statep-implies-fm9001-state-structure
                         fm9001-statep-implies-macrocycle-invariant
                         map-up-inverts-map-down)
                       (theory 'minimal-theory)))))

(defun no-holds-reset-or-test (i c)
  (and (chip-system-operating-inputs-p i c)
       (operating-inputs-p (map-up-inputs i) c)))

;; Here is an informal statement of the following lemma,
;; FM9001=CHIP-SYSTEM-SUMMARY, which is the chief result proved about the
;; FM9001.  Let H be the hardware netlist that we have constructed for the
;; FM9001.  The lemma states that for each FM9001 user-visible state, S, and
;; for each positive integer, N, there exists a positive integer C such that
;; the result of running the user-model of the FM9001 (the function FM9001) N
;; steps can instead be obtained by simulating H and S under the DE semantics
;; for C steps.  In precisely stating the theorem, we arrange to supply the DE
;; semantics with a transform (obtained with MAP-DOWN) of S, and afterwards we
;; do a reverse transformation (with MAP-UP) to obtain the final user-visible
;; state.  Futhermore, in making the statement precise we stipulate that the
;; external stimuli, I, to the chip do not enable a hold, a reset, or a test
;; input for the C clock cycles.  The fact that N and C are different reflects
;; the fact that a single FM9001 instruction takes several clock cycles to
;; emulate at the DE netlist level.  The precise statement of this correctness
;; result is:

(defthm fm9001=chip-system-summary
  (let ((h (chip-system$netlist))
        (c (total-microcycles (map-down s) (map-up-inputs i) n)))
    (implies
     (and (fm9001-statep s)
          (no-holds-reset-or-test i c))
     (equal (fm9001 s n)
            (map-up
             (de-sim-n 'chip-system i (map-down s) h c)))))
  :hints (("Goal"
           :use (:instance fm9001=chip-system
                           (st s)
                           (netlist (chip-system$netlist))
                           (inputs i))
           :in-theory (union-theories
                       '(no-holds-reset-or-test
                         check-chip-system$netlist)
                       (theory 'minimal-theory)))))

