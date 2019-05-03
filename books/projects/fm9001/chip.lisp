;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

;; The DE model of the FM9001 chip.

(in-package "FM9001")

(include-book "fm9001-hardware")
(include-book "pad-vectors")

;; ======================================================================

;; CHIP-MODULE

;; The entire chip, sans pads, as a module.

;; INPUTS:
;;
;;    CLK  -- The system clock
;;
;;    TI   -- Test input (Scan in)
;;    TE   -- Test enable (Scan enable)
;;
;;    DTACK-  --  DTACK input
;;    RESET-  --  RESET input
;;    HOLD-   --  HOLD input
;;
;;    DISABLE-REGFILE-   --  Must be high to write enable the register
;;                           file RAM.  During scan-in, DISABLE-REGFILE- is
;;                           held low to avoid spurious writes to the RAM.
;;
;;    TEST-REGFILE-    --  Normally high.  When low, forces the register file
;;                         output mux to pass data directly from the register
;;                         file RAM.
;;
;;    PC-REG-IN[0..3]    --  The PC-REG inputs.
;;
;;    DATA-IN[0..31]  --  The input data bus.  We consider the bus as two
;;                        unidirectional busses at this level.
;;
;; OUTPUTS:
;;
;;    TO      --  Test Output (Scan out)
;;    TIMING  --  The net corresponding to the longest combinational path.
;;                Used to verify the speed of the device.  This is currently
;;                the ZERO flag computed by the ALU.
;;
;;    HDACK-   --  Hold Acknowledge
;;
;;    EN-ADDR-OUT-  -- The inverse of HDACK-, with high drive for ADDR-BUS
;;                     and memory control lines.
;;
;;    RW-      --  Memory control lines  (High Drive for DATA-OUT)
;;    STROBE-
;;
;;    ADDR-OUT[0..31]  --  Address bus
;;    DATA-OUT[0..31]  --  Data output bus
;;
;;    FLAGS[0..3]     --  Observability pins
;;    CNTL-STATE[0..4]
;;    I-REG[28..31]

(module-generator
 chip-module* ()

 'chip-module

 (list* 'clk 'ti 'te 'dtack- 'reset- 'hold-
        'disable-regfile- 'test-regfile-
        (append (sis 'pc-reg-in 0 4) (sis 'data-in 0 32)))

 (list* 'to 'timing 'hdack- 'en-addr-out- 'rw- 'strobe-
        (append (sis 'addr-out 0 32)
                (append (sis 'data-out 0 32)
                        (append (sis 'flags 0 4)
                                (append (sis 'cntl-state 0 5)
                                        (subseq-list (sis 'i-reg 0 32)
                                                     28 32))))))
 ;; States
 '(regs cvnz-flags a-reg b-reg i-reg data-out addr-out
        reset-latch dtack-latch hold-latch
        pc-reg cntl-state)

 (list

  ;; The sequential modules, in specification order except for CNTL-STATE,
  ;; which must appear first since its combinational outputs control the
  ;; combinational output of the register file.

  ;; CNTL-STATE.  Scan TI to (si 'ALU-MPG 6)
  (list 'cntl-state
        (list* 'rw-sig- 'strobe- 'hdack-
               'we-regs 'we-a-reg 'we-b-reg 'we-i-reg
               'we-data-out 'we-addr-out 'we-hold- 'we-pc-reg
               'data-in-select 'dec-addr-out 'select-immediate
               'alu-c 'alu-zero
               (append (sis 'cntl-state 0 5)
                       (append (sis 'we-flags 0 4)
                               (append (sis 'regs-address 0 4)
                                       (append (sis 'alu-op 0 4)
                                               (sis 'alu-mpg 0 7))))))
        (si 'reg 40)
        (list* 'clk 'te-sig 'ti (sis 'next-state 0 40)))

  ;;  REGS.  Scan (si 'ALU-MPG 6) to REGFILE-TO
  (list 'regs
        (cons 'regfile-to (sis 'regfile-out 0 32))
        'regfile
        (list* 'clk 'te-sig (si 'alu-mpg 6)
               'we-regs 'disable-regfile- 'test-regfile-
               (append (sis 'regs-address 0 4) (bv (sis 'alu-bus 0 35)))))

  ;;  FLAGS.  Scan REGFILE-TO to (si 'FLAGS 3)
  (list 'cvnz-flags
        (sis 'flags 0 4)
        'flags
        (list* 'clk 'te-sig 'regfile-to (append (sis 'we-flags 0 4)
                                                (sis 'alu-bus 0 35))))
  ;;  A-REG.  Scan (si 'FLAGS 3) to (si 'A-REG 31)
  (list 'a-reg
        (sis 'a-reg 0 32)
        (si 'we-reg 32)
        (list* 'clk 'we-a-reg 'te-sig (si 'FLAGS 3) (sis 'abi-bus 0 32)))
  ;;  B-REG.  Scan (si 'A-REG 31) to (si 'B-REG 31)
  (list 'b-reg
        (sis 'b-reg 0 32)
        (si 'we-reg 32)
        (list* 'clk 'we-b-reg 'te-sig (si 'a-reg 31) (sis 'abi-bus 0 32)))
  ;;  I-REG.  Scan (si 'B-REG 31) to (si 'I-REG 31)
  (list 'i-reg
        (sis 'i-reg 0 32)
        (si 'we-reg 32)
        (list* 'clk 'we-i-reg 'te-sig (si 'b-reg 31) (sis 'abi-bus 0 32)))
  ;;  DATA-OUT.  Scan (si 'I-REG 31) to (si 'DATA-OUT 31)
  (list 'data-out
        (sis 'data-out 0 32)
        (si 'we-reg 32)
        (list* 'clk 'we-data-out 'te-sig (si 'i-reg 31)
               (bv (sis 'alu-bus 0 35))))
  ;;  ADDR-OUT.  Scan (si 'DATA-OUT 31) to (si 'ADDR-OUT 31)
  (list 'addr-out
        (sis 'addr-out 0 32)
        (si 'we-reg 32)
        (list* 'clk 'we-addr-out 'te-sig (si 'data-out 31)
               (sis 'addr-out-bus 0 32)))
  ;;  RESET.  Scan (si 'ADDR-OUT 31) to LAST-RESET-
  (list 'reset-latch
        '(last-reset- last-reset-inv)
        'fd1s
        (list 'reset- 'clk (si 'addr-out 31) 'te-sig))
  ;;  DTACK.  Scan LAST-RESET- to LAST-DTACK-
  ;;
  ;;  The DTACK- input is ORed with STROBE-, to insure that the DTACK- state
  ;;  is initializable, and remains boolean.
  '(dtack--or (dtack--or-strobe-) b-or (strobe- dtack-))
  (list 'dtack-latch
        '(last-dtack- last-dtack-inv)
        'fd1s
        '(dtack--or-strobe- clk last-reset- te-sig))
  ;;  HOLD.  Scan LAST-DTACK- to LAST-HOLD-
  (list 'hold-latch
        '(last-hold- last-hold-inv)
        'fd1slp
        '(hold- clk we-hold- last-dtack- te-sig))

  ;;  PC-REG.  Scan LAST-HOLD- to (si 'PC-REG 3) [Renamed to TO later].
  (list 'pc-reg
        (sis 'pc-reg 0 4)
        (si 'we-reg 4)
        (list* 'clk 'we-pc-reg 'te-sig 'last-hold- (sis 'pc-reg-in 0 4)))

  ;;  Now, the combinational modules.

  ;;  IMMEDIATE/PASS
  (list 'immediate-pass
        (sis 'reg-bus 0 32)
        'extend-immediate
        (cons 'select-immediate
              (append (a-immediate (sis 'i-reg 0 32))
                      (sis 'regfile-out 0 32))))
  ;;  DEC/PASS
  (list 'dec-pass
        (sis 'addr-out-bus 0 32)
        (si 'dec-pass 32)
        (cons 'dec-addr-out (sis 'reg-bus 0 32)))
  ;;  DATA-IN-MUX
  ;;
  ;;  The data input bus is only selected when DTACK- is asserted, in order to
  ;;  avoid passing garbage onto the ABI-BUS.
  '(mux-cntl (abi-cntl) b-nand (data-in-select last-dtack-inv))
  (list 'data-in-mux
        (sis 'abi-bus 0 32)
        (si 'tv-if (tree-number (make-tree 32)))
        (cons 'abi-cntl (append (sis 'reg-bus 0 32) (sis 'data-in 0 32))))
  ;;  ALU
  (list 'alu
        (sis 'alu-bus 0 35)
        (si 'core-alu (tree-number (make-tree 32)))
        (cons 'alu-c (append (sis 'a-reg 0 32)
                             (append (sis 'b-reg 0 32)
                                     (cons 'alu-zero
                                           (append (sis 'alu-mpg 0 7)
                                                   (sis 'alu-op 0 4)))))))

  ;;  NEXT-STATE
  (list 'next-state
        (sis 'next-state 0 40)
        'next-cntl-state
        (list* 'last-reset- 'last-dtack- 'last-hold- 'rw-sig-
               (append (sis 'cntl-state 0 5)
                       (append (sis 'i-reg 0 32)
                               (append (sis 'flags 0 4)
                                       (append (sis 'pc-reg 0 4)
                                               (sis 'regs-address 0 4)))))))

  ;;  TE is buffered due to its high load.

  '(te-buffer (te-sig) b-buf-pwr (te))

  ;;  RW- is buffered to enable the DATA-OUT pads.

  '(rw-buffer (rw-) b-buf (rw-sig-))

  ;;  ADDR-OUT, RW- and STROBE- drivers are enabled whenever HDACK- is not
  ;;  asserted.

  '(en-addr-out-gate (en-addr-out-) b-not (hdack-))

  ;;  We believe the longest combinational net is the ALU ZERO
  ;;  computation.

  (list 'timing-gate '(timing) 'id (list (si 'alu-bus 2)))

  ;;  Rename the scan out

  (list 'scanout '(to) 'id (list (si 'pc-reg 3))))

 :guard t)

(defund chip-module& (netlist)
  (and (equal (assoc 'chip-module netlist)
              (chip-module*))
       (let ((netlist (delete-to-eq 'chip-module netlist)))
         (and
          (regfile& netlist)
          (flags& netlist)
          (we-reg& netlist 32)
          (we-reg& netlist 4)
          (reg& netlist 40)
          (b-buf-pwr& netlist)
          (extend-immediate& netlist)
          (dec-pass& netlist 32)
          (tv-if& netlist (make-tree 32))
          (core-alu& netlist (make-tree 32))
          (next-cntl-state& netlist)))))

(defun chip-module$netlist ()
  (cons
   (chip-module*)
   (union$ (regfile$netlist)
           (flags$netlist)
           (we-reg$netlist 32)
           (we-reg$netlist 4)
           (reg$netlist 40)
           (extend-immediate$netlist)
           (dec-pass$netlist 32)
           (tv-if$netlist (make-tree 32))
           (core-alu$netlist (make-tree 32))
           (next-cntl-state$netlist)
           *b-buf-pwr*
           :test 'equal)))

;;;  A few crocks for the coming proof.

(defthm equal-len-40-as-collected-nth+subseq
  (implies (and (equal (len l) 40)
                (true-listp l))
           (equal (append (list-as-collected-nth l 16 0)
                          (subseq l 16 40))
                  l))
  :hints (("Goal" :in-theory (enable open-nthcdr))))

(defthm list-as-cntl-state-crock
  (implies (and (true-listp list)
                (equal (len list) 40))
           (equal (list*
                   (rw-              list)
                   (strobe-          list)
                   (hdack-           list)
                   (we-regs          list)
                   (we-a-reg         list)
                   (we-b-reg         list)
                   (we-i-reg         list)
                   (we-data-out      list)
                   (we-addr-out      list)
                   (we-hold-         list)
                   (we-pc-reg        list)
                   (data-in-select   list)
                   (dec-addr-out     list)
                   (select-immediate list)
                   (alu-c            list)
                   (alu-zero         list)
                   (append (major-state list)
                           (append (we-flags list)
                                   (append (regs-address list)
                                           (append (alu-op list)
                                                   (alu-mpg list))))))
                  list))
  :hints (("Goal"
           :use (:instance equal-len-40-as-collected-nth+subseq
                           (l list))
           :in-theory (enable control-vector-accessors
                              open-nthcdr))))

(defthmd reg-40$value-as-cntl-state
  (implies
   (and (reg& netlist 40)
        (true-listp sts)
        (equal (len sts) 40))
   (equal (se (si 'reg 40) args sts netlist)
          (list*
           (rw-              (v-threefix (strip-cars sts)))
           (strobe-          (v-threefix (strip-cars sts)))
           (hdack-           (v-threefix (strip-cars sts)))
           (we-regs          (v-threefix (strip-cars sts)))
           (we-a-reg         (v-threefix (strip-cars sts)))
           (we-b-reg         (v-threefix (strip-cars sts)))
           (we-i-reg         (v-threefix (strip-cars sts)))
           (we-data-out      (v-threefix (strip-cars sts)))
           (we-addr-out      (v-threefix (strip-cars sts)))
           (we-hold-         (v-threefix (strip-cars sts)))
           (we-pc-reg        (v-threefix (strip-cars sts)))
           (data-in-select   (v-threefix (strip-cars sts)))
           (dec-addr-out     (v-threefix (strip-cars sts)))
           (select-immediate (v-threefix (strip-cars sts)))
           (alu-c            (v-threefix (strip-cars sts)))
           (alu-zero         (v-threefix (strip-cars sts)))
           (append (major-state (v-threefix (strip-cars sts)))
                   (append (we-flags (v-threefix (strip-cars sts)))
                           (append (regs-address (v-threefix
                                                  (strip-cars sts)))
                                   (append
                                    (alu-op (v-threefix
                                             (strip-cars sts)))
                                    (alu-mpg (v-threefix
                                              (strip-cars sts))))))))))
  :hints (("Goal" :in-theory (e/d (reg$value)
                                  ((si))))))

(defthmd bv-as-subseq
  (implies (and (>= (len x) 3)
                (true-listp x))
           (equal (bv x) (subseq x 3 (len x))))
  :hints (("Goal" :in-theory (enable bv))))

;; Lemmas

(defun machine-state-invariant (machine-state)
  (declare (xargs :guard (and (true-listp machine-state)
                              (true-listp (car machine-state)))))
  (b* ((regs               (car machine-state))
       (flags              (cadr machine-state))
       (a-reg              (caddr machine-state))
       (b-reg              (cadddr machine-state))
       (i-reg              (car (cddddr machine-state)))
       (data-out           (cadr (cddddr machine-state)))
       (addr-out           (caddr (cddddr machine-state)))
       (?last-reset-       (cadddr (cddddr machine-state)))
       (?last-dtack-       (car (cddddr (cddddr machine-state))))
       (?last-hold-        (cadr (cddddr (cddddr machine-state))))
       (pc-reg             (caddr (cddddr (cddddr machine-state))))
       (cntl-state         (cadddr (cddddr (cddddr machine-state)))))
    (b* ((?regs-regs   (car regs))
         (?regs-we     (cadr regs))
         (regs-data    (caddr regs))
         (regs-address (cadddr regs)))
      (and
       ;;(all-ramp-mem 4 (car regs-regs))
       ;;(memory-properp 4 32 (car regs-regs))
       (true-listp regs-data) (equal (len regs-data) 32)
       (true-listp regs-address) (equal (len regs-address) 4)
       (true-listp flags) (equal (len flags) 4)
       (true-listp a-reg) (equal (len a-reg) 32)
       (true-listp b-reg) (equal (len b-reg) 32)
       (true-listp i-reg) (equal (len i-reg) 32)
       (true-listp data-out) (equal (len data-out) 32)
       (true-listp addr-out) (equal (len addr-out) 32)
       (true-listp pc-reg) (equal (len pc-reg) 4)
       (true-listp cntl-state) (equal (len cntl-state) 40)))))

(defthmd chip-module$value
  (let ((regs (list regs-regs regs-we regs-data regs-addr)))
    (let ((machine-state
           (list
            regs flags a-reg b-reg i-reg data-out addr-out
            last-reset- last-dtack- last-hold- last-pc-reg
            cntl-state))
          (inputs
           (list* clk ti te dtack- reset- hold-
                  disable-regfile- test-regfile-
                  (append pc-reg-in data-in))))
      (implies
       (and (chip-module& netlist)
            (machine-state-invariant machine-state))
       (equal (se 'chip-module inputs machine-state netlist)
              (b* ((major-state      (major-state
                                      (v-threefix (strip-cars cntl-state))))
                   (rw-              (rw-
                                      (v-threefix (strip-cars cntl-state))))
                   (strobe-          (strobe-
                                      (v-threefix (strip-cars cntl-state))))
                   (?hdack-          (hdack-
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-regs         (we-regs
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-flags        (we-flags
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-a-reg        (we-a-reg
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-b-reg        (we-b-reg
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-i-reg        (we-i-reg
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-data-out     (we-data-out
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-addr-out     (we-addr-out
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-hold-        (we-hold-
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-pc-reg       (we-pc-reg
                                      (v-threefix (strip-cars cntl-state))))
                   (data-in-select   (data-in-select
                                      (v-threefix (strip-cars cntl-state))))
                   (dec-addr-out     (dec-addr-out
                                      (v-threefix (strip-cars cntl-state))))
                   (select-immediate (select-immediate
                                      (v-threefix (strip-cars cntl-state))))
                   (regs-address     (regs-address
                                      (v-threefix (strip-cars cntl-state))))
                   (alu-c            (alu-c
                                      (v-threefix (strip-cars cntl-state))))
                   (alu-op           (alu-op
                                      (v-threefix (strip-cars cntl-state))))
                   (alu-zero         (alu-zero
                                      (v-threefix (strip-cars cntl-state))))
                   (alu-mpg          (alu-mpg
                                      (v-threefix (strip-cars cntl-state)))))
                (let ((reg-bus (f$extend-immediate
                                select-immediate
                                (a-immediate (v-threefix (strip-cars i-reg)))
                                (f$read-regs regs-address regs)))
                      (alu-bus (f$core-alu alu-c
                                           (v-threefix (strip-cars a-reg))
                                           (v-threefix (strip-cars b-reg))
                                           alu-zero alu-mpg alu-op
                                           (make-tree 32))))
                  (b* ((?addr-out-bus (f$dec-pass dec-addr-out reg-bus))
                       (?abi-bus (fv-if (f-nand data-in-select
                                                (f-not (car last-dtack-)))
                                        reg-bus
                                        data-in)))
                    (list* (nth 3 (v-threefix (strip-cars last-pc-reg)))
                           (nth 2 alu-bus)
                           hdack-
                           (f-not hdack-)
                           (f-buf rw-)
                           strobe-
                           (append
                            (v-threefix (strip-cars addr-out))
                            (v-threefix (strip-cars data-out))
                            (v-threefix (strip-cars flags))
                            major-state
                            (subseq (v-threefix (strip-cars i-reg))
                                    28 32))))))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (se-rules
                             chip-module&
                             chip-module*$destructure
                             regfile$value
                             flags$value
                             we-reg$value
                             reg$value
                             b-buf-pwr$value
                             dec-pass$value
                             tv-if$value
                             core-alu$value
                             next-cntl-state$value
                             extend-immediate$value
                             reg-40$value-as-cntl-state
                             control-vector-accessors
                             a-immediate
                             bv-as-subseq)
                            (tv-disabled-rules
                             (chip-module*)
                             (make-tree)
                             (si)
                             (sis)
                             f-gates=b-gates
                             nth
                             strip-cars
                             open-v-threefix)))))

(defthmd chip-module$state
  (let ((regs (list regs-regs regs-we regs-data regs-addr)))
    (let ((machine-state
           (list
            regs flags a-reg b-reg i-reg data-out addr-out
            last-reset- last-dtack- last-hold- last-pc-reg
            cntl-state))
          (inputs
           (list* clk ti te dtack- reset- hold-
                  disable-regfile- test-regfile-
                  (append pc-reg-in data-in))))
      (implies
       (and (chip-module& netlist)
            (machine-state-invariant machine-state)
            (equal te nil)
            (equal disable-regfile- t)
            (equal test-regfile- t)
            (true-listp pc-reg-in) (equal (len pc-reg-in) 4)
            (true-listp data-in) (equal (len data-in) 32))
       (equal (de 'chip-module inputs machine-state netlist)
              (b* ((major-state      (major-state
                                      (v-threefix (strip-cars cntl-state))))
                   (rw-              (rw-
                                      (v-threefix (strip-cars cntl-state))))
                   (strobe-          (strobe-
                                      (v-threefix (strip-cars cntl-state))))
                   (?hdack-          (hdack-
                                      (v-threefix (strip-cars cntl-state))))
                   (we-regs          (we-regs
                                      (v-threefix (strip-cars cntl-state))))
                   (we-flags         (we-flags
                                      (v-threefix (strip-cars cntl-state))))
                   (we-a-reg         (we-a-reg
                                      (v-threefix (strip-cars cntl-state))))
                   (we-b-reg         (we-b-reg
                                      (v-threefix (strip-cars cntl-state))))
                   (we-i-reg         (we-i-reg
                                      (v-threefix (strip-cars cntl-state))))
                   (we-data-out      (we-data-out
                                      (v-threefix (strip-cars cntl-state))))
                   (we-addr-out      (we-addr-out
                                      (v-threefix (strip-cars cntl-state))))
                   (we-hold-         (we-hold-
                                      (v-threefix (strip-cars cntl-state))))
                   (we-pc-reg        (we-pc-reg
                                      (v-threefix (strip-cars cntl-state))))
                   (data-in-select   (data-in-select
                                      (v-threefix (strip-cars cntl-state))))
                   (dec-addr-out     (dec-addr-out
                                      (v-threefix (strip-cars cntl-state))))
                   (select-immediate (select-immediate
                                      (v-threefix (strip-cars cntl-state))))
                   (regs-address     (regs-address
                                      (v-threefix (strip-cars cntl-state))))
                   (alu-c            (alu-c
                                      (v-threefix (strip-cars cntl-state))))
                   (alu-op           (alu-op
                                      (v-threefix (strip-cars cntl-state))))
                   (alu-zero         (alu-zero
                                      (v-threefix (strip-cars cntl-state))))
                   (alu-mpg          (alu-mpg
                                      (v-threefix (strip-cars cntl-state)))))
                (let ((reg-bus (f$extend-immediate
                                select-immediate
                                (a-immediate (v-threefix (strip-cars i-reg)))
                                (f$read-regs regs-address regs)))
                      (alu-bus (f$core-alu alu-c
                                           (v-threefix (strip-cars a-reg))
                                           (v-threefix (strip-cars b-reg))
                                           alu-zero alu-mpg alu-op
                                           (make-tree 32))))
                  (let ((addr-out-bus (f$dec-pass dec-addr-out reg-bus))
                        (abi-bus (fv-if (f-nand data-in-select
                                                (f-not (car last-dtack-)))
                                        reg-bus
                                        data-in)))
                    (list
                     (f$write-regs we-regs regs-address regs (bv alu-bus))
                     (pairlis$
                      (f$update-flags (strip-cars flags) we-flags alu-bus)
                      nil)
                     (pairlis$
                      (fv-if we-a-reg abi-bus (strip-cars a-reg))
                      nil)
                     (pairlis$
                      (fv-if we-b-reg abi-bus (strip-cars b-reg))
                      nil)
                     (pairlis$
                      (fv-if we-i-reg abi-bus (strip-cars i-reg))
                      nil)
                     (pairlis$
                      (fv-if we-data-out (bv alu-bus) (strip-cars data-out))
                      nil)
                     (pairlis$
                      (fv-if we-addr-out addr-out-bus (strip-cars addr-out))
                      nil)
                     (list (f-buf reset-))
                     (list (f-or strobe- dtack-))
                     (list (f-if we-hold- hold- (car last-hold-)))
                     (pairlis$
                      (fv-if we-pc-reg pc-reg-in (strip-cars last-pc-reg))
                      nil)
                     (pairlis$
                      (v-threefix (f$next-cntl-state
                                   (f-buf (car last-reset-))
                                   (f-buf (car last-dtack-))
                                   (f-buf (car last-hold-))
                                   rw-
                                   major-state
                                   (v-threefix (strip-cars i-reg))
                                   (v-threefix (strip-cars flags))
                                   (v-threefix (strip-cars last-pc-reg))
                                   regs-address))
                      nil)))))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (de-rules
                             chip-module&
                             chip-module*$destructure
                             regfile$value regfile$state
                             flags$value flags$state
                             we-reg$value we-reg$state
                             reg$value reg$state
                             b-buf-pwr$value
                             dec-pass$value
                             tv-if$value
                             core-alu$value
                             next-cntl-state$value
                             extend-immediate$value
                             reg-40$value-as-cntl-state
                             control-vector-accessors
                             a-immediate
                             bv-as-subseq)
                            (tv-disabled-rules
                             (chip-module*)
                             (make-tree)
                             (si)
                             (sis)
                             f-gates=b-gates
                             nth
                             strip-cars
                             open-v-threefix)))))

;; ======================================================================

;; CHIP

;; The entire chip, with pads, as a module.

;; INPUTS:

;; The system clock input is a special two-pad, clock-driver buffer.
;; The other inputs are ordinary TTL inputs.

;;    CLK  -- The system clock

;;    TI   -- Test input (Scan in)
;;    TE   -- Test enable (Scan enable)

;;    DTACK-  --  DTACK input
;;    RESET-  --  RESET input
;;    HOLD-   --  HOLD input

;;    DISABLE-REGFILE-   --  Must be high to write enable the register
;;                           file RAM.  During scan-in, DISABLE-REGFILE- is
;;                           held low to avoid spurious writes to the RAM.

;;    TEST-REGFILE-    --  Normally high.  When low, forces the register file
;;                         output mux to pass data directly from the RAM.

;;    PC-REG-IN[0..3]  --  The PC-REG inputs.


;; BI-DIRECTS:

;;    DATA-BUS[0..31]  --  The bi-directional data bus. (Controlled by RW-)

;; OUTPUTS:

;; The memory control lines and the ADDR-OUT lines are tri-state.
;; The other output signals are ordinary TTL outputs.

;;    PO      --  Parametric Output.
;;    TO      --  Test Output (Scan out)
;;    TIMING  --  The net corresponding to the longest combinational path.
;;                Used to verify the speed of the device.

;;    HDACK-   --  Hold Acknowledge

;;    RW-      --  Memory control lines  (Tristate)
;;    STROBE-

;;    ADDR-OUT[0..31]  --  Address bus (Tristate)

;;    FLAGS[0..3]     --  Observability pins
;;    CNTL-STATE[0..4]
;;    I-REG[28..31]

(module-generator
 chip* ()

 'chip

 (list* 'clk 'ti 'te 'dtack- 'reset- 'hold-
        'disable-regfile- 'test-regfile-
        (append (sis 'pc-reg-in 0 4)
                (sis 'data-bus 0 32)))

 (list* 'po 'to 'timing 'hdack- 'rw- 'strobe-
        (append (sis 'addr-out 0 32)
                (append (sis 'data-bus 0 32)
                        (append (sis 'flags 0 4)
                                (append (sis 'cntl-state 0 5)
                                        (sis 'i-reg 28 4))))))

 ;;  The processor state
 '(body)

 (list

  ;;  The processor core.

  (list 'body
        (list* 'i-to 'i-timing 'i-hdack- 'i-en-addr-out- 'i-rw- 'i-strobe-
               (append (sis 'i-addr-out 0 32)
                       (append (sis 'i-data-out 0 32)
                               (append (sis 'i-flags 0 4)
                                       (append (sis 'i-cntl-state 0 5)
                                               (sis 'i-i-reg 28 4))))))

        'chip-module
        (list* 'i-clk 'i-ti 'i-te 'i-dtack- 'i-reset-
               'i-hold- 'i-disable-regfile- 'i-test-regfile-
               (append (sis 'i-pc-reg 0 4)
                       (sis 'i-data-in 0 32))))

  ;;  The input pads.  The pads are ordered such that the inputs to PROCMON are
  ;;  not from bidirect pads (as required), while maintaining the ordering
  ;;  required by the DE interpreter.

  '(plus-5 (b-true-p) vdd-parametric ())

  '(clock-pad (i-clk clk-po) ttl-clk-input (clk b-true-p))
  '(ti-pad    (i-ti  ti-po)  ttl-input     (ti b-true-p))
  '(te-pad    (i-te  te-po)  ttl-input     (te ti-po))

  '(dtack-pad (i-dtack- dtack-po) ttl-input (dtack- te-po))
  '(reset-pad (i-reset- reset-po) ttl-input (reset- dtack-po))
  '(hold-pad  (i-hold- hold-po)   ttl-input (hold- reset-po))

  '(disable-regfile-pad (i-disable-regfile- disable-regfile-po)
                        ttl-input (disable-regfile- hold-po))
  '(test-regfile-pad (i-test-regfile- test-regfile-po)
                     ttl-input (test-regfile- disable-regfile-po))

  ;;  DATA-BUS

  (list 'data-bus-pads
        (cons 'data-bus-po (append (sis 'data-bus 0 32)
                                   (sis 'i-data-in 0 32)))
        (si 'ttl-bidirect-pads 32)
        (list* 'i-rw- 'test-regfile-po
               (append (sis 'data-bus 0 32) (sis 'i-data-out 0 32))))

  ;;  PC-REG

  (list 'pc-reg-pads
        (cons 'pc-reg-po (sis 'i-pc-reg 0 4))
        (si 'ttl-input-pads 4)
        (cons 'data-bus-po (sis 'pc-reg-in 0 4)))

  ;;  The process monitor -- required by LSI Logic.

  '(monitor (i-po) procmon (pc-reg-po clk-po b-true-p b-true-p))

  ;;  The output pads.

  '(po-pad     (po)      ttl-output-parametric (i-po))
  '(to-pad     (to)      ttl-output (i-to))
  '(timing-pad (timing)  ttl-output-fast (i-timing))

  '(hdack-pad   (hdack-)  ttl-output-fast (i-hdack-))
  '(rw-pad      (rw-)     ttl-tri-output-fast (i-rw- i-en-addr-out-))
  '(strobe-pad  (strobe-) ttl-tri-output-fast (i-strobe- i-en-addr-out-))

  ;;  ADDR-OUT

  (list 'addr-out-pads
        (sis 'addr-out 0 32)
        (si 'ttl-tri-output-pads 32)
        (cons 'i-en-addr-out- (sis 'i-addr-out 0 32)))

  ;;  FLAGS

  (list 'flags-pads
        (sis 'flags 0 4)
        (si 'ttl-output-pads 4)
        (sis 'i-flags 0 4))

  ;;  CNTL-STATE

  (list 'cntl-state-pads
        (sis 'cntl-state 0 5)
        (si 'ttl-output-pads 5)
        (sis 'i-cntl-state 0 5))

  ;;  I-REG [28..31]

  (list 'i-reg-pads
        (sis 'i-reg 28 4)
        (si 'ttl-output-pads 4)
        (sis 'i-i-reg 28 4))

  )
 :guard t)

(defund chip& (netlist)
  (and (equal (assoc 'chip netlist)
              (chip*))
       (let ((netlist (delete-to-eq 'chip netlist)))
         (and (chip-module& netlist)
              (ttl-input-pads& netlist 4)
              (ttl-bidirect-pads& netlist 32)
              (ttl-tri-output-pads& netlist 32)
              (ttl-output-pads& netlist 4)
              (ttl-output-pads& netlist 5)))))

(defun chip$netlist ()
  (cons
   (chip*)
   (union$ (ttl-bidirect-pads$netlist 32)
           (chip-module$netlist)
           (ttl-input-pads$netlist 4)
           (ttl-tri-output-pads$netlist 32)
           (ttl-output-pads$netlist 4)
           (ttl-output-pads$netlist 5)
           :test 'equal)))

(defthmd chip$value
  (let ((regs (list regs-regs regs-we regs-data regs-addr)))
    (let ((machine-state
           (list
            regs flags a-reg b-reg i-reg data-out addr-out
            last-reset- last-dtack- last-hold- last-pc-reg
            cntl-state))
          (inputs
           (list* clk ti te dtack- reset- hold-
                  disable-regfile- test-regfile-
                  (append pc-reg-in data-in))))
      (implies
       (and (chip& netlist)
            (machine-state-invariant machine-state))
       (equal (cdr (se 'chip inputs (list machine-state) netlist))
              (b* ((major-state      (major-state
                                      (v-threefix (strip-cars cntl-state))))
                   (rw-              (rw-
                                      (v-threefix (strip-cars cntl-state))))
                   (strobe-          (strobe-
                                      (v-threefix (strip-cars cntl-state))))
                   (?hdack-          (hdack-
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-regs         (we-regs
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-flags        (we-flags
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-a-reg        (we-a-reg
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-b-reg        (we-b-reg
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-i-reg        (we-i-reg
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-data-out     (we-data-out
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-addr-out     (we-addr-out
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-hold-        (we-hold-
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-pc-reg       (we-pc-reg
                                      (v-threefix (strip-cars cntl-state))))
                   (data-in-select   (data-in-select
                                      (v-threefix (strip-cars cntl-state))))
                   (dec-addr-out     (dec-addr-out
                                      (v-threefix (strip-cars cntl-state))))
                   (select-immediate (select-immediate
                                      (v-threefix (strip-cars cntl-state))))
                   (regs-address     (regs-address
                                      (v-threefix (strip-cars cntl-state))))
                   (alu-c            (alu-c
                                      (v-threefix (strip-cars cntl-state))))
                   (alu-op           (alu-op
                                      (v-threefix (strip-cars cntl-state))))
                   (alu-zero         (alu-zero
                                      (v-threefix (strip-cars cntl-state))))
                   (alu-mpg          (alu-mpg
                                      (v-threefix (strip-cars cntl-state)))))
                (let ((reg-bus (f$extend-immediate
                                select-immediate
                                (a-immediate (v-threefix (strip-cars i-reg)))
                                (f$read-regs regs-address regs)))
                      (alu-bus (f$core-alu alu-c
                                           (v-threefix (strip-cars a-reg))
                                           (v-threefix (strip-cars b-reg))
                                           alu-zero alu-mpg alu-op
                                           (make-tree 32))))
                  (b* ((?addr-out-bus (f$dec-pass dec-addr-out reg-bus))
                       (?abi-bus
                        (fv-if (f-nand data-in-select
                                       (f-not (car last-dtack-)))
                               reg-bus
                               (v-wire data-in
                                       (vft-buf (f-not rw-)
                                                (v-threefix
                                                 (strip-cars data-out)))))))
                    (list* (f-buf
                            (nth 3 (v-threefix (strip-cars last-pc-reg))))
                           (f-buf (nth 2 alu-bus))
                           (f-buf hdack-)
                           (ft-buf (f-buf hdack-) (f-buf rw-))
                           (ft-buf (f-buf hdack-) strobe-)
                           (append
                            (vft-buf (f-buf hdack-)
                                     (v-threefix (strip-cars addr-out)))
                            (vft-buf (f-not (f-buf rw-))
                                     (v-threefix (strip-cars data-out)))
                            (v-threefix (strip-cars flags))
                            (v-threefix major-state)
                            (v-threefix
                             (subseq (v-threefix (strip-cars i-reg))
                                     28 32)))))))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (se-rules
                             chip&
                             chip*$destructure
                             chip-module$value
                             ttl-input-pads$value
                             ttl-output-pads$value
                             ttl-bidirect-pads$value
                             ttl-tri-output-pads$value
                             major-state
                             f-not-f-not=f-buf)
                            (tv-disabled-rules
                             (chip*)
                             (make-tree)
                             (si)
                             (sis)
                             f-gates=b-gates
                             nth
                             strip-cars
                             append-v-threefix
                             open-v-threefix)))))

(defthmd chip$state
  (let ((regs (list regs-regs regs-we regs-data regs-addr)))
    (let ((machine-state
           (list
            regs flags a-reg b-reg i-reg data-out addr-out
            last-reset- last-dtack- last-hold- last-pc-reg
            cntl-state))
          (inputs
           (list* clk ti te dtack- reset- hold-
                  disable-regfile- test-regfile-
                  (append pc-reg-in data-in))))
      (implies
       (and (chip& netlist)
            (machine-state-invariant machine-state)
            (equal te nil)
            (equal disable-regfile- t)
            (equal test-regfile- t)
            (true-listp pc-reg-in) (equal (len pc-reg-in) 4)
            (true-listp data-in) (equal (len data-in) 32))
       (equal (de 'chip inputs (list machine-state) netlist)
              (b* ((major-state      (major-state
                                      (v-threefix (strip-cars cntl-state))))
                   (rw-              (rw-
                                      (v-threefix (strip-cars cntl-state))))
                   (strobe-          (strobe-
                                      (v-threefix (strip-cars cntl-state))))
                   (?hdack-          (hdack-
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-regs         (we-regs
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-flags        (we-flags
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-a-reg        (we-a-reg
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-b-reg        (we-b-reg
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-i-reg        (we-i-reg
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-data-out     (we-data-out
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-addr-out     (we-addr-out
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-hold-        (we-hold-
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-pc-reg       (we-pc-reg
                                      (v-threefix (strip-cars cntl-state))))
                   (data-in-select   (data-in-select
                                      (v-threefix (strip-cars cntl-state))))
                   (dec-addr-out     (dec-addr-out
                                      (v-threefix (strip-cars cntl-state))))
                   (select-immediate (select-immediate
                                      (v-threefix (strip-cars cntl-state))))
                   (regs-address     (regs-address
                                      (v-threefix (strip-cars cntl-state))))
                   (alu-c            (alu-c
                                      (v-threefix (strip-cars cntl-state))))
                   (alu-op           (alu-op
                                      (v-threefix (strip-cars cntl-state))))
                   (alu-zero         (alu-zero
                                      (v-threefix (strip-cars cntl-state))))
                   (alu-mpg          (alu-mpg
                                      (v-threefix (strip-cars cntl-state)))))
                (let ((reg-bus (f$extend-immediate
                                select-immediate
                                (a-immediate (v-threefix (strip-cars i-reg)))
                                (f$read-regs regs-address regs)))
                      (alu-bus (f$core-alu alu-c
                                           (v-threefix (strip-cars a-reg))
                                           (v-threefix (strip-cars b-reg))
                                           alu-zero alu-mpg alu-op
                                           (make-tree 32))))
                  (let ((addr-out-bus (f$dec-pass dec-addr-out reg-bus))
                        (abi-bus
                         (fv-if (f-nand data-in-select
                                        (f-not (car last-dtack-)))
                                reg-bus
                                (v-wire data-in
                                        (vft-buf (f-not (f-buf rw-))
                                                 (v-threefix
                                                  (strip-cars data-out)))))))
                    (list
                     (list
                      (f$write-regs we-regs regs-address regs (bv alu-bus))
                      (pairlis$
                       (f$update-flags (strip-cars flags) we-flags alu-bus)
                       nil)
                      (pairlis$
                       (fv-if we-a-reg abi-bus (strip-cars a-reg))
                       nil)
                      (pairlis$
                       (fv-if we-b-reg abi-bus (strip-cars b-reg))
                       nil)
                      (pairlis$
                       (fv-if we-i-reg abi-bus (strip-cars i-reg))
                       nil)
                      (pairlis$
                       (fv-if we-data-out (bv alu-bus) (strip-cars data-out))
                       nil)
                      (pairlis$
                       (fv-if we-addr-out addr-out-bus (strip-cars addr-out))
                       nil)
                      (list (f-buf reset-))
                      (list (f-or strobe- (f-buf dtack-)))
                      (list (f-if we-hold- (f-buf hold-) (car last-hold-)))
                      (pairlis$
                       (fv-if we-pc-reg pc-reg-in (strip-cars last-pc-reg))
                       nil)
                      (pairlis$
                       (v-threefix (f$next-cntl-state
                                    (f-buf (car last-reset-))
                                    (f-buf (car last-dtack-))
                                    (f-buf (car last-hold-))
                                    rw-
                                    major-state
                                    (v-threefix (strip-cars i-reg))
                                    (v-threefix (strip-cars flags))
                                    (v-threefix (strip-cars last-pc-reg))
                                    regs-address))
                       nil))))))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (de-rules
                             chip&
                             chip*$destructure
                             chip-module$value chip-module$state
                             ttl-input-pads$value
                             ttl-output-pads$value
                             ttl-bidirect-pads$value
                             ttl-tri-output-pads$value
                             f-buf-delete-lemmas)
                            (tv-disabled-rules
                             (chip*)
                             (make-tree)
                             (si)
                             (sis)
                             f-gates=b-gates
                             nth
                             strip-cars
                             append-v-threefix
                             open-v-threefix)))))

;; ======================================================================

;;    CHIP-SYSTEM

;;    CHIP + MEMORY

;; INPUTS:

;;    CLK  -- The system clock

;;    TI   -- Test input (Scan in)
;;    TE   -- Test enable (Scan enable)

;;    RESET-  --  RESET input
;;    HOLD-   --  HOLD input

;;    DISABLE-REGFILE-   --  Must be high to write enable the register
;;                           file RAM.  During scan-in, DISABLE-REGFILE- is
;;                           held low to avoid spurious writes to the RAM.

;;    TEST-REGFILE-    --  Normally high.  When low, forces the register file
;;                         output mux to pass data directly from the RAM.

;;    PC-REG-IN[0..3]  --  The PC-REG inputs.

;; OUTPUTS:

;;    None.

(module-generator
 chip-system* ()
 'chip-system
 ;;  Inputs
 (list* 'clk 'ti 'te 'reset- 'hold-
        'disable-regfile- 'test-regfile-
        (sis 'pc-reg 0 4))
 ;;  Outputs
 ()
 ;;  State
 '(fm9001 mem)
 ;;  Body
 (list
  ;;  The FM9001
  (list 'fm9001
        (list* 'po 'to 'timing 'hdack- 'rw- 'strobe-
               (append (sis 'addr-out 0 32)
                       (append (sis 'fm9001-data 0 32)
                               (append (sis 'flags 0 4)
                                       (append (sis 'cntl-state 0 5)
                                               (sis 'i-reg 28 4))))))
        'chip
        (list* 'clk 'ti 'te 'dtack- 'reset- 'hold-
               'disable-regfile- 'test-regfile-
               (append (sis 'pc-reg 0 4)
                       (sis 'data-bus 0 32))))
  ;;  Memory control busses
  '(pullup-rw- (rw-bus) pullup (rw-))

  '(pullup-strobe- (strobe-bus) pullup (strobe-))

  (list 'address
        (sis 'addr-bus 0 32)
        (si 'v-pullup 32)
        (sis 'addr-out 0 32))

  ;;  Memory
  (list 'mem
        (list* 'dtack- (sis 'mem-data 0 32))
        'mem-32x32
        (list* 'rw-bus 'strobe-bus
               (append (sis 'addr-bus 0 32) (sis 'data-bus 0 32))))

  ;;  Data busses
  (list 'data-wire
        (sis 'data-wire 0 32)
        (si 'v-wire 32)
        (append (sis 'fm9001-data 0 32) (sis 'mem-data 0 32)))

  (list 'data
        (sis 'data-bus 0 32)
        (si 'v-pullup 32)
        (sis 'data-wire 0 32)))

 :guard t)

(defund chip-system& (netlist)
  (and (equal (assoc 'chip-system netlist)
              (chip-system*))
       (let ((netlist (delete-to-eq 'chip-system netlist)))
         (and (chip& netlist)
              (v-pullup& netlist 32)
              (v-wire& netlist 32)))))

(defun chip-system$netlist ()
  (cons (chip-system*)
        (union$ (v-pullup$netlist 32)
                (v-wire$netlist 32)
                (chip$netlist)
                :test 'equal)))

(defthm check-chip-system$netlist
  (chip-system& (chip-system$netlist)))

(defun memory-state-invariant (mem-state)
  (declare (xargs :guard (true-listp mem-state)))
  (b* ((mem              (car mem-state))
       (?mem-cntl        (cadr mem-state))
       (?mem-clock       (caddr mem-state))
       (?mem-count       (cadddr mem-state))
       (?mem-dtack       (car (cddddr mem-state)))
       (?mem-last-rw-    (cadr (cddddr mem-state)))
       (mem-last-address (caddr (cddddr mem-state)))
       (mem-last-data    (cadddr (cddddr mem-state))))
    (and (memory-properp 32 32 mem)
         (true-listp mem-last-address)
         (true-listp mem-last-data)
         (equal (len mem-last-data) 32))))

(defund chip-system-invariant (st)
  (and (machine-state-invariant (caar st))
       (memory-state-invariant (caadr st))))

(defthm equal-memory-value-for-chip-system$state
  (equal (memory-value st strobe rw- address (assoc-eq-values args alist))
         (memory-value st strobe rw- address
                       (make-list (len args) :initial-element *X*))))

(defthmd chip-system$state-help
  (let ((regs (list regs-regs regs-we regs-data regs-addr)))
    (let ((machine-state
           (list
            regs flags a-reg b-reg i-reg data-out addr-out
            last-reset- last-dtack- last-hold- last-pc-reg
            cntl-state))
          (inputs
           (list* clk ti te reset- hold-
                  disable-regfile- test-regfile-
                  pc-reg-in)))
      (implies
       (and (chip-system& netlist)
            (chip-system-invariant (list (list machine-state)
                                         (list mem-state)))
            (equal te nil)
            (equal disable-regfile- t)
            (equal test-regfile- t)
            (true-listp pc-reg-in) (equal (len pc-reg-in) 4))
       (equal (de 'chip-system
                  inputs
                  (list (list machine-state)
                        (list mem-state))
                  netlist)
              (b* ((major-state      (major-state
                                      (v-threefix (strip-cars cntl-state))))
                   (rw-              (rw-
                                      (v-threefix (strip-cars cntl-state))))
                   (strobe-          (strobe-
                                      (v-threefix (strip-cars cntl-state))))
                   (?hdack-          (hdack-
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-regs         (we-regs
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-flags        (we-flags
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-a-reg        (we-a-reg
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-b-reg        (we-b-reg
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-i-reg        (we-i-reg
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-data-out     (we-data-out
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-addr-out     (we-addr-out
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-hold-        (we-hold-
                                      (v-threefix (strip-cars cntl-state))))
                   (?we-pc-reg       (we-pc-reg
                                      (v-threefix (strip-cars cntl-state))))
                   (data-in-select   (data-in-select
                                      (v-threefix (strip-cars cntl-state))))
                   (dec-addr-out     (dec-addr-out
                                      (v-threefix (strip-cars cntl-state))))
                   (select-immediate (select-immediate
                                      (v-threefix (strip-cars cntl-state))))
                   (regs-address     (regs-address
                                      (v-threefix (strip-cars cntl-state))))
                   (alu-c            (alu-c
                                      (v-threefix (strip-cars cntl-state))))
                   (alu-op           (alu-op
                                      (v-threefix (strip-cars cntl-state))))
                   (alu-zero         (alu-zero
                                      (v-threefix (strip-cars cntl-state))))
                   (alu-mpg          (alu-mpg
                                      (v-threefix (strip-cars cntl-state)))))
                (let ((ext-addr-out
                       (v-pullup (vft-buf (f-buf hdack-)
                                          (v-threefix (strip-cars addr-out)))))
                      (ext-rw-
                       (f-pullup (ft-buf (f-buf hdack-) (f-buf rw-))))
                      (ext-strobe-
                       (f-pullup (ft-buf (f-buf hdack-) strobe-)))
                      (ext-data-out
                       (vft-buf (f-not (f-buf rw-))
                                (v-threefix (strip-cars data-out)))))
                  (let ((mem-response
                         (memory-value mem-state ext-strobe- ext-rw-
                                       ext-addr-out
                                       (make-list 32 :initial-element *X*))))
                    (let ((dtack- (car mem-response))
                          (ext-data-bus (v-pullup
                                         (v-wire ext-data-out
                                                 (cdr mem-response)))))
                      (let ((reg-bus (f$extend-immediate
                                      select-immediate
                                      (a-immediate (v-threefix
                                                    (strip-cars i-reg)))
                                      (f$read-regs regs-address regs)))
                            (alu-bus (f$core-alu alu-c
                                                 (v-threefix
                                                  (strip-cars a-reg))
                                                 (v-threefix
                                                  (strip-cars b-reg))
                                                 alu-zero alu-mpg alu-op
                                                 (make-tree 32)))
                            (data-in (v-threefix
                                      (v-wire ext-data-bus
                                              ext-data-out))))
                        (let ((addr-out-bus (f$dec-pass dec-addr-out reg-bus))
                              (abi-bus
                               (fv-if (f-nand data-in-select
                                              (f-not (car last-dtack-)))
                                      reg-bus
                                      data-in)))
                          (list
                           (list
                            (list
                             (f$write-regs we-regs regs-address regs
                                           (bv alu-bus))
                             (pairlis$
                              (f$update-flags (strip-cars flags)
                                              we-flags
                                              alu-bus)
                              nil)
                             (pairlis$
                              (fv-if we-a-reg abi-bus (strip-cars a-reg))
                              nil)
                             (pairlis$
                              (fv-if we-b-reg abi-bus (strip-cars b-reg))
                              nil)
                             (pairlis$
                              (fv-if we-i-reg abi-bus (strip-cars i-reg))
                              nil)
                             (pairlis$
                              (fv-if we-data-out (bv alu-bus)
                                     (strip-cars data-out))
                              nil)
                             (pairlis$
                              (fv-if we-addr-out addr-out-bus
                                     (strip-cars addr-out))
                              nil)
                             (list (f-buf reset-))
                             (list (f-or strobe- (f-buf dtack-)))
                             (list (f-if we-hold-
                                         (f-buf hold-)
                                         (car last-hold-)))
                             (pairlis$
                              (fv-if we-pc-reg
                                     pc-reg-in
                                     (strip-cars last-pc-reg))
                              nil)
                             (pairlis$
                              (v-threefix (f$next-cntl-state
                                           (f-buf (car last-reset-))
                                           (f-buf (car last-dtack-))
                                           (f-buf (car last-hold-))
                                           rw-
                                           major-state
                                           (v-threefix (strip-cars i-reg))
                                           (v-threefix (strip-cars flags))
                                           (v-threefix
                                            (strip-cars last-pc-reg))
                                           regs-address))
                              nil)))
                           (list
                            (next-memory-state
                             mem-state ext-strobe- ext-rw-
                             ext-addr-out
                             ext-data-bus)))))))))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (de-rules
                            chip-system&
                            chip-system*$destructure
                            chip-system-invariant
                            chip$value chip$state
                            mem-32x32$structured-value
                            mem-32x32$structured-state
                            v-pullup$value
                            v-wire$value)
                           (tv-disabled-rules
                            (chip-system*)
                            (make-tree)
                            (si)
                            (sis)
                            f-gates=b-gates
                            nth
                            strip-cars
                            append-v-threefix
                            open-v-threefix)))))

(defthmd chip-system$state
  (let ((regs (list regs-regs regs-we regs-data regs-addr)))
    (let ((machine-state
           (list
            regs flags a-reg b-reg i-reg data-out addr-out
            last-reset- last-dtack- last-hold- last-pc-reg
            cntl-state))
          (inputs
           (list* clk ti te reset- hold-
                  disable-regfile- test-regfile-
                  pc-reg-in)))
      (implies
       (and (chip-system& netlist)
            (chip-system-invariant (list (list machine-state)
                                         (list mem-state)))
            (equal te nil)
            (equal disable-regfile- t)
            (equal test-regfile- t)
            (true-listp pc-reg-in) (equal (len pc-reg-in) 4))
       (equal (de 'chip-system
                  inputs
                  (list (list machine-state)
                        (list mem-state))
                  netlist)
              (fm9001-next-state (list (list machine-state)
                                       (list mem-state))
                                 (list* reset- hold- pc-reg-in))))))
  :hints (("Goal"
           :in-theory (e/d (fm9001-hardware-state-accessors
                            fm9001-external-input-accessors
                            chip-system$state-help
                            fm9001-next-state)
                           (f-gates=b-gates
                            nth
                            strip-cars
                            append-v-threefix
                            open-v-threefix)))))

;; ======================================================================

;; Induction proofs and specifications.

(defthm next-memory-state-preserves-memory-invariant
  (implies (and (memory-state-invariant mem-state)
                (equal (len data) 32)
                (equal (len address) 32))
           (memory-state-invariant
            (next-memory-state mem-state strobe- rw- address data)))
  :hints (("Goal" :in-theory (e/d (next-memory-state)
                                  (bvp-cvzbv
                                   zp-open
                                   nfix)))))

(defthm memory-properp-dual-port-ram-state-crock
  (implies (memory-properp 4 32 regs)
           (memory-properp
            4 32
            (dual-port-ram-state
             32 4
             (append a-address (append b-address (cons we data))) regs))))

(defthm all-ramp-mem-dual-port-ram-state-crock
  (implies (all-ramp-mem 4 regs)
           (all-ramp-mem
            4
            (dual-port-ram-state
             32 4
             (append a-address (append b-address (cons we data))) regs))))

(defthm fm9001-preserves-chip-system-invariant
  (implies (and (chip-system-invariant st)
                (equal (len (pc-reg-input inputs)) 4))
           (chip-system-invariant
            (fm9001-next-state st inputs)))
  :hints (("Goal"
           :in-theory (e/d (chip-system-invariant
                            fm9001-hardware-state-accessors
                            fm9001-next-state
                            f$write-regs
                            regs-address)
                           (dual-port-ram-state
                            memory-state-invariant
                            nth
                            bvp-is-true-listp
                            bvp-cvzbv
                            v-threefix-bvp
                            take
                            f-gates=b-gates
                            open-v-threefix)))))

;; ======================================================================

;; CHIP-SYSTEM-OPERATING-INPUTS-P

(defun chip-system-input-invariant (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((?clk             (car inputs))
       (?ti              (cadr inputs))
       (te               (caddr inputs))
       (?reset-          (cadddr inputs))
       (?hold-           (car (cddddr inputs)))
       (disable-regfile- (cadr (cddddr inputs)))
       (test-regfile-    (caddr (cddddr inputs)))
       (pc-reg-in        (cdddr (cddddr inputs))))
    (and (equal te nil)
         (equal disable-regfile- t)
         (equal test-regfile- t)
         (true-listp pc-reg-in)
         (equal (len pc-reg-in) 4))))

(defthm rewrite-chip-system-input-invariant
  (equal (chip-system-input-invariant inputs)
         (b* ((?clk             (car inputs))
              (?ti              (cadr inputs))
              (te               (caddr inputs))
              (?reset-          (cadddr inputs))
              (?hold-           (car (cddddr inputs)))
              (disable-regfile- (cadr (cddddr inputs)))
              (test-regfile-    (caddr (cddddr inputs)))
              (pc-reg-in        (cdddr (cddddr inputs))))
           (and (equal inputs
                       (list* clk ti te reset- hold-
                              disable-regfile- test-regfile-
                              pc-reg-in))
                (equal te nil)
                (equal disable-regfile- t)
                (equal test-regfile- t)
                (true-listp pc-reg-in)
                (equal (len pc-reg-in) 4)))))

(in-theory (disable chip-system-input-invariant))

(defun chip-system-operating-inputs-p (inputs n)
  (declare (xargs :guard (and (true-list-listp inputs)
                              (natp n))))
  (if (zp n)
      t
    (and (chip-system-input-invariant (car inputs))
         (chip-system-operating-inputs-p (cdr inputs) (1- n)))))

(defthm open-chip-system-operating-inputs-p
  (and
   (implies (zp n)
            (equal (chip-system-operating-inputs-p inputs n)
                   t))
   (implies (not (zp n))
            (equal (chip-system-operating-inputs-p inputs n)
                   (and (chip-system-input-invariant (car inputs))
                        (chip-system-operating-inputs-p (cdr inputs)
                                                        (1- n)))))))

(in-theory (disable chip-system-operating-inputs-p))

;; ======================================================================

;; MAP-UP-1-INPUT and MAP-UP-INPUTS

;; Convert low-level input streams to mid-level input streams.

(defun map-up-1-input (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((?clk              (car inputs))
       (?ti               (cadr inputs))
       (?te               (caddr inputs))
       (reset-            (cadddr inputs))
       (hold-             (car (cddddr inputs)))
       (?disable-regfile- (cadr (cddddr inputs)))
       (?test-regfile-    (caddr (cddddr inputs)))
       (pc-reg-in         (cdddr (cddddr inputs))))
    (list* reset- hold- pc-reg-in)))

(defun map-up-inputs (inputs)
  (declare (xargs :guard (true-list-listp inputs)))
  (if (atom inputs)
      nil
    (cons (map-up-1-input (car inputs))
          (map-up-inputs (cdr inputs)))))

(defthm open-map-up-inputs
  (and
   (implies (atom inputs)
            (equal (map-up-inputs inputs)
                   nil))
   (implies (consp inputs)
            (equal (map-up-inputs inputs)
                   (cons (map-up-1-input (car inputs))
                         (map-up-inputs (cdr inputs)))))))

(in-theory (disable map-up-1-input map-up-inputs))

;; ======================================================================

;; The proofs that the DE model of the processor equal RUN-FM9001.

(defthmd chip-system=fm9001$step
  (implies (and (chip-system& netlist)
                (fm9001-state-structure sts)
                (chip-system-invariant sts)
                (chip-system-input-invariant inputs))
           (equal (de 'chip-system inputs sts netlist)
                  (fm9001-next-state sts (map-up-1-input inputs))))
  :hints (("Goal"
           :in-theory (e/d (map-up-1-input)
                           (car-cdr-elim
                            fm9001-state-as-a-list

; The following rule was disabled by Matt K. after v8-0, due to ACL2 changes
; based on keeping LET-expressions on right-hand sides of rewrite rules.

                            acl2::cons-car-cdr))
           :use ((:instance fm9001-state-as-a-list
                            (st sts))
                 (:instance
                  chip-system$state
                  (regs-regs        (caaaar sts))
                  (regs-we          (car (cdaaar sts)))
                  (regs-data        (cadr (cdaaar sts)))
                  (regs-addr        (caddr (cdaaar sts)))
                  (flags            (cadaar sts))
                  (a-reg            (car (cddaar sts)))
                  (b-reg            (cadr (cddaar sts)))
                  (i-reg            (caddr (cddaar sts)))
                  (data-out         (cadddr (cddaar sts)))
                  (addr-out         (car (cddddr (cddaar sts))))
                  (last-reset-      (cadr (cddddr (cddaar sts))))
                  (last-dtack-      (caddr (cddddr (cddaar sts))))
                  (last-hold-       (cadddr (cddddr (cddaar sts))))
                  (last-pc-reg      (car (cddddr (cddddr (cddaar sts)))))
                  (cntl-state       (cadr (cddddr (cddddr (cddaar sts)))))
                  (mem-state        (list (caaadr sts)
                                          (car (cdaadr sts))
                                          (cadr (cdaadr sts))
                                          (caddr (cdaadr sts))
                                          (cadddr (cdaadr sts))
                                          (car (cddddr (cdaadr sts)))
                                          (cadr (cddddr (cdaadr sts)))
                                          (caddr (cddddr (cdaadr sts)))))
                  (clk              (car inputs))
                  (ti               (cadr inputs))
                  (te               (caddr inputs))
                  (reset-           (cadddr inputs))
                  (hold-            (car (cddddr inputs)))
                  (disable-regfile- (cadr (cddddr inputs)))
                  (test-regfile-    (caddr (cddddr inputs)))
                  (pc-reg-in        (cdddr (cddddr inputs))))))))

(defthm chip-system=run-fm9001
  (implies (and (chip-system& netlist)
                (fm9001-state-structure sts)
                (chip-system-invariant sts)
                (chip-system-operating-inputs-p inputs n)
                (equal fm9001-inputs (map-up-inputs inputs)))
           (equal (de-sim-n 'chip-system inputs sts netlist n)
                  (run-fm9001 sts fm9001-inputs n)))
  :hints (("Goal"
           :in-theory (e/d (de-sim-n
                            chip-system=fm9001$step
                            run-fm9001-step-case
                            pc-reg-input)
                           ()))))
