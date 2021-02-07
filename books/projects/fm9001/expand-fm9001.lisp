;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

(in-package "FM9001")

(include-book "expand-fm9001-macros")
(include-book "fm9001-hardware")

;; ======================================================================

;; RUN-INPUTS-P inputs n

;; This predicate recognizes input streams that don't cause the machine to
;; enter the RESET state.

(defun run-inputs-p (inputs n)
  (declare (xargs :guard (and (true-list-listp inputs)
                              (natp n))))
  (if (zp n)
      t
    (and (equal (reset--input (car inputs)) t)
         (true-listp (pc-reg-input (car inputs)))
         (equal (len (pc-reg-input (car inputs))) 4)
         (run-inputs-p (cdr inputs) (1- n)))))

(defthm open-run-inputs-p
  (and
   (implies (zp n)
            (equal (run-inputs-p inputs n)
                   t))
   (implies (not (zp n))
            (equal (run-inputs-p inputs n)
                   (and (equal (reset--input (car inputs)) t)
                        (true-listp (pc-reg-input (car inputs)))
                        (equal (len (pc-reg-input (car inputs))) 4)
                        (run-inputs-p (cdr inputs) (1- n)))))))

(in-theory (disable run-inputs-p))

;; (defthm run-inputs-p-+
;;   (implies (and (natp m)
;;                 (natp n))
;;            (equal (run-inputs-p inputs (+ n m))
;;                   (and (run-inputs-p inputs n)
;;                        (run-inputs-p (nthcdr n inputs) m)))))

(defthm run-inputs-p-plus
  (implies (and (natp m)
                (natp n))
           (equal (run-inputs-p inputs (plus n m))
                  (and (run-inputs-p inputs n)
                       (run-inputs-p (nthcdr n inputs) m))))
  :hints (("Goal" :in-theory (enable plus))))

(defthm run-inputs-p-1
  (implies (and (run-inputs-p inputs n)
                (not (zp n)))
           (run-inputs-p inputs 1)))

(defthm open-run-inputs-p-add1
  (implies (natp n)
           (equal (run-inputs-p inputs (add1 n))
                  (and (equal (reset--input (car inputs)) t)
                       (true-listp (pc-reg-input (car inputs)))
                       (equal (len (pc-reg-input (car inputs))) 4)
                       (run-inputs-p (cdr inputs) n)))))

;; REGFILE-OKP regs

;; This predicate states that the register file RAM, and the address, data, and
;; write-enable latches are Boolean and the proper size.

(defun regfile-okp (regs)
  (declare (xargs :guard (true-list-alistp regs)))
  (and (equal (len regs) 4)
       (memory-okp 4 32 (caar regs))
       (all-ramp-mem 4 (caar regs))
       (booleanp (caadr regs))
       ;;(true-listp (caddr regs))
       (bvp (strip-cars (caddr regs))) (equal (len (caddr regs)) 32)
       ;;(true-listp (cadddr regs))
       (bvp (strip-cars (cadddr regs))) (equal (len (cadddr regs)) 4)))

;; ======================================================================

;; LOW LEVEL EXPANSION

(defthm rewrite-fm9001-next-state-for-step-lemmas
  (implies
   (and (bvp (strip-cars flags))
        (bvp (strip-cars a-reg))
        (bvp (strip-cars b-reg))
        (bvp (strip-cars i-reg))
        (bvp (strip-cars data-out))
        (bvp (strip-cars addr-out))
        (booleanp (car last-reset-))
        (booleanp (car last-dtack-))
        (booleanp (car last-hold-))
        (bvp (strip-cars last-pc-reg))
        (bvp (strip-cars cntl-state)))
   (equal
    (fm9001-next-state
     (list (list
            (list regs
                  flags
                  a-reg b-reg i-reg
                  data-out addr-out
                  last-reset- last-dtack- last-hold-
                  last-pc-reg cntl-state))
           (list mem-state))
     external-inputs)
    (let ((reset-    (reset--input external-inputs))
          (hold-     (hold--input  external-inputs))
          (pc-reg-in (pc-reg-input external-inputs))

          (major-state      (major-state      (strip-cars cntl-state)))
          (rw-              (rw-              (strip-cars cntl-state)))
          (strobe-          (strobe-          (strip-cars cntl-state)))
          (hdack-           (hdack-           (strip-cars cntl-state)))
          (we-regs          (we-regs          (strip-cars cntl-state)))
          (we-flags         (we-flags         (strip-cars cntl-state)))
          (we-a-reg         (we-a-reg         (strip-cars cntl-state)))
          (we-b-reg         (we-b-reg         (strip-cars cntl-state)))
          (we-i-reg         (we-i-reg         (strip-cars cntl-state)))
          (we-data-out      (we-data-out      (strip-cars cntl-state)))
          (we-addr-out      (we-addr-out      (strip-cars cntl-state)))
          (we-hold-         (we-hold-         (strip-cars cntl-state)))
          (we-pc-reg        (we-pc-reg        (strip-cars cntl-state)))
          (data-in-select   (data-in-select   (strip-cars cntl-state)))
          (dec-addr-out     (dec-addr-out     (strip-cars cntl-state)))
          (select-immediate (select-immediate (strip-cars cntl-state)))
          (regs-address     (regs-address     (strip-cars cntl-state)))
          (alu-c            (alu-c            (strip-cars cntl-state)))
          (alu-op           (alu-op           (strip-cars cntl-state)))
          (alu-zero         (alu-zero         (strip-cars cntl-state)))
          (alu-mpg          (alu-mpg          (strip-cars cntl-state))))
      (let ((ext-addr-out
             (v-pullup (vft-buf (f-buf hdack-)
                                (strip-cars addr-out))))
            (ext-rw-
             (f-pullup (ft-buf (f-buf hdack-) (f-buf  rw-))))
            (ext-strobe-
             (f-pullup (ft-buf (f-buf hdack-) strobe-)))
            (ext-data-out
             (vft-buf (f-not (f-buf rw-)) (strip-cars data-out))))
        (let ((mem-response
               (memory-value mem-state ext-strobe- ext-rw-
                             ext-addr-out
                             (make-list 32 :initial-element *X*))))
          (let ((reg-bus (f$extend-immediate
                          select-immediate
                          (a-immediate (strip-cars i-reg))
                          (f$read-regs regs-address regs)))
                (alu-bus (f$core-alu alu-c
                                     (strip-cars a-reg)
                                     (strip-cars b-reg)
                                     alu-zero alu-mpg alu-op
                                     (make-tree 32)))
                (dtack- (car mem-response))
                (data-in (v-threefix
                          (v-wire (v-pullup
                                   (v-wire ext-data-out
                                           (cdr mem-response)))
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
                 (f$write-regs we-regs regs-address regs (bv alu-bus))
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
                 (v-pullup
                  (v-wire ext-data-out
                          (cdr mem-response)))))))))))))
  :hints (("Goal" :in-theory (e/d (fm9001-next-state
                                    fm9001-hardware-state-accessors)
                                   (open-v-threefix
                                    f-gates=b-gates)))))

;; ======================================================================

;; SINGLE STEP SIMULATIONS

;; The STEP-FM9001 macro creates a lemma that describes the new state computed
;; by a single step of the low-level machine from a given initial state.  This
;; procedure is complicated by the fact that the next state depends on the
;; state of the memory.  Rather than produce a single lemma that captures the
;; behavior for all possible memory states, we create separate lemmas only for
;; those processor-state/memory-state configurations that are possible during
;; normal instruction execution.  This is important because if the memory
;; protocol is not followed, then unknown values may be loaded into the
;; processor registers.  What we are doing here is creating a state-by-state,
;; almost-Boolean specification of the low-level machine.  So we obviously want
;; to insure that the processor state remains Boolean.

;; STEP-FM9001 is defined in "expand-fm9001-macros.lisp".

;; Page numbers refer to the page numbers of the state diagram drawings,
;; e.g., Page 0 is the figure with caption ``States Figure 0'' in
;; Technical Report 86.

;; Page 0

;; (step-fm9001 fetch0 :suffix 0)
;; (step-fm9001 fetch0 :suffix 1 :mem-state 1)
;; (step-fm9001 fetch0 :suffix 2 :mem-state 2
;;              :addr-stable t :data-stable t :last-rw- nil
;;              :hyps (zp mem-count))

;; (step-fm9001 fetch1 :hyps (booleanp last-rw-) :last-rw- last-rw-)
;; (step-fm9001 fetch2 :addr-stable t :split-term (zp (car clock)))

;; (step-fm9001 fetch3 :suffix 0
;;              :addr-stable t :dtack- nil :mem-state 1 :mem-dtack t
;;              :hyps (zp mem-count))
;; (step-fm9001 fetch3 :suffix 1 :addr-stable t :dtack- t :mem-state 1
;;              :mem-dtack nil :split-term (zp mem-count))

;; (step-fm9001 decode :mem-state 1)

(make-event
 (step-fm9001 state 'fetch0 :suffix 0 :disable '(nfix)))

(make-event
 (step-fm9001 state 'fetch0 :suffix 1 :mem-state 1 :disable '(nfix)))

(make-event
 (step-fm9001 state 'fetch0 :suffix 2 :mem-state 2
              :addr-stable t :data-stable t :last-rw- nil :rw--for-hint nil
              :hyps '(zp mem-count)))

(make-event
 (step-fm9001 state 'fetch1 :hyps '(booleanp last-rw-) :last-rw- 'last-rw-
              :disable '(nfix) :split-term '(car hold-)))

(make-event
 (step-fm9001 state 'fetch2 :addr-stable t :split-term '(zp (car clock))))

(make-event
 (step-fm9001 state 'fetch3 :suffix 0
              :addr-stable t :dtack- ''(nil) :mem-state 1 :mem-dtack t
              :hyps '(zp mem-count)))

(make-event
 (step-fm9001 state 'fetch3 :suffix 1
              :addr-stable t :dtack- ''(t) :mem-state 1 :mem-dtack nil
              :split-term '(zp mem-count)))

(defthm decode$step
  (implies
   (and (cv-hyps t last-regs-address
                 last-i-reg last-flags last-pc-reg)
        (cv-hyps t (strip-cars pc-reg)
                 (strip-cars i-reg)
                 (strip-cars flags)
                 (strip-cars pc-reg))
        (memory-okp 32 32 mem)
        (regfile-okp regs)
        (len-1-true-listp flags)
        (len-1-true-listp a-reg)
        (bvp (strip-cars a-reg))
        (equal (len a-reg) 32)
        (len-1-true-listp b-reg)
        (bvp (strip-cars b-reg))
        (equal (len b-reg) 32)
        (len-1-true-listp i-reg)
        (len-1-true-listp addr-out)
        (bvp (strip-cars addr-out))
        (equal (len addr-out) 32)
        (len-1-true-listp data-out)
        (bvp (strip-cars data-out))
        (equal (len data-out) 32)
        (len-1-true-listp pc-reg)
        (not (zp n))
        (run-inputs-p inputs 1)
        (booleanp (car dtack-))
        (booleanp (car hold-))
        (equal (car reset-) t))
   (equal
    (run-fm9001
     (list (list
            (list
             regs flags a-reg b-reg i-reg data-out
             addr-out reset- dtack- hold- pc-reg
             (pairlis$ (cv_decode t last-regs-address
                                  last-i-reg last-flags last-pc-reg)
                       nil)))
           (list
            (list mem 1 clock mem-count
                  mem-dtack t last-address last-data)))
     inputs n)
    (run-fm9001
     (list (list
            (list
             (write-regs nil 0 regs 0)
             flags a-reg b-reg i-reg data-out addr-out
             '(t)
             '(t)
             (list (car hold-))
             pc-reg
             (pairlis$
              (b* ((a-immediate-p (a-immediate-p (strip-cars i-reg)))
                   (mode-a (mode-a (strip-cars i-reg)))
                   (mode-b (mode-b (strip-cars i-reg)))
                   (set-flags (set-flags (strip-cars i-reg)))
                   (store-cc (store-cc (strip-cars i-reg)))
                   (op-code (op-code (strip-cars i-reg)))
                   (a-immediate-p- (not* a-immediate-p))
                   (?store (store-resultp store-cc (strip-cars flags)))
                   (?set-some-flags (set-some-flags set-flags))
                   (?direct-a
                    (or* a-immediate-p (reg-direct-p mode-a)))
                   (?direct-b (reg-direct-p mode-b))
                   (unary (unary-op-code-p op-code))
                   (pre-dec-a (pre-dec-p mode-a))
                   (post-inc-a (post-inc-p mode-a))
                   (pre-dec-b (pre-dec-p mode-b))
                   (post-inc-b (post-inc-p mode-b))
                   (?side-effect-a (and* a-immediate-p-
                                         (or* pre-dec-a post-inc-a)))
                   (?side-effect-b (or* pre-dec-b post-inc-b)))
                (if*
                 (or* store set-some-flags)
                 (if*
                  direct-a
                  (if* (or* direct-b unary)
                       (cv_rega t last-pc-reg (strip-cars i-reg)
                                (strip-cars flags)
                                (strip-cars pc-reg))
                       (cv_readb0 t last-pc-reg (strip-cars i-reg)
                                  (strip-cars flags)
                                  (strip-cars pc-reg)))
                  (cv_reada0 t last-pc-reg (strip-cars i-reg)
                             (strip-cars flags)
                             (strip-cars pc-reg)))
                 (if*
                  side-effect-a
                  (cv_sefa0 t last-pc-reg (strip-cars i-reg)
                            (strip-cars flags)
                            (strip-cars pc-reg))
                  (if* side-effect-b
                       (cv_sefb0 t last-pc-reg (strip-cars i-reg)
                                 (strip-cars flags)
                                 (strip-cars pc-reg))
                       (cv_fetch0 t last-pc-reg (strip-cars i-reg)
                                  (strip-cars flags)
                                  (strip-cars pc-reg))))))
              nil)))
           (list
            (list mem 0 (consp-or-nil clock)
                  0 t t
                  (strip-cars addr-out)
                  (v-threefix last-data))))
     (cdr inputs)
     (+ -1 n))))
  :hints (("Goal"
           :use (:instance next-cntl-state$decode
                           (reset- t)
                           (dtack- (car dtack-))
                           (hold- (car hold-))
                           (rw- t)
                           (i-reg (strip-cars i-reg))
                           (flags (strip-cars flags))
                           (pc-reg (strip-cars pc-reg))
                           (regs-address last-pc-reg))
           :in-theory (e/d (run-fm9001-step-case
                             cv_decode$destructure
                             next-memory-state
                             memory-value
                             f-buf-delete-lemmas
                             fm9001-hardware-state-accessors)
                            (open-v-threefix
                             (make-list-ac)
                             make-list-ac-removal
                             (make-tree)
                             strip-cars
                             (alu-dec-op)
                             (alu-inc-op)
                             nfix)))))

;; Page 1

;; (step-fm9001 rega)
;; (step-fm9001 regb)
;; (step-fm9001 update :mem-state mem-state
;;                :hyps (or (equal mem-state 0) (equal mem-state 1)))

(defthm rega$step
  (implies
   (and (cv-hyps t last-regs-address
                 last-i-reg last-flags last-pc-reg)
        (cv-hyps t (strip-cars pc-reg)
                 (strip-cars i-reg)
                 (strip-cars flags)
                 (strip-cars pc-reg))
        (memory-okp 32 32 mem)
        (regfile-okp regs)
        (len-1-true-listp flags)
        (len-1-true-listp a-reg)
        (bvp (strip-cars a-reg))
        (equal (len a-reg) 32)
        (len-1-true-listp b-reg)
        (bvp (strip-cars b-reg))
        (equal (len b-reg) 32)
        (len-1-true-listp i-reg)
        (len-1-true-listp addr-out)
        (bvp (strip-cars addr-out))
        (equal (len addr-out) 32)
        (len-1-true-listp data-out)
        (bvp (strip-cars data-out))
        (equal (len data-out) 32)
        (len-1-true-listp pc-reg)
        (not (zp n))
        (run-inputs-p inputs 1)
        (booleanp (car dtack-))
        (booleanp (car hold-))
        (equal (car reset-) t))
   (equal
    (run-fm9001
     (list (list
            (list
             regs flags a-reg b-reg i-reg data-out
             addr-out reset- dtack- hold- pc-reg
             (pairlis$ (cv_rega t last-regs-address
                                last-i-reg last-flags last-pc-reg)
                       nil)))
           (list
            (list mem 0 clock mem-count
                  mem-dtack t last-address last-data)))
     inputs n)
    (run-fm9001
     (list (list
            (list
             (write-regs nil 0 regs 0)
             flags
             (pairlis$
              (if* (a-immediate-p last-i-reg)
                   (sign-extend (a-immediate (strip-cars i-reg))
                                32)
                   (read-regs (rn-a last-i-reg) regs))
              nil)
             b-reg i-reg data-out addr-out
             '(t)
             '(t)
             (list (car hold-))
             pc-reg
             (pairlis$
              (b* ((a-immediate-p (a-immediate-p (strip-cars i-reg)))
                   (mode-a (mode-a (strip-cars i-reg)))
                   (mode-b (mode-b (strip-cars i-reg)))
                   (set-flags (set-flags (strip-cars i-reg)))
                   (store-cc (store-cc (strip-cars i-reg)))
                   (op-code (op-code (strip-cars i-reg)))
                   (a-immediate-p- (not* a-immediate-p))
                   (?store (store-resultp store-cc (strip-cars flags)))
                   (?set-some-flags (set-some-flags set-flags))
                   (?direct-a
                    (or* a-immediate-p (reg-direct-p mode-a)))
                   (?direct-b (reg-direct-p mode-b))
                   (unary (unary-op-code-p op-code))
                   (pre-dec-a (pre-dec-p mode-a))
                   (post-inc-a (post-inc-p mode-a))
                   (pre-dec-b (pre-dec-p mode-b))
                   (post-inc-b (post-inc-p mode-b))
                   (?side-effect-a (and* a-immediate-p-
                                         (or* pre-dec-a post-inc-a)))
                   (?side-effect-b (or* pre-dec-b post-inc-b)))
                (if* direct-b
                     (if* unary
                          (cv_update t (rn-a last-i-reg)
                                     (strip-cars i-reg)
                                     (strip-cars flags)
                                     (strip-cars pc-reg))
                          (cv_regb t (rn-a last-i-reg)
                                   (strip-cars i-reg)
                                   (strip-cars flags)
                                   (strip-cars pc-reg)))
                     (if* store
                          (cv_write0 t (rn-a last-i-reg)
                                     (strip-cars i-reg)
                                     (strip-cars flags)
                                     (strip-cars pc-reg))
                          (cv_update t (rn-a last-i-reg)
                                     (strip-cars i-reg)
                                     (strip-cars flags)
                                     (strip-cars pc-reg)))))
              nil)))
           (list
            (list mem 0 (consp-or-nil clock)
                  0 t t
                  (strip-cars addr-out)
                  (v-threefix last-data))))
     (cdr inputs)
     (+ -1 n))))
  :hints (("Goal"
           :use (:instance next-cntl-state$rega
                           (reset- t)
                           (dtack- (car dtack-))
                           (hold- (car hold-))
                           (rw- t)
                           (i-reg (strip-cars i-reg))
                           (flags (strip-cars flags))
                           (pc-reg (strip-cars pc-reg))
                           (regs-address (rn-a last-i-reg)))
           :in-theory (e/d (run-fm9001-step-case
                             cv_rega$destructure
                             next-memory-state
                             memory-value
                             f-buf-delete-lemmas
                             fm9001-hardware-state-accessors)
                            (open-v-threefix
                             (make-list-ac)
                             make-list-ac-removal
                             (make-tree)
                             strip-cars
                             (alu-dec-op)
                             (alu-inc-op)
                             nfix)))))

(make-event
 (step-fm9001 state 'regb :regs-address '(rn-b last-i-reg)
              :disable '(nfix)))

(make-event
 (step-fm9001
  state 'update :mem-state 'mem-state
  :hyps '(or (equal mem-state 0) (equal mem-state 1))
  :regs-address '(rn-b last-i-reg) :disable '(nfix)
  :split-term '(and* (or* (pre-dec-p (mode-b (strip-cars i-reg)))
                          (post-inc-p (mode-b (strip-cars i-reg))))
                     (unary-op-code-p (op-code (strip-cars i-reg))))))

;; Page 2

;; (step-fm9001 reada0)
;; (step-fm9001 reada1)
;; (step-fm9001 reada2 :addr-stable t :split-term (zp (car clock)))

;; (step-fm9001 reada3 :suffix 0
;;                :addr-stable t :dtack- nil :mem-state 1 :mem-dtack t
;;                :hyps (zp mem-count))
;; (step-fm9001 reada3 :suffix 1 :addr-stable t :dtack- t :mem-state 1
;;              :mem-dtack nil :split-term (zp mem-count))

(make-event
 (step-fm9001 state 'reada0 :regs-address '(rn-a last-i-reg)
              :disable '(nfix if*)))

;; (make-event
;;  (step-fm9001 state 'reada1 :regs-address '(rn-a last-i-reg)
;;               :disable '(nfix)
;;               :split-term '(pre-dec-p (mode-a last-i-reg))))

(defthm reada1$step
  (implies
   (and (cv-hyps t last-regs-address
                 last-i-reg last-flags last-pc-reg)
        (cv-hyps t
                 (strip-cars pc-reg)
                 (strip-cars i-reg)
                 (strip-cars flags)
                 (strip-cars pc-reg))
        (memory-okp 32 32 mem)
        (regfile-okp regs)
        (len-1-true-listp flags)
        (len-1-true-listp a-reg)
        (bvp (strip-cars a-reg))
        (equal (len a-reg) 32)
        (len-1-true-listp b-reg)
        (bvp (strip-cars b-reg))
        (equal (len b-reg) 32)
        (len-1-true-listp i-reg)
        (len-1-true-listp addr-out)
        (bvp (strip-cars addr-out))
        (equal (len addr-out) 32)
        (len-1-true-listp data-out)
        (bvp (strip-cars data-out))
        (equal (len data-out) 32)
        (len-1-true-listp pc-reg)
        (not (zp n))
        (run-inputs-p inputs 1)
        (booleanp (car dtack-))
        (booleanp (car hold-))
        (equal (car reset-) t))
   (equal
    (run-fm9001
     (list (list
            (list
             regs flags a-reg b-reg i-reg data-out
             addr-out reset- dtack- hold- pc-reg
             (pairlis$ (cv_reada1 t last-regs-address
                                  last-i-reg last-flags last-pc-reg)
                       nil)))
           (list
            (list mem 0 clock mem-count
                  mem-dtack t last-address last-data)))
     inputs
     n)
    (run-fm9001
     (list (list
            (list
             (write-regs
              (binary-and*
               (not* (a-immediate-p last-i-reg))
               (binary-or* (pre-dec-p (mode-a last-i-reg))
                           (post-inc-p (mode-a last-i-reg))))
              (rn-a last-i-reg)
              regs
              (if* (pre-dec-p (mode-a last-i-reg))
                   (v-dec (strip-cars a-reg))
                   (v-inc (strip-cars a-reg))))
             flags
             a-reg b-reg i-reg data-out addr-out
             '(t)
             '(t)
             (list (car hold-))
             pc-reg
             (pairlis$ (cv_reada2 t
                                  (rn-a last-i-reg)
                                  (strip-cars i-reg)
                                  (strip-cars flags)
                                  (strip-cars pc-reg))
                       nil)))
           (list
            (list mem 0 (consp-or-nil clock)
                  0 t t (strip-cars addr-out)
                  (v-threefix last-data))))
     (cdr inputs)
     (+ -1 n))))
  :hints (("Goal"
           :use (:instance next-cntl-state$reada1
                           (reset- t)
                           (dtack- (car dtack-))
                           (hold- (car hold-))
                           (rw- t)
                           (i-reg (strip-cars i-reg))
                           (flags (strip-cars flags))
                           (pc-reg (strip-cars pc-reg))
                           (regs-address (rn-a last-i-reg)))
           :in-theory (e/d (run-fm9001-step-case
                             cv_reada1$destructure
                             next-memory-state
                             memory-value
                             f-buf-delete-lemmas
                             fm9001-hardware-state-accessors)
                            (open-v-threefix
                             (make-list-ac)
                             make-list-ac-removal
                             (make-tree)
                             strip-cars
                             (alu-dec-op)
                             (alu-inc-op)
                             nfix)))))

(make-event
 (step-fm9001 state 'reada2 :addr-stable t :regs-address '(rn-b last-i-reg)
              :split-term '(zp (car clock))))

(defthm reada3$step0
  (implies
   (and (cv-hyps t last-regs-address
                 last-i-reg last-flags last-pc-reg)
        (cv-hyps t (strip-cars pc-reg)
                 (strip-cars i-reg)
                 (strip-cars flags)
                 (strip-cars pc-reg))
        (memory-okp 32 32 mem)
        (regfile-okp regs)
        (len-1-true-listp flags)
        (len-1-true-listp a-reg)
        (bvp (strip-cars a-reg))
        (equal (len a-reg) 32)
        (len-1-true-listp b-reg)
        (bvp (strip-cars b-reg))
        (equal (len b-reg) 32)
        (len-1-true-listp i-reg)
        (len-1-true-listp addr-out)
        (bvp (strip-cars addr-out))
        (equal (len addr-out) 32)
        (len-1-true-listp data-out)
        (bvp (strip-cars data-out))
        (equal (len data-out) 32)
        (len-1-true-listp pc-reg)
        (not (zp n))
        (run-inputs-p inputs 1)
        (booleanp (car '(nil)))
        (booleanp (car hold-))
        (equal (car reset-) t)
        (equal last-address (strip-cars addr-out))
        (zp mem-count))
   (equal
    (run-fm9001
     (list (list
            (list
             regs flags a-reg b-reg
             i-reg data-out addr-out reset- '(nil)
             hold- pc-reg
             (pairlis$ (cv_reada3 t last-regs-address
                                  last-i-reg last-flags last-pc-reg)
                       nil)))
           (list
            (list mem 1 clock
                  mem-count t t last-address last-data)))
     inputs n)
    (run-fm9001
     (list (list
            (list
             (write-regs nil 0 regs 0)
             flags
             (pairlis$ (read-mem (strip-cars addr-out) mem)
                       nil)
             b-reg i-reg data-out addr-out
             '(t)
             '(nil)
             (list (car hold-))
             pc-reg
             (pairlis$
              (b* ((a-immediate-p (a-immediate-p (strip-cars i-reg)))
                   (mode-a (mode-a (strip-cars i-reg)))
                   (mode-b (mode-b (strip-cars i-reg)))
                   (set-flags (set-flags (strip-cars i-reg)))
                   (store-cc (store-cc (strip-cars i-reg)))
                   (op-code (op-code (strip-cars i-reg)))
                   (a-immediate-p- (not* a-immediate-p))
                   (?store (store-resultp store-cc (strip-cars flags)))
                   (?set-some-flags (set-some-flags set-flags))
                   (?direct-a
                    (or* a-immediate-p (reg-direct-p mode-a)))
                   (?direct-b (reg-direct-p mode-b))
                   (unary (unary-op-code-p op-code))
                   (pre-dec-a (pre-dec-p mode-a))
                   (post-inc-a (post-inc-p mode-a))
                   (pre-dec-b (pre-dec-p mode-b))
                   (post-inc-b (post-inc-p mode-b))
                   (?side-effect-a (and* a-immediate-p-
                                         (or* pre-dec-a post-inc-a)))
                   (?side-effect-b (or* pre-dec-b post-inc-b)))
                (if*
                 direct-b
                 (cv_update t last-pc-reg (strip-cars i-reg)
                            (strip-cars flags)
                            (strip-cars pc-reg))
                 (if*
                  unary
                  (if* store
                       (cv_write0 t last-pc-reg (strip-cars i-reg)
                                  (strip-cars flags)
                                  (strip-cars pc-reg))
                       (cv_update t last-pc-reg (strip-cars i-reg)
                                  (strip-cars flags)
                                  (strip-cars pc-reg)))
                  (cv_readb0 t last-pc-reg (strip-cars i-reg)
                             (strip-cars flags)
                             (strip-cars pc-reg)))))
              nil)))
           (list
            (list mem 1 (consp-or-nil clock)
                  -1 t t
                  (strip-cars addr-out)
                  (v-threefix last-data))))
     (cdr inputs)
     (+ -1 n))))
  :hints (("Goal"
           :use (:instance next-cntl-state$reada3
                           (reset- t)
                           (dtack- (car '(nil)))
                           (hold- (car hold-))
                           (rw- t)
                           (i-reg (strip-cars i-reg))
                           (flags (strip-cars flags))
                           (pc-reg (strip-cars pc-reg))
                           (regs-address last-pc-reg))
           :in-theory (e/d (run-fm9001-step-case
                             cv_reada3$destructure
                             next-memory-state
                             memory-value
                             f-buf-delete-lemmas
                             fm9001-hardware-state-accessors)
                            (open-v-threefix
                             (make-list-ac)
                             make-list-ac-removal
                             (make-tree)
                             strip-cars
                             (alu-dec-op)
                             (alu-inc-op))))))

(make-event
 (step-fm9001 state 'reada3 :suffix 1
              :addr-stable t :dtack- ''(t) :mem-state 1 :mem-dtack nil
              :split-term '(zp mem-count)))

;; Page 3

;; (step-fm9001 readb0 :mem-state mem-state
;;                :hyps (or (equal mem-state 0) (equal mem-state 1)))
;; (step-fm9001 readb1)
;; (step-fm9001 readb2 :addr-stable t :split-term (zp (car clock)))

;; (step-fm9001 readb3 :suffix 0
;;                :addr-stable t :dtack- nil :mem-state 1 :mem-dtack t
;;                :hyps (zp mem-count))
;; (step-fm9001 readb3 :suffix 1 :addr-stable t :dtack- t :mem-state 1
;;              :mem-dtack nil :split-term (zp mem-count))

(make-event
 (step-fm9001 state 'readb0 :mem-state 'mem-state
              :hyps '(or (equal mem-state 0) (equal mem-state 1))
              :regs-address '(rn-b last-i-reg) :disable '(nfix if*)))

(defthm readb1$step
  (implies
   (and (cv-hyps t last-regs-address
                 last-i-reg last-flags last-pc-reg)
        (cv-hyps t
                 (strip-cars pc-reg)
                 (strip-cars i-reg)
                 (strip-cars flags)
                 (strip-cars pc-reg))
        (memory-okp 32 32 mem)
        (regfile-okp regs)
        (len-1-true-listp flags)
        (len-1-true-listp a-reg)
        (bvp (strip-cars a-reg))
        (equal (len a-reg) 32)
        (len-1-true-listp b-reg)
        (bvp (strip-cars b-reg))
        (equal (len b-reg) 32)
        (len-1-true-listp i-reg)
        (len-1-true-listp addr-out)
        (bvp (strip-cars addr-out))
        (equal (len addr-out) 32)
        (len-1-true-listp data-out)
        (bvp (strip-cars data-out))
        (equal (len data-out) 32)
        (len-1-true-listp pc-reg)
        (not (zp n))
        (run-inputs-p inputs 1)
        (booleanp (car dtack-))
        (booleanp (car hold-))
        (equal (car reset-) t))
   (equal
    (run-fm9001
     (list (list
            (list
             regs flags a-reg b-reg i-reg data-out
             addr-out reset- dtack- hold- pc-reg
             (pairlis$ (cv_readb1 t last-regs-address
                                  last-i-reg last-flags last-pc-reg)
                       nil)))
           (list
            (list mem 0 clock mem-count
                  mem-dtack t last-address last-data)))
     inputs n)
    (run-fm9001
     (list (list
            (list
             (write-regs nil 0 regs 0)
             flags
             (pairlis$
              (if* (a-immediate-p last-i-reg)
                   (sign-extend (a-immediate (strip-cars i-reg))
                                32)
                   (if* (reg-direct-p (mode-a last-i-reg))
                        (read-regs (rn-a last-i-reg) regs)
                        (strip-cars a-reg)))
              nil)
             b-reg i-reg data-out addr-out
             '(t)
             '(t)
             (list (car hold-))
             pc-reg
             (pairlis$ (cv_readb2 t
                                  (rn-a last-i-reg)
                                  (strip-cars i-reg)
                                  (strip-cars flags)
                                  (strip-cars pc-reg))
                       nil)))
           (list
            (list mem 0 (consp-or-nil clock)
                  0 t t
                  (strip-cars addr-out)
                  (v-threefix last-data))))
     (cdr inputs)
     (+ -1 n))))
  :hints (("Goal"
           :use (:instance next-cntl-state$readb1
                           (reset- t)
                           (dtack- (car dtack-))
                           (hold- (car hold-))
                           (rw- t)
                           (i-reg (strip-cars i-reg))
                           (flags (strip-cars flags))
                           (pc-reg (strip-cars pc-reg))
                           (regs-address (rn-a last-i-reg)))
           :in-theory (e/d (run-fm9001-step-case
                             cv_readb1$destructure
                             next-memory-state
                             memory-value
                             f-buf-delete-lemmas
                             fm9001-hardware-state-accessors
                             binary-or*)
                            (open-v-threefix
                             (make-list-ac)
                             make-list-ac-removal
                             (make-tree)
                             strip-cars
                             (alu-dec-op)
                             (alu-inc-op)
                             nfix)))))

(defthm readb2$step
  (implies
   (and (cv-hyps t last-regs-address
                 last-i-reg last-flags last-pc-reg)
        (cv-hyps t
                 (strip-cars pc-reg)
                 (strip-cars i-reg)
                 (strip-cars flags)
                 (strip-cars pc-reg))
        (memory-okp 32 32 mem)
        (regfile-okp regs)
        (len-1-true-listp flags)
        (len-1-true-listp a-reg)
        (bvp (strip-cars a-reg))
        (equal (len a-reg) 32)
        (len-1-true-listp b-reg)
        (bvp (strip-cars b-reg))
        (equal (len b-reg) 32)
        (len-1-true-listp i-reg)
        (len-1-true-listp addr-out)
        (bvp (strip-cars addr-out))
        (equal (len addr-out) 32)
        (len-1-true-listp data-out)
        (bvp (strip-cars data-out))
        (equal (len data-out) 32)
        (len-1-true-listp pc-reg)
        (not (zp n))
        (run-inputs-p inputs 1)
        (booleanp (car dtack-))
        (booleanp (car hold-))
        (equal (car reset-) t)
        (equal last-address (strip-cars addr-out)))
   (equal
    (run-fm9001
     (list (list
            (list
             regs flags a-reg b-reg i-reg data-out
             addr-out reset- dtack- hold- pc-reg
             (pairlis$ (cv_readb2 t last-regs-address
                                  last-i-reg last-flags last-pc-reg)
                       nil)))
           (list
            (list mem 0 clock mem-count
                  mem-dtack t last-address last-data)))
     inputs n)
    (if (zp (car clock))
        (run-fm9001
         (list (list
                (list
                 (write-regs
                  (binary-and*
                   (not* (store-resultp (store-cc last-i-reg)
                                        last-flags))
                   (binary-or* (pre-dec-p (mode-b last-i-reg))
                               (post-inc-p (mode-b last-i-reg))))
                  (rn-b last-i-reg)
                  regs
                  (if* (pre-dec-p (mode-b last-i-reg))
                       (v-dec (strip-cars b-reg))
                       (v-inc (strip-cars b-reg))))
                 flags a-reg b-reg i-reg data-out addr-out
                 '(t)
                 '(nil)
                 (list (car hold-))
                 pc-reg
                 (pairlis$ (cv_readb3 t
                                      (rn-b last-i-reg)
                                      (strip-cars i-reg)
                                      (strip-cars flags)
                                      (strip-cars pc-reg))
                           nil)))
               (list
                (list mem 1 (cdr clock)
                      -1 t t
                      (strip-cars addr-out)
                      (v-threefix last-data))))
         (cdr inputs)
         (+ -1 n))
      (run-fm9001
       (list (list
              (list
               (write-regs
                (binary-and*
                 (not* (store-resultp (store-cc last-i-reg)
                                      last-flags))
                 (binary-or* (pre-dec-p (mode-b last-i-reg))
                             (post-inc-p (mode-b last-i-reg))))
                (rn-b last-i-reg)
                regs
                (if* (pre-dec-p (mode-b last-i-reg))
                     (v-dec (strip-cars b-reg))
                     (v-inc (strip-cars b-reg))))
               flags a-reg b-reg i-reg data-out addr-out
               '(t)
               '(t)
               (list (car hold-))
               pc-reg
               (pairlis$ (cv_readb3 t
                                    (rn-b last-i-reg)
                                    (strip-cars i-reg)
                                    (strip-cars flags)
                                    (strip-cars pc-reg))
                         nil)))
             (list
              (list mem 1 (cdr clock)
                    (1- (car clock))
                    nil t
                    (strip-cars addr-out)
                    (v-threefix last-data))))
       (cdr inputs)
       (+ -1 n)))))
  :hints (("Goal"
           :use (:instance next-cntl-state$readb2
                           (reset- t)
                           (dtack- (car dtack-))
                           (hold- (car hold-))
                           (rw- t)
                           (i-reg (strip-cars i-reg))
                           (flags (strip-cars flags))
                           (pc-reg (strip-cars pc-reg))
                           (regs-address (rn-b last-i-reg)))
           :in-theory (e/d (run-fm9001-step-case
                             cv_readb2$destructure
                             next-memory-state
                             memory-value
                             f-buf-delete-lemmas
                             fm9001-hardware-state-accessors)
                            (open-v-threefix
                             (make-list-ac)
                             make-list-ac-removal
                             (make-tree)
                             strip-cars
                             (alu-dec-op)
                             (alu-inc-op))))))

;; (make-event
;;  (step-fm9001 state 'readb3 :suffix 0
;;               :addr-stable t :dtack- ''(nil) :mem-state 1 :mem-dtack t
;;               :hyps '(zp mem-count)
;;               :split-term '(store-resultp (store-cc (strip-cars i-reg))
;;                                           (strip-cars flags))))

(defthm readb3$step0
  (implies
   (and (cv-hyps t last-regs-address
                 last-i-reg last-flags last-pc-reg)
        (cv-hyps t
                 (strip-cars pc-reg)
                 (strip-cars i-reg)
                 (strip-cars flags)
                 (strip-cars pc-reg))
        (memory-okp 32 32 mem)
        (regfile-okp regs)
        (len-1-true-listp flags)
        (len-1-true-listp a-reg)
        (bvp (strip-cars a-reg))
        (equal (len a-reg) 32)
        (len-1-true-listp b-reg)
        (bvp (strip-cars b-reg))
        (equal (len b-reg) 32)
        (len-1-true-listp i-reg)
        (len-1-true-listp addr-out)
        (bvp (strip-cars addr-out))
        (equal (len addr-out) 32)
        (len-1-true-listp data-out)
        (bvp (strip-cars data-out))
        (equal (len data-out) 32)
        (len-1-true-listp pc-reg)
        (not (zp n))
        (run-inputs-p inputs 1)
        (booleanp (car '(nil)))
        (booleanp (car hold-))
        (equal (car reset-) t)
        (equal last-address (strip-cars addr-out))
        (zp mem-count))
   (equal
    (run-fm9001
     (list (list
            (list
             regs flags a-reg b-reg
             i-reg data-out addr-out reset- '(nil)
             hold- pc-reg
             (pairlis$ (cv_readb3 t last-regs-address
                                  last-i-reg last-flags last-pc-reg)
                       nil)))
           (list
            (list mem 1 clock
                  mem-count t t last-address last-data)))
     inputs
     n)
    (run-fm9001
     (list (list
            (list
             (write-regs nil 0 regs 0)
             flags a-reg
             (pairlis$ (read-mem (strip-cars addr-out) mem)
                       nil)
             i-reg data-out addr-out
             '(t)
             '(nil)
             (list (car hold-))
             pc-reg
             (pairlis$
              (if* (store-resultp (store-cc (strip-cars i-reg))
                                  (strip-cars flags))
                   (cv_write0 t
                              last-pc-reg
                              (strip-cars i-reg)
                              (strip-cars flags)
                              (strip-cars pc-reg))
                   (cv_update t
                              last-pc-reg
                              (strip-cars i-reg)
                              (strip-cars flags)
                              (strip-cars pc-reg)))
              nil)))
           (list
            (list mem 1 (consp-or-nil clock)
                  -1 t t (strip-cars addr-out)
                  (v-threefix last-data))))
     (cdr inputs)
     (+ -1 n))))
  :hints (("Goal"
           :use (:instance next-cntl-state$readb3
                           (reset- t)
                           (dtack- (car '(nil)))
                           (hold- (car hold-))
                           (rw- t)
                           (i-reg (strip-cars i-reg))
                           (flags (strip-cars flags))
                           (pc-reg (strip-cars pc-reg))
                           (regs-address last-pc-reg))
           :in-theory
           (e/d (run-fm9001-step-case
                  cv_readb3$destructure
                  next-memory-state
                  memory-value
                  f-buf-delete-lemmas
                  fm9001-hardware-state-accessors)
                 (open-v-threefix
                  (make-list-ac)
                  make-list-ac-removal
                  (make-tree)
                  strip-cars
                  (alu-dec-op)
                  (alu-inc-op))))))

(make-event
 (step-fm9001 state 'readb3 :suffix 1
              :addr-stable t :dtack- ''(t) :mem-state 1 :mem-dtack nil
              :split-term '(zp mem-count)))

;; Page 4

;; (step-fm9001 write0 :mem-state mem-state
;;                :hyps (or (equal mem-state 0) (equal mem-state 1)))
;; (step-fm9001 write1)
;; (step-fm9001 write2 :last-rw- nil :addr-stable t :data-stable t
;;              :split-term (zp (car clock)))

;; (step-fm9001 write3 :suffix 0
;;                :addr-stable t :data-stable t :dtack- nil :mem-state 2
;;                :mem-dtack t :last-rw- nil
;;                :hyps (zp mem-count))
;; (step-fm9001 write3 :suffix 1 :addr-stable t :data-stable t :dtack- t
;;              :mem-state 2 :mem-dtack nil :last-rw- nil
;;              :split-term (zp mem-count))

(make-event
 (step-fm9001 state 'write0 :mem-state 'mem-state
              :hyps '(or (equal mem-state 0) (equal mem-state 1))
              :regs-address '(rn-b last-i-reg) :disable '(if* nfix)))

;; (make-event
;;  (step-fm9001 state 'write1 :rw--for-hint nil
;;               :regs-address '(rn-b last-i-reg) :disable '(nfix)
;;               :split-term '(pre-dec-p (mode-b last-i-reg))))

(defthm write1$step
  (implies
   (and (cv-hyps t last-regs-address
                 last-i-reg last-flags last-pc-reg)
        (cv-hyps t
                 (strip-cars pc-reg)
                 (strip-cars i-reg)
                 (strip-cars flags)
                 (strip-cars pc-reg))
        (memory-okp 32 32 mem)
        (regfile-okp regs)
        (len-1-true-listp flags)
        (len-1-true-listp a-reg)
        (bvp (strip-cars a-reg))
        (equal (len a-reg) 32)
        (len-1-true-listp b-reg)
        (bvp (strip-cars b-reg))
        (equal (len b-reg) 32)
        (len-1-true-listp i-reg)
        (len-1-true-listp addr-out)
        (bvp (strip-cars addr-out))
        (equal (len addr-out) 32)
        (len-1-true-listp data-out)
        (bvp (strip-cars data-out))
        (equal (len data-out) 32)
        (len-1-true-listp pc-reg)
        (not (zp n))
        (run-inputs-p inputs 1)
        (booleanp (car dtack-))
        (booleanp (car hold-))
        (equal (car reset-) t))
   (equal
    (run-fm9001
     (list (list
            (list
             regs flags a-reg b-reg i-reg data-out
             addr-out reset- dtack- hold- pc-reg
             (pairlis$ (cv_write1 t last-regs-address
                                  last-i-reg last-flags last-pc-reg)
                       nil)))
           (list
            (list mem 0 clock mem-count
                  mem-dtack t last-address last-data)))
     inputs
     n)
    (run-fm9001
     (list (list
            (list
             (write-regs
              (binary-or* (pre-dec-p (mode-b last-i-reg))
                          (post-inc-p (mode-b last-i-reg)))
              (rn-b last-i-reg)
              regs
              (if* (pre-dec-p (mode-b last-i-reg))
                   (v-dec (strip-cars b-reg))
                   (v-inc (strip-cars b-reg))))
             flags
             a-reg b-reg i-reg data-out addr-out
             '(t)
             '(t)
             (list (car hold-))
             pc-reg
             (pairlis$ (cv_write2 nil
                                  (rn-b last-i-reg)
                                  (strip-cars i-reg)
                                  (strip-cars flags)
                                  (strip-cars pc-reg))
                       nil)))
           (list
            (list mem 0 (consp-or-nil clock)
                  0 t nil (strip-cars addr-out)
                  (strip-cars data-out))))
     (cdr inputs)
     (+ -1 n))))
  :hints (("Goal"
           :use (:instance next-cntl-state$write1
                           (reset- t)
                           (dtack- (car dtack-))
                           (hold- (car hold-))
                           (rw- nil)
                           (i-reg (strip-cars i-reg))
                           (flags (strip-cars flags))
                           (pc-reg (strip-cars pc-reg))
                           (regs-address (rn-b last-i-reg)))
           :in-theory (e/d (run-fm9001-step-case
                             cv_write1$destructure
                             next-memory-state
                             memory-value
                             f-buf-delete-lemmas
                             fm9001-hardware-state-accessors)
                            (open-v-threefix
                             (make-list-ac)
                             make-list-ac-removal
                             (make-tree)
                             strip-cars
                             (alu-dec-op)
                             (alu-inc-op)
                             nfix)))))

(make-event
 (step-fm9001 state 'write2 :last-rw- nil :addr-stable t :data-stable t
              :rw--for-hint nil :split-term '(zp (car clock))))

(make-event
 (step-fm9001 state 'write3 :suffix 0
              :addr-stable t :data-stable t :dtack- ''(nil) :mem-state 2
              :mem-dtack t :last-rw- nil :rw--for-hint nil
              :hyps '(zp mem-count)))

(make-event
 (step-fm9001 state 'write3 :suffix 1
              :addr-stable t :data-stable t :dtack- ''(t)
              :mem-state 2 :mem-dtack nil :last-rw- nil :rw--for-hint nil
              :split-term '(zp mem-count)))

;; Page 5

;; (step-fm9001 sefa0)
;; (step-fm9001 sefa1)
;; (step-fm9001 sefb0)
;; (step-fm9001 sefb1)

(make-event
 (step-fm9001 state 'sefa0 :regs-address '(rn-a last-i-reg)
              :disable '(nfix)))

(defthm sefa1$step
  (implies
   (and (cv-hyps t last-regs-address
                 last-i-reg last-flags last-pc-reg)
        (cv-hyps t (strip-cars pc-reg)
                 (strip-cars i-reg)
                 (strip-cars flags)
                 (strip-cars pc-reg))
        (memory-okp 32 32 mem)
        (regfile-okp regs)
        (len-1-true-listp flags)
        (len-1-true-listp a-reg)
        (bvp (strip-cars a-reg))
        (equal (len a-reg) 32)
        (len-1-true-listp b-reg)
        (bvp (strip-cars b-reg))
        (equal (len b-reg) 32)
        (len-1-true-listp i-reg)
        (len-1-true-listp addr-out)
        (bvp (strip-cars addr-out))
        (equal (len addr-out) 32)
        (len-1-true-listp data-out)
        (bvp (strip-cars data-out))
        (equal (len data-out) 32)
        (len-1-true-listp pc-reg)
        (not (zp n))
        (run-inputs-p inputs 1)
        (booleanp (car dtack-))
        (booleanp (car hold-))
        (equal (car reset-) t))
   (equal
    (run-fm9001
     (list (list
            (list
             regs flags a-reg b-reg i-reg data-out
             addr-out reset- dtack- hold- pc-reg
             (pairlis$ (cv_sefa1 t last-regs-address
                                 last-i-reg last-flags last-pc-reg)
                       nil)))
           (list
            (list mem 0 clock mem-count
                  mem-dtack t last-address last-data)))
     inputs n)
    (run-fm9001
     (list (list
            (list
             (write-regs t (rn-a last-i-reg)
                         regs
                         (if* (pre-dec-p (mode-a last-i-reg))
                              (v-dec (strip-cars a-reg))
                              (v-inc (strip-cars a-reg))))
             flags a-reg b-reg i-reg data-out addr-out
             '(t)
             '(t)
             (list (car hold-))
             pc-reg
             (pairlis$
              (if* (or* (pre-dec-p (mode-b (strip-cars i-reg)))
                        (post-inc-p (mode-b (strip-cars i-reg))))
                   (cv_sefb0 t
                             (rn-a last-i-reg)
                             (strip-cars i-reg)
                             (strip-cars flags)
                             (strip-cars pc-reg))
                   (cv_fetch0 t
                              (rn-a last-i-reg)
                              (strip-cars i-reg)
                              (strip-cars flags)
                              (strip-cars pc-reg)))
              nil)))
           (list
            (list mem 0 (consp-or-nil clock)
                  0 t t
                  (strip-cars addr-out)
                  (v-threefix last-data))))
     (cdr inputs)
     (+ -1 n))))
  :hints (("Goal"
           :use (:instance next-cntl-state$sefa1
                           (reset- t)
                           (dtack- (car dtack-))
                           (hold- (car hold-))
                           (rw- t)
                           (i-reg (strip-cars i-reg))
                           (flags (strip-cars flags))
                           (pc-reg (strip-cars pc-reg))
                           (regs-address (rn-a last-i-reg)))
           :in-theory (e/d (run-fm9001-step-case
                             cv_sefa1$destructure
                             next-memory-state
                             memory-value
                             f-buf-delete-lemmas
                             fm9001-hardware-state-accessors)
                            (open-v-threefix
                             (make-list-ac)
                             make-list-ac-removal
                             (make-tree)
                             strip-cars
                             (alu-dec-op)
                             (alu-inc-op)
                             nfix)))))

(make-event
 (step-fm9001 state 'sefb0 :regs-address '(rn-b last-i-reg)
              :disable '(nfix)))

;; (make-event
;;  (step-fm9001 state 'sefb1 :regs-address '(rn-b last-i-reg)
;;               :disable '(nfix)
;;               :split-term '(pre-dec-p (mode-b last-i-reg))))

(defthm sefb1$step
  (implies
   (and (cv-hyps t last-regs-address
                 last-i-reg last-flags last-pc-reg)
        (cv-hyps t
                 (strip-cars pc-reg)
                 (strip-cars i-reg)
                 (strip-cars flags)
                 (strip-cars pc-reg))
        (memory-okp 32 32 mem)
        (regfile-okp regs)
        (len-1-true-listp flags)
        (len-1-true-listp a-reg)
        (bvp (strip-cars a-reg))
        (equal (len a-reg) 32)
        (len-1-true-listp b-reg)
        (bvp (strip-cars b-reg))
        (equal (len b-reg) 32)
        (len-1-true-listp i-reg)
        (len-1-true-listp addr-out)
        (bvp (strip-cars addr-out))
        (equal (len addr-out) 32)
        (len-1-true-listp data-out)
        (bvp (strip-cars data-out))
        (equal (len data-out) 32)
        (len-1-true-listp pc-reg)
        (not (zp n))
        (run-inputs-p inputs 1)
        (booleanp (car dtack-))
        (booleanp (car hold-))
        (equal (car reset-) t))
   (equal
    (run-fm9001
     (list (list
            (list
             regs flags a-reg b-reg i-reg data-out
             addr-out reset- dtack- hold- pc-reg
             (pairlis$ (cv_sefb1 t last-regs-address
                                 last-i-reg last-flags last-pc-reg)
                       nil)))
           (list
            (list mem 0 clock mem-count
                  mem-dtack t last-address last-data)))
     inputs
     n)
    (run-fm9001
     (list (list
            (list (write-regs t (rn-b last-i-reg)
                              regs
                              (if* (pre-dec-p (mode-b last-i-reg))
                                   (v-dec (strip-cars b-reg))
                                   (v-inc (strip-cars b-reg))))
                  flags
                  a-reg b-reg i-reg data-out addr-out
                  '(t)
                  '(t)
                  (list (car hold-))
                  pc-reg
                  (pairlis$ (cv_fetch0 t
                                       (rn-b last-i-reg)
                                       (strip-cars i-reg)
                                       (strip-cars flags)
                                       (strip-cars pc-reg))
                            nil)))
           (list
            (list mem 0 (consp-or-nil clock)
                  0 t t (strip-cars addr-out)
                  (v-threefix last-data))))
     (cdr inputs)
     (+ -1 n))))
  :hints (("Goal"
           :use (:instance next-cntl-state$sefb1
                           (reset- t)
                           (dtack- (car dtack-))
                           (hold- (car hold-))
                           (rw- t)
                           (i-reg (strip-cars i-reg))
                           (flags (strip-cars flags))
                           (pc-reg (strip-cars pc-reg))
                           (regs-address (rn-b last-i-reg)))
           :in-theory (e/d (run-fm9001-step-case
                             cv_sefb1$destructure
                             next-memory-state
                             memory-value
                             f-buf-delete-lemmas
                             fm9001-hardware-state-accessors)
                            (open-v-threefix
                             (make-list-ac)
                             make-list-ac-removal
                             (make-tree)
                             strip-cars
                             (alu-dec-op)
                             (alu-inc-op)
                             nfix)))))


(deftheory fm9001-step-theory
  '(sefb1$step sefb0$step sefa1$step sefa0$step write3$step1 write3$step0
               write2$step write1$step write0$step readb3$step1 readb3$step0
               readb2$step readb1$step readb0$step reada3$step1 reada3$step0
               reada2$step reada1$step reada0$step update$step regb$step
               rega$step decode$step fetch3$step1 fetch3$step0 fetch2$step
               fetch1$step fetch0$step2 fetch0$step1 fetch0$step0))


#|
;; Page 6

It was never necessary to expand these states.

(step-fm9001 hold0)
(step-fm9001 hold1)

(step-fm9001 reset0)
(step-fm9001 reset1)
(step-fm9001 reset2)

|#

;; ======================================================================

;; Inductive progress proofs

;; For each of the states that wait for memory, we must prove that the
;; processor will eventually move on.  The lemmas below tell how long the
;; processor will remain in a given state, before the internal registers are in
;; such a condition that the machine will leave that state on the next clock
;; cycle.



;;  READ-FN reg clock n

;;  READ-FN gives the value produced by the ABI-MUX as we wait for DTACK.

(defun read-fn (reg0 reg1 n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      reg0
    (read-fn reg1 reg1 (1- n))))

(defthm open-read-fn
  (and
   (implies (zp n)
            (equal (read-fn reg0 reg1 n)
                   reg0))
   (implies (not (zp n))
            (equal (read-fn reg0 reg1 n)
                   reg1))))

(defthm len-read-fn
  (implies (and (equal (len reg0) 32)
                (equal (len reg1) 32))
           (equal (len (read-fn reg0 reg1 n)) 32)))

(defthm true-listp-read-fn
  (implies (and (true-listp reg0)
                (true-listp reg1))
           (true-listp (read-fn reg0 reg1 n)))
  :rule-classes :type-prescription)

(defthm bvp-read-fn
  (implies (and (bvp reg0)
                (bvp reg1))
           (bvp (read-fn reg0 reg1 n)))
  :rule-classes (:rewrite :type-prescription))

(defthm read-fn-same-reg
  (equal (read-fn reg reg n) reg))

(in-theory (disable read-fn))

;; ======================================================================

;; FETCH3

(defun fetch3$induction (n clock count inputs
                           regs a-reg b-reg
                           i-reg flags pc-reg
                           last-regs-address last-i-reg last-flags
                           last-data)
  (if (zp n)
      (list clock count inputs
            regs a-reg b-reg
            i-reg flags pc-reg
            last-regs-address last-i-reg last-flags
            last-data)
    (fetch3$induction
     (1- n) (consp-or-nil clock) (1- count) (cdr inputs)
     (write-regs nil 0 regs 0)
     a-reg b-reg
     (pairlis$ (read-regs (strip-cars pc-reg) regs)
               nil)
     flags pc-reg
     (strip-cars pc-reg)
     (strip-cars i-reg)
     (strip-cars flags)
     (v-threefix last-data))))

(defthm fetch3$progress-help
  (implies
   (and (cv-hyps t
                 last-regs-address
                 last-i-reg
                 last-flags
                 (strip-cars pc-reg))
        (cv-hyps t
                 last-regs-address
                 (strip-cars i-reg)
                 (strip-cars flags)
                 (strip-cars pc-reg))
        (memory-okp 32 32 mem)
        (regfile-okp regs)
        (len-1-true-listp flags)
        (len-1-true-listp a-reg)
        (bvp (strip-cars a-reg))
        (equal (len a-reg) 32)
        (len-1-true-listp b-reg)
        (bvp (strip-cars b-reg))
        (equal (len b-reg) 32)
        (len-1-true-listp i-reg)
        (len-1-true-listp addr-out)
        (bvp (strip-cars addr-out))
        (equal (len addr-out) 32)
        (len-1-true-listp data-out)
        (bvp (strip-cars data-out))
        (equal (len data-out) 32)
        (len-1-true-listp pc-reg)
        (booleanp (car hold-))
        (equal last-address (strip-cars addr-out))
        (run-inputs-p inputs (add1 n))
        (natp n)
        (natp count)
        (<= n count))
   (equal
    (run-fm9001
     (list (list
            (list regs flags
                  a-reg b-reg i-reg
                  data-out addr-out
                  '(t) '(t) hold-
                  pc-reg
                  (pairlis$
                   (cv_fetch3 t
                              last-regs-address
                              last-i-reg
                              last-flags
                              (strip-cars pc-reg))
                   nil)))
           (list
            (list mem 1 clock count
                  nil t last-address last-data)))
     inputs
     (add1 n))
    (list (list
           (list (write-regs nil 0 regs 0)
                 flags a-reg b-reg
                 (pairlis$
                  (read-regs (strip-cars pc-reg) regs)
                  nil)
                 data-out addr-out
                 '(t)
                 (list (not (<= count n)))
                 (list (car hold-))
                 pc-reg
                 (pairlis$
                  (cv_fetch3 t
                             (strip-cars pc-reg)
                             (read-fn (strip-cars i-reg)
                                      (read-regs (strip-cars pc-reg) regs)
                                      n)
                             (strip-cars flags)
                             (strip-cars pc-reg))
                  nil)))
          (list
           (list mem 1 (consp-or-nil clock) (- count (1+ n))
                 (<= count n) t
                 (strip-cars addr-out)
                 (v-threefix last-data))))))
  :hints (("Goal"
           :in-theory (disable open-v-threefix
                               bvp-cvzbv
                               strip-cars
                               default-car
                               default-cdr)
           :induct (fetch3$induction
                    n clock count inputs
                    regs a-reg b-reg
                    i-reg flags pc-reg
                    last-regs-address last-i-reg last-flags
                    last-data))))

(defthm fetch3$progress
  (implies
   (and (cv-hyps t
                 last-regs-address
                 last-i-reg
                 last-flags
                 (strip-cars pc-reg))
        (cv-hyps t
                 last-regs-address
                 (strip-cars i-reg)
                 (strip-cars flags)
                 (strip-cars pc-reg))
        (memory-okp 32 32 mem)
        (regfile-okp regs)
        (len-1-true-listp flags)
        (len-1-true-listp a-reg)
        (bvp (strip-cars a-reg))
        (equal (len a-reg) 32)
        (len-1-true-listp b-reg)
        (bvp (strip-cars b-reg))
        (equal (len b-reg) 32)
        (len-1-true-listp i-reg)
        (len-1-true-listp addr-out)
        (bvp (strip-cars addr-out))
        (equal (len addr-out) 32)
        (len-1-true-listp data-out)
        (bvp (strip-cars data-out))
        (equal (len data-out) 32)
        (len-1-true-listp pc-reg)
        (booleanp (car hold-))
        (equal last-address (strip-cars addr-out))
        (run-inputs-p inputs count)
        (not (zp count)))
   (equal
    (run-fm9001
     (list (list
            (list regs flags
                  a-reg b-reg i-reg
                  data-out addr-out
                  '(t) '(t) hold-
                  pc-reg
                  (pairlis$
                   (cv_fetch3 t
                              last-regs-address
                              last-i-reg
                              last-flags
                              (strip-cars pc-reg))
                   nil)))
           (list
            (list mem 1 clock (1- count)
                  nil t last-address last-data)))
     inputs
     count)
    (list (list
           (list (write-regs nil 0 regs 0)
                 flags a-reg b-reg
                 (pairlis$
                  (read-regs (strip-cars pc-reg) regs)
                  nil)
                 data-out addr-out
                 '(t)
                 '(nil)
                 (list (car hold-))
                 pc-reg
                 (pairlis$
                  (cv_fetch3 t
                             (strip-cars pc-reg)
                             (read-fn (strip-cars i-reg)
                                      (read-regs (strip-cars pc-reg) regs)
                                      (1- count))
                             (strip-cars flags)
                             (strip-cars pc-reg))
                  nil)))
          (list
           (list mem 1 (consp-or-nil clock)
                 -1 t t
                 (strip-cars addr-out)
                 (v-threefix last-data))))))
  :hints (("Goal"
           :in-theory (e/d (plus)
                           (cv-hyps
                            regfile-okp
                            strip-cars
                            car-cdr-elim
                            open-run-inputs-p))
           :use (:instance fetch3$progress-help
                           (n (1- count))
                           (count (1- count))))))

;; ======================================================================

;; READA3

(defun reada3$induction (n clock count inputs
                           regs a-reg b-reg
                           i-reg flags pc-reg
                           last-regs-address last-i-reg last-flags
                           last-data)

  (if (zp n)
      (list clock count inputs
            regs a-reg b-reg
            i-reg flags pc-reg
            last-regs-address last-i-reg last-flags
            last-data)
    (reada3$induction
     (1- n) (consp-or-nil clock) (1- count) (cdr inputs)
     (write-regs nil 0 regs 0)
     (pairlis$ (read-regs (strip-cars pc-reg) regs) nil)
     b-reg i-reg flags pc-reg
     (strip-cars pc-reg)
     (strip-cars i-reg)
     (strip-cars flags)
     (v-threefix last-data))))

(defthm reada3$progress-help
  (implies
   (and (cv-hyps t
                 last-regs-address
                 last-i-reg
                 last-flags
                 (strip-cars pc-reg))
        (cv-hyps t
                 last-regs-address
                 (strip-cars i-reg)
                 (strip-cars flags)
                 (strip-cars pc-reg))
        (memory-okp 32 32 mem)
        (regfile-okp regs)
        (len-1-true-listp flags)
        (len-1-true-listp a-reg)
        (bvp (strip-cars a-reg))
        (equal (len a-reg) 32)
        (len-1-true-listp b-reg)
        (bvp (strip-cars b-reg))
        (equal (len b-reg) 32)
        (len-1-true-listp i-reg)
        (len-1-true-listp addr-out)
        (bvp (strip-cars addr-out))
        (equal (len addr-out) 32)
        (len-1-true-listp data-out)
        (bvp (strip-cars data-out))
        (equal (len data-out) 32)
        (len-1-true-listp pc-reg)
        (booleanp (car hold-))
        (equal last-address (strip-cars addr-out))
        (run-inputs-p inputs (add1 n))
        (natp n)
        (natp count)
        (<= n count))
   (equal
    (run-fm9001
     (list (list
            (list regs flags
                  a-reg b-reg i-reg
                  data-out addr-out
                  '(t) '(t) hold-
                  pc-reg
                  (pairlis$
                   (cv_reada3 t
                              last-regs-address
                              last-i-reg
                              last-flags
                              (strip-cars pc-reg))
                   nil)))
           (list
            (list mem 1 clock count
                  nil t last-address last-data)))
     inputs
     (add1 n))
    (list (list
           (list (write-regs nil 0 regs 0)
                 flags
                 (pairlis$
                  (read-regs (strip-cars pc-reg) regs)
                  nil)
                 b-reg i-reg data-out addr-out
                 '(t)
                 (list (not (<= count n)))
                 (list (car hold-))
                 pc-reg
                 (pairlis$
                  (cv_reada3 t
                             (strip-cars pc-reg)
                             (strip-cars i-reg)
                             (strip-cars flags)
                             (strip-cars pc-reg))
                  nil)))
          (list
           (list mem 1 (consp-or-nil clock) (- count (1+ n))
                 (<= count n) t
                 (strip-cars addr-out)
                 (v-threefix last-data))))))
  :hints (("Goal"
           :in-theory (disable open-v-threefix
                               bvp-cvzbv
                               strip-cars
                               default-car
                               default-cdr)
           :induct (reada3$induction
                    n clock count inputs
                    regs a-reg b-reg
                    i-reg flags pc-reg
                    last-regs-address last-i-reg last-flags
                    last-data))))

(defthm reada3$progress
  (implies
   (and (cv-hyps t
                 last-regs-address
                 last-i-reg
                 last-flags
                 (strip-cars pc-reg))
        (cv-hyps t
                 last-regs-address
                 (strip-cars i-reg)
                 (strip-cars flags)
                 (strip-cars pc-reg))
        (memory-okp 32 32 mem)
        (regfile-okp regs)
        (len-1-true-listp flags)
        (len-1-true-listp a-reg)
        (bvp (strip-cars a-reg))
        (equal (len a-reg) 32)
        (len-1-true-listp b-reg)
        (bvp (strip-cars b-reg))
        (equal (len b-reg) 32)
        (len-1-true-listp i-reg)
        (len-1-true-listp addr-out)
        (bvp (strip-cars addr-out))
        (equal (len addr-out) 32)
        (len-1-true-listp data-out)
        (bvp (strip-cars data-out))
        (equal (len data-out) 32)
        (len-1-true-listp pc-reg)
        (booleanp (car hold-))
        (equal last-address (strip-cars addr-out))
        (run-inputs-p inputs count)
        (not (zp count)))
   (equal
    (run-fm9001
     (list (list
            (list regs flags
                  a-reg b-reg i-reg
                  data-out addr-out
                  '(t) '(t) hold-
                  pc-reg
                  (pairlis$
                   (cv_reada3 t
                              last-regs-address
                              last-i-reg
                              last-flags
                              (strip-cars pc-reg))
                   nil)))
           (list
            (list mem 1 clock (1- count)
                  nil t last-address last-data)))
     inputs
     count)
    (list (list
           (list (write-regs nil 0 regs 0)
                 flags
                 (pairlis$
                  (read-regs (strip-cars pc-reg) regs)
                  nil)
                 b-reg i-reg data-out addr-out
                 '(t)
                 '(nil)
                 (list (car hold-))
                 pc-reg
                 (pairlis$
                  (cv_reada3 t
                             (strip-cars pc-reg)
                             (strip-cars i-reg)
                             (strip-cars flags)
                             (strip-cars pc-reg))
                  nil)))
          (list
           (list mem 1 (consp-or-nil clock)
                 -1 t t
                 (strip-cars addr-out)
                 (v-threefix last-data))))))
  :hints (("Goal"
           :in-theory (e/d (plus)
                           (cv-hyps
                            regfile-okp
                            strip-cars
                            car-cdr-elim
                            open-run-inputs-p))
           :use (:instance reada3$progress-help
                           (n (1- count))
                           (count (1- count))))))

;; ======================================================================

;; READB3

(defun readb3$induction (n clock count inputs
                           regs a-reg b-reg
                           i-reg flags pc-reg
                           last-regs-address last-i-reg last-flags
                           last-data)

  (if (zp n)
      (list clock count inputs
            regs a-reg b-reg
            i-reg flags pc-reg
            last-regs-address last-i-reg last-flags
            last-data)
    (readb3$induction
     (1- n) (consp-or-nil clock) (1- count) (cdr inputs)
     (write-regs nil 0 regs 0)
     a-reg
     (pairlis$ (read-regs (strip-cars pc-reg) regs) nil)
     i-reg flags pc-reg
     (strip-cars pc-reg)
     (strip-cars i-reg)
     (strip-cars flags)
     (v-threefix last-data))))

(defthm readb3$progress-help
  (implies
   (and (cv-hyps t
                 last-regs-address
                 last-i-reg
                 last-flags
                 (strip-cars pc-reg))
        (cv-hyps t
                 last-regs-address
                 (strip-cars i-reg)
                 (strip-cars flags)
                 (strip-cars pc-reg))
        (memory-okp 32 32 mem)
        (regfile-okp regs)
        (len-1-true-listp flags)
        (len-1-true-listp a-reg)
        (bvp (strip-cars a-reg))
        (equal (len a-reg) 32)
        (len-1-true-listp b-reg)
        (bvp (strip-cars b-reg))
        (equal (len b-reg) 32)
        (len-1-true-listp i-reg)
        (len-1-true-listp addr-out)
        (bvp (strip-cars addr-out))
        (equal (len addr-out) 32)
        (len-1-true-listp data-out)
        (bvp (strip-cars data-out))
        (equal (len data-out) 32)
        (len-1-true-listp pc-reg)
        (booleanp (car hold-))
        (equal last-address (strip-cars addr-out))
        (run-inputs-p inputs (add1 n))
        (natp n)
        (natp count)
        (<= n count))
   (equal
    (run-fm9001
     (list (list
            (list regs flags
                  a-reg b-reg i-reg
                  data-out addr-out
                  '(t) '(t) hold-
                  pc-reg
                  (pairlis$
                   (cv_readb3 t
                              last-regs-address
                              last-i-reg
                              last-flags
                              (strip-cars pc-reg))
                   nil)))
           (list
            (list mem 1 clock count
                  nil t last-address last-data)))
     inputs
     (add1 n))
    (list (list
           (list (write-regs nil 0 regs 0)
                 flags a-reg
                 (pairlis$
                  (read-regs (strip-cars pc-reg) regs)
                  nil)
                 i-reg data-out addr-out
                 '(t)
                 (list (not (<= count n)))
                 (list (car hold-))
                 pc-reg
                 (pairlis$
                  (cv_readb3 t
                             (strip-cars pc-reg)
                             (strip-cars i-reg)
                             (strip-cars flags)
                             (strip-cars pc-reg))
                  nil)))
          (list
           (list mem 1 (consp-or-nil clock) (- count (1+ n))
                 (<= count n) t
                 (strip-cars addr-out)
                 (v-threefix last-data))))))
  :hints (("Goal"
           :in-theory (disable open-v-threefix
                               bvp-cvzbv
                               strip-cars
                               default-car
                               default-cdr)
           :induct (readb3$induction
                    n clock count inputs
                    regs a-reg b-reg
                    i-reg flags pc-reg
                    last-regs-address last-i-reg last-flags
                    last-data))))

(defthm readb3$progress
  (implies
   (and (cv-hyps t
                 last-regs-address
                 last-i-reg
                 last-flags
                 (strip-cars pc-reg))
        (cv-hyps t
                 last-regs-address
                 (strip-cars i-reg)
                 (strip-cars flags)
                 (strip-cars pc-reg))
        (memory-okp 32 32 mem)
        (regfile-okp regs)
        (len-1-true-listp flags)
        (len-1-true-listp a-reg)
        (bvp (strip-cars a-reg))
        (equal (len a-reg) 32)
        (len-1-true-listp b-reg)
        (bvp (strip-cars b-reg))
        (equal (len b-reg) 32)
        (len-1-true-listp i-reg)
        (len-1-true-listp addr-out)
        (bvp (strip-cars addr-out))
        (equal (len addr-out) 32)
        (len-1-true-listp data-out)
        (bvp (strip-cars data-out))
        (equal (len data-out) 32)
        (len-1-true-listp pc-reg)
        (booleanp (car hold-))
        (equal last-address (strip-cars addr-out))
        (run-inputs-p inputs count)
        (not (zp count)))
   (equal
    (run-fm9001
     (list (list
            (list regs flags
                  a-reg b-reg i-reg
                  data-out addr-out
                  '(t) '(t) hold-
                  pc-reg
                  (pairlis$
                   (cv_readb3 t
                              last-regs-address
                              last-i-reg
                              last-flags
                              (strip-cars pc-reg))
                   nil)))
           (list
            (list mem 1 clock (1- count)
                  nil t last-address last-data)))
     inputs
     count)
    (list (list
           (list (write-regs nil 0 regs 0)
                 flags a-reg
                 (pairlis$
                  (read-regs (strip-cars pc-reg) regs)
                  nil)
                 i-reg data-out addr-out
                 '(t)
                 '(nil)
                 (list (car hold-))
                 pc-reg
                 (pairlis$
                  (cv_readb3 t
                             (strip-cars pc-reg)
                             (strip-cars i-reg)
                             (strip-cars flags)
                             (strip-cars pc-reg))
                  nil)))
          (list
           (list mem 1 (consp-or-nil clock)
                 -1 t t
                 (strip-cars addr-out)
                 (v-threefix last-data))))))
  :hints (("Goal"
           :in-theory (e/d (plus)
                           (cv-hyps
                            regfile-okp
                            strip-cars
                            car-cdr-elim
                            open-run-inputs-p))
           :use (:instance readb3$progress-help
                           (n (1- count))
                           (count (1- count))))))

;; ======================================================================

;; WRITE3

(defun write3$induction (n clock count inputs
                           regs a-reg b-reg
                           i-reg flags pc-reg
                           last-regs-address last-i-reg last-flags
                           last-data)

  (if (zp n)
      (list clock count inputs
            regs a-reg b-reg
            i-reg flags pc-reg
            last-regs-address last-i-reg last-flags
            last-data)
    (write3$induction
     (1- n) (consp-or-nil clock) (1- count) (cdr inputs)
     (write-regs nil 0 regs 0)
     a-reg b-reg i-reg flags pc-reg
     (strip-cars pc-reg)
     (strip-cars i-reg)
     (strip-cars flags)
     (v-threefix last-data))))

(defthm write3$progress-help
  (implies
   (and (cv-hyps t
                 last-regs-address
                 last-i-reg
                 last-flags
                 (strip-cars pc-reg))
        (cv-hyps t
                 last-regs-address
                 (strip-cars i-reg)
                 (strip-cars flags)
                 (strip-cars pc-reg))
        (memory-okp 32 32 mem)
        (regfile-okp regs)
        (len-1-true-listp flags)
        (len-1-true-listp a-reg)
        (bvp (strip-cars a-reg))
        (equal (len a-reg) 32)
        (len-1-true-listp b-reg)
        (bvp (strip-cars b-reg))
        (equal (len b-reg) 32)
        (len-1-true-listp i-reg)
        (len-1-true-listp addr-out)
        (bvp (strip-cars addr-out))
        (equal (len addr-out) 32)
        (len-1-true-listp data-out)
        (bvp (strip-cars data-out))
        (equal (len data-out) 32)
        (len-1-true-listp pc-reg)
        (booleanp (car hold-))
        (equal last-address (strip-cars addr-out))
        (equal last-data (strip-cars data-out))
        (run-inputs-p inputs (add1 n))
        (natp n)
        (natp count)
        (<= n count))
   (equal
    (run-fm9001
     (list (list
            (list regs flags
                  a-reg b-reg i-reg
                  data-out addr-out
                  '(t) '(t) hold-
                  pc-reg
                  (pairlis$
                   (cv_write3 nil
                              last-regs-address
                              last-i-reg
                              last-flags
                              (strip-cars pc-reg))
                   nil)))
           (list
            (list mem 2 clock count
                  nil nil last-address last-data)))
     inputs
     (add1 n))
   (list (list
          (list (write-regs nil 0 regs 0)
                flags a-reg b-reg i-reg
                data-out addr-out
                '(t)
                (list (not (<= count n)))
                (list (car hold-))
                pc-reg
                (pairlis$
                 (cv_write3 nil
                            (strip-cars pc-reg)
                            (strip-cars i-reg)
                            (strip-cars flags)
                            (strip-cars pc-reg))
                 nil)))
         (list
          (list mem 2 (consp-or-nil clock) (- count (1+ n))
                (<= count n) nil
                (strip-cars addr-out)
                (strip-cars data-out))))))
  :hints (("Goal"
           :in-theory (disable open-v-threefix
                               bvp-cvzbv
                               strip-cars
                               default-car
                               default-cdr)
           :induct (write3$induction
                    n clock count inputs
                    regs a-reg b-reg
                    i-reg flags pc-reg
                    last-regs-address last-i-reg last-flags
                    last-data))))

(defthm write3$progress
  (implies
   (and (cv-hyps t
                 last-regs-address
                 last-i-reg
                 last-flags
                 (strip-cars pc-reg))
        (cv-hyps t
                 last-regs-address
                 (strip-cars i-reg)
                 (strip-cars flags)
                 (strip-cars pc-reg))
        (memory-okp 32 32 mem)
        (regfile-okp regs)
        (len-1-true-listp flags)
        (len-1-true-listp a-reg)
        (bvp (strip-cars a-reg))
        (equal (len a-reg) 32)
        (len-1-true-listp b-reg)
        (bvp (strip-cars b-reg))
        (equal (len b-reg) 32)
        (len-1-true-listp i-reg)
        (len-1-true-listp addr-out)
        (bvp (strip-cars addr-out))
        (equal (len addr-out) 32)
        (len-1-true-listp data-out)
        (bvp (strip-cars data-out))
        (equal (len data-out) 32)
        (len-1-true-listp pc-reg)
        (booleanp (car hold-))
        (equal last-address (strip-cars addr-out))
        (equal last-data (strip-cars data-out))
        (run-inputs-p inputs count)
        (not (zp count)))
   (equal
    (run-fm9001
     (list (list
            (list regs flags
                  a-reg b-reg i-reg
                  data-out addr-out
                  '(t) '(t) hold-
                  pc-reg
                  (pairlis$
                   (cv_write3 nil
                              last-regs-address
                              last-i-reg
                              last-flags
                              (strip-cars pc-reg))
                   nil)))
           (list
            (list mem 2 clock (1- count)
                  nil nil last-address last-data)))
     inputs
     count)
    (list (list
           (list (write-regs nil 0 regs 0)
                 flags a-reg b-reg i-reg
                 data-out addr-out
                 '(t)
                 '(nil)
                 (list (car hold-))
                 pc-reg
                 (pairlis$
                  (cv_write3 nil
                             (strip-cars pc-reg)
                             (strip-cars i-reg)
                             (strip-cars flags)
                             (strip-cars pc-reg))
                  nil)))
          (list
           (list mem 2 (consp-or-nil clock)
                 -1 t nil
                 (strip-cars addr-out)
                 (strip-cars data-out))))))
   :hints (("Goal"
           :in-theory (e/d (plus)
                           (cv-hyps
                            regfile-okp
                            strip-cars
                            car-cdr-elim
                            open-run-inputs-p))
           :use (:instance write3$progress-help
                           (n (1- count))
                           (count (1- count))))))

;; ======================================================================

;; Chunk Simulations

;; SIM-FM9001 is a macro that creates lemmas that describe the operation of the
;; machine for multiple clock cycles.  We create a multi-state simulation for
;; each non-branching segment of the state diagrams.  For this purpose, we
;; consider the states that wait for memory as "non-branching".  Notice that
;; some of the "multi-state" lemmas only include a single state.

;; SIM-FM9001 is defined in "expand-fm9001-macros.lisp"

;; ZP-NOT-ZP-CASES is a bogus recursive function used to force the
;; prover to do these multi-step simulations by cases.

;; (defun zp-not-zp-cases (n)
;;   (declare (xargs :measure (acl2-count n)))
;;   (if (zp n)
;;       t
;;     (if (not (zp n))
;;         t
;;       (zp-not-zp-cases n))))

(make-event
 (sim-fm9001 state 'fetch0 'fetch0 :suffix 0))

(make-event
 (sim-fm9001 state 'fetch0 'fetch0 :suffix 1 :mem-state 1))

(make-event
 (sim-fm9001 state 'fetch0 'fetch0 :suffix 2 :mem-state 2
             :hyps '(zp mem-count)
             :addr-stable t :data-stable t :last-rw- nil))

(make-event
 (sim-fm9001 state 'fetch1 'decode
             :hyps '(and (equal (car hold-) t) (booleanp last-rw-))
             :last-rw- 'last-rw-
             :dtack-wait *w_fetch1->decode* :disable '(fetch3$step1)))

(make-event
 (sim-fm9001 state 'rega 'rega))

(make-event
 (sim-fm9001
  state 'regb 'update
  :split-term '(and* (or* (pre-dec-p (mode-b (strip-cars i-reg)))
                          (post-inc-p (mode-b (strip-cars i-reg))))
                     (unary-op-code-p (op-code (strip-cars i-reg))))))

(make-event
 (sim-fm9001
  state 'update 'update :mem-state 'mem-state
  :hyps '(or (equal mem-state 0) (equal mem-state 1))
  :split-term '(and* (or* (pre-dec-p (mode-b (strip-cars i-reg)))
                          (post-inc-p (mode-b (strip-cars i-reg))))
                     (unary-op-code-p (op-code (strip-cars i-reg))))))

(make-event
 (sim-fm9001 state 'reada0 'reada3 :dtack-wait *w_reada0->reada3*
             :disable '(reada3$step1)))

(make-event
 (sim-fm9001 state 'readb0 'readb3
             :mem-state 'mem-state
             :hyps '(or (equal mem-state 0) (equal mem-state 1))
             :dtack-wait *w_readb0->readb3*
             :disable '(readb3$step1)))

(make-event
 (sim-fm9001 state 'write0 'write3
             :mem-state 'mem-state
             :hyps '(or (equal mem-state 0) (equal mem-state 1))
             :dtack-wait *w_write0->write3*
             :disable '(write3$step1)))

(make-event
 (sim-fm9001 state 'sefa0 'sefa1))

(make-event
 (sim-fm9001 state 'sefb0 'sefb1))

(make-event
 (sim-fm9001 state 'sefb1 'sefb1))

;; ======================================================================

;; Execution time functions.

;; For each of the "chunks" above we define a function that states exactly how
;; many clock cycles are necessary to complete the instruction execution cycle
;; from the given starting state.  In these functions, CLOCK is the memory
;; delay oracle, and I-REG and FLAGS are the corresponding processor registers.
;; The functions below are defined in terms of constants appearing in
;; "constant.lisp".  The function T_initial-state->final-state is an expression
;; for the amount of time necessary to execute the indicated section of of the
;; state diagram.  The function CT_initial-state->final-state is an expression
;; for the memory delay oracle at the end of the sequence.  The function
;; TIMING-IF-TREE creates an "IF" tree of calls to timing functions based on
;; the branching decisions that appear in the state diagrams.

(defun timify-tree (tree)
  (cond
   ((symbolp tree)
    `(,(unstring "T_" (symbol-name tree)) CLOCK I-REG FLAGS))
   ((and (consp tree) (equal (car tree) 'IF))
    (if (equal (cadr tree) 'DTACK-)
        (timify-tree (cadddr tree))
      (if (equal (cadr tree) 'HOLD-)
          (timify-tree (caddr tree))
        `(IF ,(cadr tree)
             ,(timify-tree (caddr tree))
             ,(timify-tree (cadddr tree))))))
   (t (er hard 'timify-tree
          "Error when calling (timify-tree ~x0)."
          tree))))

(defun control-let-alt (body)
  (declare (xargs :guard t))
  `(B* ((A-IMMEDIATE-P (A-IMMEDIATE-P I-REG))
        (MODE-A        (MODE-A        I-REG))
        (?RN-A          (RN-A          I-REG))
        (MODE-B        (MODE-B        I-REG))
        (?RN-B          (RN-B          I-REG))
        (SET-FLAGS     (SET-FLAGS     I-REG))
        (STORE-CC      (STORE-CC      I-REG))
        (OP-CODE       (OP-CODE       I-REG)))
     (B* ((A-IMMEDIATE-P-     (NOT* A-IMMEDIATE-P))
          (STORE              (STORE-RESULTP STORE-CC FLAGS))
          (?SET-SOME-FLAGS    (SET-SOME-FLAGS SET-FLAGS))
          (DIRECT-A           (OR* A-IMMEDIATE-P (REG-DIRECT-P MODE-A)))
          (DIRECT-B           (REG-DIRECT-P MODE-B))
          (UNARY              (UNARY-OP-CODE-P OP-CODE))
          (PRE-DEC-A          (PRE-DEC-P MODE-A))
          (POST-INC-A         (POST-INC-P MODE-A))
          (PRE-DEC-B          (PRE-DEC-P MODE-B))
          (POST-INC-B         (POST-INC-P MODE-B))
          (?C                 (C-FLAG FLAGS)))
       (B* ((?STORE-        (NOT* STORE))
            (?DIRECT-A-     (NOT* DIRECT-A))
            (?DIRECT-B-     (NOT* DIRECT-B))
            (?UNARY-        (NOT* UNARY))
            (?SIDE-EFFECT-A (AND* A-IMMEDIATE-P-
                                  (OR* PRE-DEC-A POST-INC-A)))
            (?SIDE-EFFECT-B (OR* PRE-DEC-B POST-INC-B)))
         ,body))))

(defun timing-if-tree (st)
  (control-let-alt (timify-tree (cadr (assoc st *state-table*)))))

(defun t_fetch0 (clock i-reg flags)
  (declare (ignorable clock i-reg flags))
   #.*t_fetch0->fetch0*)

(defmacro t_sefb1-macro ()
  `(defun t_sefb1 (clock i-reg flags)
     (let ((time #.*t_sefb1->sefb1*))
       (let ((clock #.*ct_sefb1->sefb1*))
         (plus time ,(timing-if-tree 'sefb1))))))

(t_sefb1-macro)

(defmacro t_sefb0-macro ()
  `(defun t_sefb0 (clock i-reg flags)
     (declare (ignorable clock))
     (let ((time #.*t_sefb0->sefb1*))
       (let ((clock #.*ct_sefb0->sefb1*))
         (plus time ,(timing-if-tree 'sefb1))))))

(t_sefb0-macro)

(defmacro t_sefa0-macro ()
  `(defun t_sefa0 (clock i-reg flags)
     (let ((time #.*t_sefa0->sefa1*))
       (let ((clock #.*ct_sefa0->sefa1*))
         (plus time ,(timing-if-tree 'sefa1))))))

(t_sefa0-macro)

(defmacro t_write0-macro ()
  `(defun t_write0 (clock i-reg flags)
     (let ((time #.*t_write0->write3*))
       (let ((clock #.*ct_write0->write3*))
         (plus time ,(timing-if-tree 'write3))))))

(t_write0-macro)

(defmacro t_update-macro ()
  `(defun t_update (clock i-reg flags)
     (let ((time #.*t_update->update*))
       (let ((clock #.*ct_update->update*))
         (plus time ,(timing-if-tree 'update))))))

(t_update-macro)

(defmacro t_readb0-macro ()
  `(defun t_readb0 (clock i-reg flags)
     (let ((time #.*t_readb0->readb3*))
       (let ((clock #.*ct_readb0->readb3*))
         (plus time ,(timing-if-tree 'readb3))))))

(t_readb0-macro)

(defmacro t_reada0-macro ()
  `(defun t_reada0 (clock i-reg flags)
     (let ((time #.*t_reada0->reada3*))
       (let ((clock #.*ct_reada0->reada3*))
         (plus time ,(timing-if-tree 'reada3))))))

(t_reada0-macro)

(defmacro t_regb-macro ()
  `(defun t_regb (clock i-reg flags)
     (let ((time #.*t_regb->update*))
       (let ((clock #.*ct_regb->update*))
         (plus time ,(timing-if-tree 'update))))))

(t_regb-macro)

(defmacro t_rega-macro ()
  `(defun t_rega (clock i-reg flags)
     (let ((time #.*t_rega->rega*))
       (let ((clock #.*ct_rega->rega*))
         (plus time ,(timing-if-tree 'rega))))))

(t_rega-macro)

(defmacro t_fetch1-macro ()
  `(defun t_fetch1 (clock i-reg flags)
     (let ((time #.*t_fetch1->decode*))
       (let ((clock #.*ct_fetch1->decode*))
         (plus time ,(timing-if-tree 'decode))))))

(t_fetch1-macro)
