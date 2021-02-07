;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

(in-package "FM9001")

(include-book "macros")

(include-book "misc/bash" :dir :system)

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

;; STEP-FM9001 is used in "expand-fm9001.lisp".

(define step-fm9001 (state
                     st
                     &key
                     (suffix '"")
                     (addr-stable 'NIL)
                     (data-stable 'NIL)
                     (dtack- ''DTACK-)
                     (mem-state '0)
                     (mem-count ''MEM-COUNT)
                     (mem-dtack ''MEM-DTACK)
                     (last-rw- 'T)
                     (rw--for-hint 'T)
                     (regs-address ''LAST-PC-REG)
                     (hyps 'T)
                     (enable 'NIL)
                     (disable 'NIL)
                     (split-term 'NIL))
  :mode :program
  (b* ((suffix (if (natp suffix)
                   (str::natstr suffix)
                 suffix))
       (lemma-name (intern$ (concatenate 'string
                                         (symbol-name st)
                                         "$STEP"
                                         suffix)
                            "FM9001"))
       (next-cntl-state (unstring "NEXT-CNTL-STATE$" (symbol-name st)))
       (cv$destructure (add-prefix-and-suffix-to-name "CV_"
                                                      "$DESTRUCTURE"
                                                      st))
       (term
        `(RUN-FM9001
          (LIST (LIST
                 (LIST REGS
                       FLAGS
                       A-REG B-REG I-REG
                       DATA-OUT ADDR-OUT
                       RESET- ,dtack- HOLD-
                       PC-REG
                       (PAIRLIS$ (,(add-prefix-to-name "CV_" st)
                                  ,last-rw- LAST-REGS-ADDRESS LAST-I-REG
                                  LAST-FLAGS LAST-PC-REG)
                                 NIL)))
                (LIST
                 (LIST MEM ,mem-state CLOCK ,mem-count ,mem-dtack
                       ,last-rw- LAST-ADDRESS LAST-DATA)))
          INPUTS
          N))
       (hyps
        `(AND (CV-HYPS ,last-rw- LAST-REGS-ADDRESS LAST-I-REG LAST-FLAGS
                       LAST-PC-REG)
              (CV-HYPS T
                       (STRIP-CARS PC-REG)
                       (STRIP-CARS I-REG)
                       (STRIP-CARS FLAGS)
                       (STRIP-CARS PC-REG))
              (MEMORY-OKP 32 32 MEM)
              (REGFILE-OKP REGS)
              (LEN-1-TRUE-LISTP FLAGS)
              (LEN-1-TRUE-LISTP A-REG)
              (BVP (STRIP-CARS A-REG))
              (EQUAL (LEN A-REG) 32)
              (LEN-1-TRUE-LISTP B-REG)
              (BVP (STRIP-CARS B-REG))
              (EQUAL (LEN B-REG) 32)
              (LEN-1-TRUE-LISTP I-REG)
              (LEN-1-TRUE-LISTP ADDR-OUT)
              (BVP (STRIP-CARS ADDR-OUT))
              (EQUAL (LEN ADDR-OUT) 32)
              (LEN-1-TRUE-LISTP DATA-OUT)
              (BVP (STRIP-CARS DATA-OUT))
              (EQUAL (LEN DATA-OUT) 32)
              (LEN-1-TRUE-LISTP PC-REG)
              (NOT (ZP N))
              (RUN-INPUTS-P INPUTS 1)
              (BOOLEANP (CAR ,dtack-))
              (BOOLEANP (CAR HOLD-))
              (EQUAL (CAR RESET-) T)
              ,(if addr-stable
                   '(EQUAL LAST-ADDRESS (STRIP-CARS ADDR-OUT))
                 T)
              ,(if data-stable
                   '(EQUAL LAST-DATA (STRIP-CARS DATA-OUT))
                 T)
              ,hyps))
       (hints
        `(("Goal"
           :use (:instance ,next-cntl-state
                           (reset- T)
                           (dtack- (car ,dtack-))
                           (hold- (car hold-))
                           (rw- ,rw--for-hint)
                           (i-reg (strip-cars i-reg))
                           (flags (strip-cars flags))
                           (pc-reg (strip-cars pc-reg))
                           (regs-address ,regs-address))
           :in-theory (e/d (run-fm9001-step-case
                             ,cv$destructure
                             next-memory-state
                             memory-value
                             f-buf-delete-lemmas
                             fm9001-hardware-state-accessors
                             ,@enable)
                            (open-v-threefix
                             (make-list-ac)
                             make-list-ac-removal
                             (make-tree)
                             strip-cars
                             (alu-dec-op)
                             (alu-inc-op)
                             ,@disable)))))
       ((mv & simplified-term1 state)
        (if split-term
            (bash-fn `(IMPLIES (AND ,hyps ,split-term)
                               (EQUAL ,term ?))
                     hints NIL 'bash state)
          (bash-fn `(IMPLIES ,hyps
                             (EQUAL ,term ?))
                   hints NIL 'bash state)))
       ((mv & simplified-term2 state)
        (if split-term
            (bash-fn `(IMPLIES (AND ,hyps (NOT ,split-term))
                               (EQUAL ,term ?))
                     hints NIL 'bash state)
          (mv NIL NIL state)))
       )

    (mv NIL
        `(defthm ,lemma-name
           (IMPLIES ,hyps
                    (EQUAL ,term
                           ,(if split-term
                                `(IF ,split-term
                                     ,(cadr (caddar simplified-term1))
                                     ,(cadr (caddar simplified-term2)))
                              (cadr (caddar simplified-term1)))))
           :hints ,hints)
        state)))

;; ======================================================================

;; Chunk Simulations

;; SIM-FM9001 is a macro that creates lemmas that describe the operation of the
;; machine for multiple clock cycles.  We create a multi-state simulation for
;; each non-branching segment of the state diagrams.  For this purpose, we
;; consider the states that wait for memory as "non-branching".  Notice that
;; some of the "multi-state" lemmas only include a single state.

;; SIM-FM9001 is used in "expand-fm9001.lisp".

(define sim-fm9001 (state
                    start-st end-st
                    &key
                    (suffix '"")
                    (addr-stable 'NIL)
                    (data-stable 'NIL)
                    (dtack- ''DTACK-)
                    (mem-state '0)
                    (mem-count ''MEM-COUNT)
                    (mem-dtack ''MEM-DTACK)
                    (last-rw- 'T)
                    (hyps 'T)
                    (enable 'NIL)
                    (disable 'NIL)
                    (split-term 'NIL)
                    (dtack-wait 'NIL))
  :mode :program
  (b* ((time-const (intern$ (concatenate 'string
                                         "*T_"
                                         (symbol-name start-st)
                                         "->"
                                         (symbol-name end-st)
                                         "*")
                            "FM9001"))
       (time-const-prop (getpropc time-const 'acl2::const nil (w state)))
       ;; ((when (not time-const-prop))
       ;;  (er hard 'sim-fm9001
       ;;      "~x0 is undefined!"
       ;;      time-const))
       (time-const-guts (assert$ (quotep time-const-prop)
                                 (unquote time-const-prop)))
       (suffix (if (natp suffix)
                   (str::natstr suffix)
                 suffix))
       (lemma-name (intern$ (concatenate 'string
                                         (symbol-name start-st)
                                         "->"
                                         (symbol-name end-st)
                                         "$SIM"
                                         suffix)
                            "FM9001"))
       (term
        `(RUN-FM9001
          (LIST (LIST
                 (LIST REGS
                       FLAGS
                       A-REG B-REG I-REG
                       DATA-OUT ADDR-OUT
                       RESET- ,dtack- HOLD-
                       PC-REG
                       (PAIRLIS$ (,(add-prefix-to-name "CV_" start-st)
                                  ,last-rw- LAST-REGS-ADDRESS LAST-I-REG
                                  LAST-FLAGS (STRIP-CARS PC-REG))
                                 NIL)))
                (LIST
                 (LIST MEM ,mem-state CLOCK ,mem-count ,mem-dtack
                       ,last-rw- LAST-ADDRESS LAST-DATA)))
          INPUTS
          N))
       (hyps
        `(AND (CV-HYPS ,last-rw- LAST-REGS-ADDRESS LAST-I-REG LAST-FLAGS
                       (STRIP-CARS PC-REG))
              (CV-HYPS T
                       (STRIP-CARS PC-REG)
                       (STRIP-CARS I-REG)
                       (STRIP-CARS FLAGS)
                       (STRIP-CARS PC-REG))
              (MEMORY-OKP 32 32 MEM)
              (REGFILE-OKP REGS)
              (LEN-1-TRUE-LISTP FLAGS)
              (LEN-1-TRUE-LISTP A-REG)
              (BVP (STRIP-CARS A-REG))
              (EQUAL (LEN A-REG) 32)
              (LEN-1-TRUE-LISTP B-REG)
              (BVP (STRIP-CARS B-REG))
              (EQUAL (LEN B-REG) 32)
              (LEN-1-TRUE-LISTP I-REG)
              (LEN-1-TRUE-LISTP ADDR-OUT)
              (BVP (STRIP-CARS ADDR-OUT))
              (EQUAL (LEN ADDR-OUT) 32)
              (LEN-1-TRUE-LISTP DATA-OUT)
              (BVP (STRIP-CARS DATA-OUT))
              (EQUAL (LEN DATA-OUT) 32)
              (LEN-1-TRUE-LISTP PC-REG)
              (BOOLEANP (CAR ,dtack-))
              (BOOLEANP (CAR HOLD-))
              (EQUAL N ,time-const-guts)
              (RUN-INPUTS-P INPUTS N)
              (EQUAL (CAR RESET-) T)
              ,(if addr-stable
                   '(EQUAL LAST-ADDRESS (STRIP-CARS ADDR-OUT))
                 T)
              ,(if data-stable
                   '(EQUAL LAST-DATA (STRIP-CARS DATA-OUT))
                 T)
              ,hyps))
       (hints
        (if dtack-wait
            `(("GOAL"
               :CASES ((ZP ,dtack-wait) (NOT (ZP ,dtack-wait)))
               :IN-THEORY (E/D (,@enable)
                                (OPEN-V-THREEFIX
                                 STRIP-CARS
                                 PAIRLIS$
                                 COMMUTATIVITY-OF-+
                                 V-THREEFIX-BVP
                                 DEFAULT-CAR
                                 DEFAULT-CDR
                                 BVP-CVZBV
                                 BOOLEANP-SET-SOME-FLAGS
                                 BVP-SET-FLAGS
                                 IF*
                                 (ALU-DEC-OP)
                                 (ALU-INC-OP)
                                 ,@disable))))
          `(("GOAL"
             :IN-THEORY (E/D (,@enable)
                              (OPEN-V-THREEFIX
                               STRIP-CARS
                               PAIRLIS$
                               COMMUTATIVITY-OF-+
                               V-THREEFIX-BVP
                               DEFAULT-CAR
                               DEFAULT-CDR
                               BVP-CVZBV
                               BOOLEANP-SET-SOME-FLAGS
                               BVP-SET-FLAGS
                               IF*
                               (ALU-DEC-OP)
                               (ALU-INC-OP)
                               ,@disable))))))
       ((mv & simplified-term1 state)
        (if dtack-wait
            (bash-fn `(IMPLIES (AND (EQUAL DTACK-WAIT ,dtack-wait)
                                    (ZP DTACK-WAIT)
                                    ,hyps)
                               (EQUAL ,term ?))
                     hints NIL 'bash state)
          (if split-term
              (bash-fn `(IMPLIES (AND ,hyps ,split-term)
                                 (EQUAL ,term ?))
                       hints NIL 'bash state)
            (bash-fn `(IMPLIES ,hyps
                               (EQUAL ,term ?))
                     hints NIL 'bash state))))
       ((mv & simplified-term2 state)
        (if split-term
            (bash-fn `(IMPLIES (AND ,hyps (NOT ,split-term))
                               (EQUAL ,term ?))
                     hints NIL 'bash state)
          (mv NIL NIL state)))
       )

    (mv NIL
        `(defthm ,lemma-name
           (IMPLIES ,hyps
                    (EQUAL ,term
                           ,(if split-term
                                `(IF ,split-term
                                     ,(cadr (caddar simplified-term1))
                                     ,(cadr (caddar simplified-term2)))
                              (cadr (caddar simplified-term1)))))
           :hints ,hints)
        state)))




