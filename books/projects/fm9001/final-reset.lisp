;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

;; This file contains the verification of the FM9001 reset sequence.  There are
;; several reset proofs in this file, all stated in slightly different ways.
;; There are also a number of refinements of the main correctness theorem of
;; the FM9001 microprocessor.

(in-package "FM9001")

(include-book "approx")
(include-book "proofs")

(local (include-book "arithmetic/top" :dir :system))

;; ======================================================================

;; The definition of a properly structured but completely unknown machine
;; state.

(defun unknown-regfile ()
  (declare (xargs :guard t))
  (list
   ;; regs
   (list
    (cons (cons (cons
                 (cons (ram (make-list 32 :initial-element *x*))
                       (ram (make-list 32 :initial-element *x*)))
                 (cons (ram (make-list 32 :initial-element *x*))
                       (ram (make-list 32 :initial-element *x*))))
                (cons
                 (cons (ram (make-list 32 :initial-element *x*))
                       (ram (make-list 32 :initial-element *x*)))
                 (cons (ram (make-list 32 :initial-element *x*))
                       (ram (make-list 32 :initial-element *x*)))))
          (cons (cons
                 (cons (ram (make-list 32 :initial-element *x*))
                       (ram (make-list 32 :initial-element *x*)))
                 (cons (ram (make-list 32 :initial-element *x*))
                       (ram (make-list 32 :initial-element *x*))))
                (cons
                 (cons (ram (make-list 32 :initial-element *x*))
                       (ram (make-list 32 :initial-element *x*)))
                 (cons (ram (make-list 32 :initial-element *x*))
                       (ram (make-list 32 :initial-element *x*)))))))
   (list *x*)                                         ; we
   (pairlis$ (make-list 32 :initial-element *x*) nil) ; data
   (pairlis$ (make-list 4 :initial-element *x*) nil)  ; address
   ))

(defun unknown-machine-state ()
  (declare (xargs :guard t))
  (list
   (unknown-regfile)                                  ; regs
   (pairlis$ (make-list 4 :initial-element *x*) nil)  ; flags
   (pairlis$ (make-list 32 :initial-element *x*) nil) ; a-reg
   (pairlis$ (make-list 32 :initial-element *x*) nil) ; b-reg
   (pairlis$ (make-list 32 :initial-element *x*) nil) ; i-reg
   (pairlis$ (make-list 32 :initial-element *x*) nil) ; data-out
   (pairlis$ (make-list 32 :initial-element *x*) nil) ; addr-out
   (list *x*)                                         ; reset
   (list *x*)                                         ; dtack
   (list *x*)                                         ; hold
   (pairlis$ (make-list 4 :initial-element *x*) nil)  ; pc-reg
   (pairlis$ (make-list 40 :initial-element *x*) nil) ; cntl-state
   ))

(defun unknown-memory-state ()
  (declare (xargs :guard t))
  (list
   (list 'stub (make-list 32))           ; mem
   0                                     ; cntl
   nil                                   ; clock
   0                                     ; count
   *x*                                   ; dtack-asserted
   *x*                                   ; last-rw-
   (make-list 32 :initial-element *x*)   ; last-address
   (make-list 32 :initial-element *x*))) ; last-data

(defun unknown-state ()
  (declare (xargs :guard t))
  (list (list (unknown-machine-state))
        (list (unknown-memory-state))))

(defthm chip-system-invariant-unknown-state
  (chip-system-invariant (unknown-state)))

(defthm fm9001-state-structure-unknown-state
  (fm9001-state-structure (unknown-state)))

;; ======================================================================

;; Resetting the CHIP-SYSTEM

;; Putting together an input stream that initializes CHIP-SYSTEM.

(defun reset-vector ()
  (declare (xargs :guard t))
  (list* *x*                                ; clk
         *x*                                ; ti
         nil                                ; te
         nil                                ; reset-
         t                                  ; hold-
         t                                  ; disable-regfile-
         t                                  ; test-regfile-
         (make-list 4 :initial-element t))) ; pc-reg

(defun run-vector ()
  (declare (xargs :guard t))
  (list* *x*                                ; clk
         *x*                                ; ti
         nil                                ; te
         t                                  ; reset-
         t                                  ; hold-
         t                                  ; disable-regfile-
         t                                  ; test-regfile-
         (make-list 4 :initial-element t))) ; pc-reg

(defun reset-sequence ()
  (declare (xargs :guard t))
  (cons (reset-vector) (make-list 19 :initial-element (run-vector))))

(defthm chip-system-operating-inputs-p-reset-sequence
  (chip-system-operating-inputs-p (reset-sequence) 20))

;; The initialized state.

(defun initialized-regfile ()
  (declare (xargs :guard t))
  (list
   ;; regs
   (list
    (cons (cons (cons (cons (ram (make-list 32))
                            (ram (make-list 32)))
                      (cons (ram (make-list 32))
                            (ram (make-list 32))))
                (cons (cons (ram (make-list 32))
                            (ram (make-list 32)))
                      (cons (ram (make-list 32))
                            (ram (make-list 32)))))
          (cons (cons (cons (ram (make-list 32))
                            (ram (make-list 32)))
                      (cons (ram (make-list 32))
                            (ram (make-list 32))))
                (cons (cons (ram (make-list 32))
                            (ram (make-list 32)))
                      (cons (ram (make-list 32))
                            (ram (make-list 32)))))))
   '(nil)                                          ; we
   (pairlis$ (make-list 32) nil)                   ; data
   (pairlis$ (make-list 4 :initial-element t) nil) ; address
   ))

(defun initialized-machine-state ()
  (declare (xargs :guard t))
  (list
   (initialized-regfile)                           ; regs
   (pairlis$ (list t nil nil nil) nil)             ; flags
   (pairlis$ (make-list 32) nil)                   ; a-reg
   (pairlis$ (make-list 32) nil)                   ; b-reg
   (pairlis$ (make-list 32) nil)                   ; i-reg
   (pairlis$ (make-list 32) nil)                   ; data-out
   (pairlis$ (make-list 32) nil)                   ; addr-out
   '(t)                                            ; reset
   '(t)                                            ; dtack
   '(t)                                            ; hold
   (pairlis$ (make-list 4 :initial-element t) nil) ; pc-reg
   (pairlis$ (cv_fetch1                            ; cntl-state
              t                                    ;   RW-
              (list t t t t)                       ;   REGS-ADDRESS
              (make-list 32)                       ;   I-REG
              (list t nil nil nil)                 ;   FLAGS
              (make-list 4 :initial-element t))    ;   PC-REG
             nil)))

(defun initialized-memory-state ()
  (declare (xargs :guard t))
  (list (list 'stub (make-list 32))         ; mem
        0                                   ; cntl
        nil                                 ; clock
        0                                   ; count
        t                                   ; dtack-asserted
        t                                   ; last-rw-
        (make-list 32)                      ; last-address
        (make-list 32 :initial-element *x*) ; last-data
        ))

(defun final-state ()
  (declare (xargs :guard t))
  (list (list (initialized-machine-state))
        (list (initialized-memory-state))))

;; Prove that the reset sequence works, by running the machine.

(defthm reset-works
  (equal (run-fm9001 (unknown-state)
                     (map-up-inputs (reset-sequence))
                     (len (reset-sequence)))
         (final-state)))

(defthm unknown-state-okp
  (and
   (fm9001-state-structure (unknown-state))
   (chip-system-invariant (unknown-state))
   (chip-system-operating-inputs-p (reset-sequence) 20)))

(defthm final-state-okp
  (and
   (chip-system& (chip-system$netlist))
   (fm9001-state-structure (final-state))
   (macrocycle-invariant (final-state)
                         (pairlis$
                          (make-list 4 :initial-element t)
                          nil))))

(defthm instance-theorem
  (let ((fm9001-inputs (map-up-inputs inputs))
        (netlist (chip-system$netlist))
        (st (final-state)))
    (let ((time (total-microcycles st fm9001-inputs n)))
      (implies
       (and (chip-system& netlist)
            (fm9001-state-structure st)
            (macrocycle-invariant st pc)
            (chip-system-operating-inputs-p inputs time)
            (operating-inputs-p fm9001-inputs time))
       (equal (map-up (de-sim-n
                       'chip-system inputs st netlist time))
              (fm9001-interpreter (map-up st)
                                  (strip-cars pc)
                                  n)))))
  :hints (("Goal"
           :use (:instance chip-system=fm9001-interpreter
                           (netlist (chip-system$netlist))
                           (st (final-state))
                           (instructions n))
           :in-theory (theory 'minimal-theory))))

(defthm fm9001-statep-map-up-final-state
  (fm9001-statep (map-up (final-state))))

;; ======================================================================

;; Resetting the CHIP in isolation

(defun reset-vector-chip ()
  (declare (xargs :guard t))
  (list* *x* ; clk
         *x* ; ti
         nil ; te

         *x* ; dtack-
         nil ; reset-
         t   ; hold-
         t   ; disable-regfile-
         t   ; test-regfile-

         (append
          (make-list 4 :initial-element t)       ; pc-reg
          (make-list 32 :initial-element *x*)))) ; data input

;; Note: If clk is *x*, chip output PO will be *x*.
;; First run vector (clk T).  PO will be NIL.

(defun run-vector-chip-1 ()
  (declare (xargs :guard t))
  (list* t   ; clk
         *x* ; ti
         nil ; te

         t ; dtack-
         t ; reset-
         t ; hold-
         t ; disable-regfile-
         t ; test-regfile-

         (append
          (make-list  4 :initial-element t)    ; pc-reg
          (make-list 32 :initial-element t)))) ; data input

;; Second run vector (clk F).  PO will be NIL.

(defun run-vector-chip-2 ()
  (declare (xargs :guard t))
  (list* nil ; clk
         *x* ; ti
         nil ; te

         t ; dtack-
         t ; reset-
         t ; hold-
         t ; disable-regfile-
         t ; test-regfile-

         (append
          (make-list  4 :initial-element t)    ; pc-reg
          (make-list 32 :initial-element t)))) ; data input

(defun reset-sequence-chip-1 ()
  (declare (xargs :guard t))
  (cons (reset-vector-chip)
        (make-list 19 :initial-element (run-vector-chip-1))))

(defun reset-sequence-chip-2 ()
  (declare (xargs :guard t))
  (cons (reset-vector-chip)
        (make-list 19 :initial-element (run-vector-chip-2))))

(defthm reset-sequence-chip-1-vs-2
  (let ((inputs-1 (reset-sequence-chip-1))
        (inputs-2 (reset-sequence-chip-2))
        (st       (list (unknown-machine-state)))
        (netlist  (chip$netlist)))
    (equal (simulate 'chip inputs-1 st netlist)
           (simulate 'chip inputs-2 st netlist))))

(defthm simulate-reset-chip-final-state
  (let ((fn      'chip)
        (inputs  (reset-sequence-chip-1))
        (st      (list (unknown-machine-state)))
        (netlist (chip$netlist)))

    (let ((n (1- (len inputs))))

      (let ((result (nth n (simulate fn inputs st netlist))))

        (let ((final-simulated-state (cadr result)))

          (equal final-simulated-state
                 (car (final-state))))))))

;; This lemma says that the reset sequence is "good" in
;; the sense required by the last lemma below.

(defthmd for-final-1-of-reset-sequence-chip
  (let ((fn      'chip)
        (inputs  (reset-sequence-chip-1))
        (st-1    (list (unknown-machine-state)))
        (netlist (chip$netlist)))

    (let ((n (1- (len inputs))))

      (let ((final-1 (nth n (simulate fn inputs st-1 netlist))))

        (and (equal (< n (len inputs)) t)
             (v-knownp (car final-1))
             (s-knownp (cadr final-1))
             (well-formed-sts fn st-1 netlist)
             (ok-netlistp 0 fn netlist '(mem-32x32)))))))

;; Thus, for any STATE-2, we can reset the machine so long
;; as (S-APPROX STATE-1 STATE-2) is true.  We believe that
;; (S-APPROX STATE-1 STATE-2) is true for any STATE-2 of the
;; proper form.

(defthm xs-suffice-for-reset-chip-lemma-instance
  (let ((fn      'chip)
        (inputs  (reset-sequence-chip-1))
        (st-1    (list (unknown-machine-state)))
        (netlist (chip$netlist)))

    (let ((n (1- (len inputs))))

      (let ((final-1 (nth n (simulate fn inputs st-1 netlist)))
            (final-2 (nth n (simulate fn inputs st-2 netlist))))

        (implies (and (s-approx st-1 st-2)
                      (good-s st-2)
                      (well-formed-sts fn st-2 netlist))
                 (equal final-1 final-2)))))
  :hints (("Goal"
           :in-theory (disable reset-sequence-chip-1
                               (reset-sequence-chip-1)
                               unknown-machine-state
                               (unknown-machine-state)
                               chip$netlist
                               (chip$netlist)
                               simulate
                               ok-netlistp)
           :use (for-final-1-of-reset-sequence-chip
                 (:instance xs-suffice-for-reset-lemma
                            (n       (1- (len (reset-sequence-chip-1))))
                            (fn      'chip)
                            (inputs  (reset-sequence-chip-1))
                            (st-1 (list (unknown-machine-state)))
                            (netlist (chip$netlist)))))))

(defthm fm9001-machine-statep-p-map-up-initialized-machine-state
  (fm9001-machine-statep (p-map-up (initialized-machine-state))))

;; ======================================================================

;; Refinements

(defun all-xs (vec)
  (declare (xargs :guard t))
  (if (atom vec)
      (null vec)
    (and (equal (car vec) *x*)
         (all-xs (cdr vec)))))

;; The following two were enabled in the context where many
;; of the following events were originally developed.

(in-theory (enable b-knownp b-approx))

(defthm all-xs-approximates
  (implies (and (all-xs vec1)
                (equal (len vec1) (len vec2))
                (true-listp vec2))
           (v-approx vec1 vec2))
  :hints (("Goal" :in-theory (enable v-approx))))

(defthm all-xs-make-list
  (all-xs (make-list n :initial-element *x*))
  :hints (("Goal" :in-theory (enable repeat))))

(defun new-machine-state-invariant (machine-state)
  (let
    ((regs               (car machine-state))
     (flags              (cadr machine-state))
     (a-reg              (caddr machine-state))
     (b-reg              (cadddr machine-state))
     (i-reg              (car (cddddr machine-state)))
     (data-out           (cadr (cddddr machine-state)))
     (addr-out           (caddr (cddddr machine-state)))
     (last-reset-        (cadddr (cddddr machine-state)))
     (last-dtack-        (car (cddddr (cddddr machine-state))))
     (last-hold-         (cadr (cddddr (cddddr machine-state))))
     (pc-reg             (caddr (cddddr (cddddr machine-state))))
     (cntl-state         (cadddr (cddddr (cddddr machine-state)))))
    (let
      ((regs-regs    (car regs))
       (regs-we      (cadr regs))
       (regs-data    (caddr regs))
       (regs-address (cadddr regs)))
      (and
       (equal (len machine-state) 12)
       (true-listp machine-state)

       (equal (len regs) 4)
       (true-listp regs)

       (true-listp regs-regs)
       (equal (len regs-regs) 1)
       (all-ramp-mem 4 (car regs-regs))
       (memory-properp 4 32 (car regs-regs))

       (true-listp regs-we)
       (equal (len regs-we) 1)
       (4vp (car regs-we))

       (4v-listp (strip-cars regs-data))
       (len-1-true-listp regs-data) (equal (len regs-data) 32)

       (4v-listp (strip-cars regs-address))
       (len-1-true-listp regs-address) (equal (len regs-address) 4)

       (4v-listp (strip-cars flags))
       (len-1-true-listp flags) (equal (len flags) 4)

       (4v-listp (strip-cars a-reg))
       (len-1-true-listp a-reg) (equal (len a-reg) 32)

       (4v-listp (strip-cars b-reg))
       (len-1-true-listp b-reg) (equal (len b-reg) 32)

       (4v-listp (strip-cars i-reg))
       (len-1-true-listp i-reg) (equal (len i-reg) 32)

       (4v-listp (strip-cars data-out))
       (len-1-true-listp data-out) (equal (len data-out) 32)

       (4v-listp (strip-cars addr-out))
       (len-1-true-listp addr-out) (equal (len addr-out) 32)

       (true-listp last-reset-)
       (equal (len last-reset-) 1)
       (4vp (car last-reset-))

       (true-listp last-dtack-)
       (equal (len last-dtack-) 1)
       (4vp (car last-dtack-))

       (true-listp last-hold-)
       (equal (len last-hold-) 1)
       (4vp (car last-hold-))

       (4v-listp (strip-cars pc-reg))
       (len-1-true-listp pc-reg) (equal (len pc-reg) 4)

       (4v-listp (strip-cars cntl-state))
       (len-1-true-listp cntl-state) (equal (len cntl-state) 40)))))

(encapsulate
  ()

  (local
   (defthm not-memp-4v-listp
     (implies (4v-listp v)
              (and (not (romp v))
                   (not (ramp v))
                   (not (stubp v))))
     :hints (("Goal" :in-theory (enable 4vp mem-theory)))))

  (local
   (defthm all-xs=>4v-listp
     (implies (all-xs v)
              (4v-listp v))))

  (defthm s-approx-make-list
    (implies (and (equal (len vec1) (len vec2))
                  (4v-listp vec2)
                  (all-xs vec1))
             (s-approx vec1 vec2))
    :hints (("Goal" :in-theory (enable s-approx 4vp)))))

(defthm consp-implies-not-4vp
  (implies (consp x)
           (not (4vp x)))
  :hints (("Goal" :in-theory (enable 4vp))))

(defthm b-approx-x
  (b-approx *x* y))

(local
 (defthm len-0=>atom
   (implies (equal (len x) 0)
            (atom x))
   :rule-classes :forward-chaining))

(local
 (defthm 4vp-car=>not-memp
   (implies (4vp (car x))
            (and (not (romp x))
                 (not (ramp x))
                 (not (stubp x))))
   :hints (("Goal"
            :in-theory (enable 4vp mem-theory)))))

(encapsulate
  ()

  (local
   (defthm not-memp-of-all-ramp-mem-1
     (implies (all-ramp-mem 1 mem)
              (and (not (romp mem))
                   (not (ramp mem))
                   (not (stubp mem))))
     :hints (("Goal" :in-theory (enable all-ramp-mem mem-theory)))))

  (local
   (defthm not-memp-of-all-ramp-mem-2
     (implies (all-ramp-mem 2 mem)
              (and (not (romp mem))
                   (not (ramp mem))
                   (not (stubp mem))))
     :hints (("Goal" :in-theory (enable all-ramp-mem mem-theory)))))

  (local
   (defthm not-memp-of-all-ramp-mem-3
     (implies (all-ramp-mem 3 mem)
              (and (not (romp mem))
                   (not (ramp mem))
                   (not (stubp mem))))
     :hints (("Goal" :in-theory (enable all-ramp-mem mem-theory)))))

  (local
   (defthm not-memp-of-all-ramp-mem-4
     (implies (all-ramp-mem 4 mem)
              (and (not (romp mem))
                   (not (ramp mem))
                   (not (stubp mem))))
     :hints (("Goal" :in-theory (enable all-ramp-mem mem-theory)))))

  (local
   (defthm s-approx-of-caar-unknown-regfile
     (implies (and (all-ramp-mem 4 st)
                   (memory-properp 4 32 st))
              (s-approx (caar (unknown-regfile)) st))
     :hints (("Goal"
              :in-theory (union-theories
                          '(s-approx
                            all-ramp-mem
                            memory-properp
                            (unknown-regfile)
                            all-xs-approximates
                            car-cons
                            cdr-cons
                            car-cdr-elim
                            (all-xs)
                            (len)
                            (ram-guts)
                            (ramp)
                            (stubp)
                            (zp)
                            true-listp-ram-guts-of-ramp
                            not-memp-of-all-ramp-mem-1
                            not-memp-of-all-ramp-mem-2
                            not-memp-of-all-ramp-mem-3
                            not-memp-of-all-ramp-mem-4)

                          (theory 'minimal-theory))))))

  (defthm s-approx-of-car-unknown-regfile
    (implies (and (true-listp regs-regs)
                  (equal (len regs-regs) 1)
                  (all-ramp-mem 4 (car regs-regs))
                  (memory-properp 4 32 (car regs-regs)))
             (s-approx (car (unknown-regfile)) regs-regs))
    :hints (("Goal"
             :in-theory (e/d (list-rewrite-1)
                             (s-approx-of-caar-unknown-regfile))
             :use ((:instance s-approx-of-caar-unknown-regfile
                              (st (car regs-regs)))
                   (:instance s-approx-of-list
                              (s1 (caar (unknown-regfile)))
                              (s2 (car regs-regs)))))))
  )

(encapsulate
  ()

  (local
   (defthmd len-1-true-listp=>not-memp
     (implies (len-1-true-listp s)
              (and (not (romp s))
                   (not (ramp s))
                   (not (stubp s))))
     :hints (("Goal"
              :in-theory (enable mem-theory
                                 len-1-true-listp
                                 len-1-listp)))))

  (defthm s-approx-of-pairlis$-make-list
    (implies (and (len-1-true-listp s)
                  (equal (len s) n)
                  (4v-listp (strip-cars s)))
             (s-approx (pairlis$ (make-list n :initial-element *x*)
                                 nil)
                       s))
    :hints (("Goal"
             :in-theory (enable s-approx
                                len-1-true-listp
                                len-1-listp
                                len-1-true-listp=>not-memp))))

  (local
   (defthm not-memp-unknown-regfile
     (and
      (not (romp (list
                  (list
                   (list*
                    (list*
                     (list* (cons (ram (make-list-ac 32 'x nil))
                                  (ram (make-list-ac 32 'x nil)))
                            (ram (make-list-ac 32 'x nil))
                            (ram (make-list-ac 32 'x nil)))
                     (cons (ram (make-list-ac 32 'x nil))
                           (ram (make-list-ac 32 'x nil)))
                     (ram (make-list-ac 32 'x nil))
                     (ram (make-list-ac 32 'x nil)))
                    (list* (cons (ram (make-list-ac 32 'x nil))
                                 (ram (make-list-ac 32 'x nil)))
                           (ram (make-list-ac 32 'x nil))
                           (ram (make-list-ac 32 'x nil)))
                    (cons (ram (make-list-ac 32 'x nil))
                          (ram (make-list-ac 32 'x nil)))
                    (ram (make-list-ac 32 'x nil))
                    (ram (make-list-ac 32 'x nil))))
                  '(x)
                  (pairlis$ (make-list-ac 32 'x nil) nil)
                  (pairlis$ (make-list-ac 4 'x nil)
                            nil))))

      (not (ramp (list
                  (list
                   (list*
                    (list*
                     (list* (cons (ram (make-list-ac 32 'x nil))
                                  (ram (make-list-ac 32 'x nil)))
                            (ram (make-list-ac 32 'x nil))
                            (ram (make-list-ac 32 'x nil)))
                     (cons (ram (make-list-ac 32 'x nil))
                           (ram (make-list-ac 32 'x nil)))
                     (ram (make-list-ac 32 'x nil))
                     (ram (make-list-ac 32 'x nil)))
                    (list* (cons (ram (make-list-ac 32 'x nil))
                                 (ram (make-list-ac 32 'x nil)))
                           (ram (make-list-ac 32 'x nil))
                           (ram (make-list-ac 32 'x nil)))
                    (cons (ram (make-list-ac 32 'x nil))
                          (ram (make-list-ac 32 'x nil)))
                    (ram (make-list-ac 32 'x nil))
                    (ram (make-list-ac 32 'x nil))))
                  '(x)
                  (pairlis$ (make-list-ac 32 'x nil) nil)
                  (pairlis$ (make-list-ac 4 'x nil)
                            nil))))

      (not (stubp (list
                   (list
                    (list*
                     (list*
                      (list* (cons (ram (make-list-ac 32 'x nil))
                                   (ram (make-list-ac 32 'x nil)))
                             (ram (make-list-ac 32 'x nil))
                             (ram (make-list-ac 32 'x nil)))
                      (cons (ram (make-list-ac 32 'x nil))
                            (ram (make-list-ac 32 'x nil)))
                      (ram (make-list-ac 32 'x nil))
                      (ram (make-list-ac 32 'x nil)))
                     (list* (cons (ram (make-list-ac 32 'x nil))
                                  (ram (make-list-ac 32 'x nil)))
                            (ram (make-list-ac 32 'x nil))
                            (ram (make-list-ac 32 'x nil)))
                     (cons (ram (make-list-ac 32 'x nil))
                           (ram (make-list-ac 32 'x nil)))
                     (ram (make-list-ac 32 'x nil))
                     (ram (make-list-ac 32 'x nil))))
                   '(x)
                   (pairlis$ (make-list-ac 32 'x nil) nil)
                   (pairlis$ (make-list-ac 4 'x nil)
                             nil))))
      )))

  (local
   (defthm not-memp-regfile
     (let ((st (list regs-regs regs-we regs-data regs-address)))
       (and (not (romp st))
            (not (ramp st))
            (not (stubp st))))
     :hints (("Goal" :in-theory (enable mem-theory)))))

  (local
   (defthm s-approx-of-unknown-regfile
     (let ((st (list regs-regs regs-we regs-data regs-address)))
       (implies (and (true-listp regs-regs)
                     (equal (len regs-regs) 1)
                     (all-ramp-mem 4 (car regs-regs))
                     (memory-properp 4 32 (car regs-regs))
                     (true-listp regs-we)
                     (equal (len regs-we) 1)
                     (4vp (car regs-we))
                     (4v-listp (strip-cars regs-data))
                     (len-1-true-listp regs-data)
                     (equal (len regs-data) 32)
                     (4v-listp (strip-cars regs-address))
                     (len-1-true-listp regs-address)
                     (equal (len regs-address) 4))
                (s-approx (unknown-regfile) st)))
     :hints (("Goal"
              :use s-approx-of-car-unknown-regfile
              :in-theory (e/d (s-approx)
                              (pairlis$
                               s-approx-opener
                               s-approx-of-car-unknown-regfile
                               true-listp-rom-guts-of-romp
                               true-listp-ram-guts-of-ramp
                               true-listp-stub-guts-of-stubp
                               bvp-is-true-listp
                               v-approx-preserves-true-listp
                               bvp-cvzbv
                               iff
                               true-listp-of-v-approx
                               default-car
                               default-cdr
                               (all-ramp-mem)
                               (memory-properp)
                               (unknown-regfile)
                               make-list-ac
                               (make-list-ac)
                               make-list-ac-removal))))))

  (local
   (defthm not-memp-machine-state
     (let ((st (list (list s1-1 s1-2 s1-3 s1-4)
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12)))
       (and (not (romp st))
            (not (ramp st))
            (not (stubp st))))
     :hints (("Goal" :in-theory (enable mem-theory)))))

  (defthm machine-state-invariant-implies-s-approx-lemma-1
    (implies (and (new-machine-state-invariant st)
                  (equal st
                         (list (list s1-1 s1-2 s1-3 s1-4)
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12)))
             (s-approx (unknown-machine-state) st))
    :hints (("Goal"
             :in-theory (e/d (s-approx)
                             (pairlis$
                              (unknown-machine-state)
                              unknown-regfile
                              (unknown-regfile)
                              make-list-ac
                              (make-list-ac)
                              make-list-ac-removal)))))
  )

(defthmd machine-state-invariant-implies-s-approx-lemma-2
  (let ((s1-1 (caar st))
        (s1-2 (cadar st))
        (s1-3 (caddar st))
        (s1-4 (car (cdddar st)))
        (s2  (cadr st))
        (s3  (caddr st))
        (s4  (cadddr st))
        (s5  (car (cddddr st)))
        (s6  (cadr (cddddr st)))
        (s7  (caddr (cddddr st)))
        (s8  (cadddr (cddddr st)))
        (s9  (car (cddddr (cddddr st))))
        (s10 (cadr (cddddr (cddddr st))))
        (s11 (caddr (cddddr (cddddr st))))
        (s12 (cadddr (cddddr (cddddr st)))))
    (implies (and (equal (len st) 12)
                  (true-listp st)
                  (equal (len (car st)) 4)
                  (true-listp (car st)))
             (equal (list (list s1-1 s1-2 s1-3 s1-4)
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12)
                    st))))

(defthmd machine-state-invariant-implies-s-approx-lemma-3
  (implies (new-machine-state-invariant st)
           (and (equal (len st) 12)
                (true-listp st)
                (equal (len (car st)) 4)
                (true-listp (car st)))))

(defthm machine-state-invariant-implies-s-approx
  (implies (new-machine-state-invariant st)
           (s-approx (unknown-machine-state) st))
  :hints
  (("Goal"
    :in-theory (theory 'minimal-theory)
    :use (machine-state-invariant-implies-s-approx-lemma-2
          machine-state-invariant-implies-s-approx-lemma-3
          (:instance
           machine-state-invariant-implies-s-approx-lemma-1
           (s1-1 (caar st))
           (s1-2 (cadar st))
           (s1-3 (caddar st))
           (s1-4 (car (cdddar st)))
           (s2  (cadr st))
           (s3  (caddr st))
           (s4  (cadddr st))
           (s5  (car (cddddr st)))
           (s6  (cadr (cddddr st)))
           (s7  (caddr (cddddr st)))
           (s8  (cadddr (cddddr st)))
           (s9  (car (cddddr (cddddr st))))
           (s10 (cadr (cddddr (cddddr st))))
           (s11 (caddr (cddddr (cddddr st))))
           (s12 (cadddr (cddddr (cddddr st)))))))))

(defthm good-s-of-list
  (implies (good-s s)
           (good-s (list s)))
  :hints (("Goal" :in-theory (enable mem-theory))))

(defthm good-s-opener
  (and (implies (ramp s)
                (equal (good-s s)
                       (equal (len (ram-guts s))
                              (mem-width))))
       (implies (romp s)
                (equal (good-s s)
                       (equal (len (rom-guts s))
                              (mem-width))))
       (implies (stubp s)
                (equal (good-s s)
                       (equal (len (stub-guts s))
                              (mem-width))))
       (implies (and (not (memp s))
                     (consp s))
                (equal (good-s s)
                       (and (good-s (car s))
                            (good-s (cdr s)))))
       (implies (4vp s)
                (good-s s))))

(local (in-theory (disable good-s)))

(defthmd memory-properp-implies-good-s
  (implies (memory-properp n 32 v)
           (good-s v))
  :hints (("Goal" :in-theory (enable memory-properp))))

(defthm memory-properp-implies-list-good-s
  (implies (and (true-listp regs-regs)
                (equal (len regs-regs) 1)
                (memory-properp n 32 (car regs-regs)))
           (good-s regs-regs))
  :hints (("Goal"
           :use (:instance good-s-of-list
                           (s (car regs-regs)))
           :in-theory (enable memory-properp-implies-good-s
                              list-rewrite-1))))

(encapsulate
  ()

  (local
   (defthmd new-machine-state-invariant-implies-good-s-aux-1
     (implies (and (equal (len v) 1)
                   (4vp (car v)))
              (good-s v))
     :hints (("Goal" :in-theory (enable good-s)))))

  (local
   (defthm new-machine-state-invariant-implies-good-s-aux-2
     (implies (and (len-1-true-listp v)
                   (4v-listp (strip-cars v)))
              (good-s v))
     :hints (("Goal" :in-theory (enable len-1-true-listp len-1-listp)))))

  (local
   (defthm new-machine-state-invariant-implies-good-s-aux-3
     (implies (and (not (memp s))
                   (true-listp s)
                   (equal (+ 11 (len s))
                          12)
                   (len-1-true-listp (car s))
                   (4v-listp (strip-cars (car s))))
              (good-s s))
     :hints (("Goal" :in-theory (enable list-rewrite-1)))))

  (local
   (defthm new-machine-state-invariant-implies-good-s-aux-4
     (implies (new-machine-state-invariant st)
              (and (not (romp st))
                   (not (ramp st))
                   (not (stubp st))

                   (not (romp (car st)))
                   (not (ramp (car st)))
                   (not (stubp (car st)))

                   (not (romp (cdar st)))
                   (not (ramp (cdar st)))
                   (not (stubp (cdar st)))

                   (not (romp (cddar st)))
                   (not (ramp (cddar st)))
                   (not (stubp (cddar st)))

                   (not (romp (cdddar st)))
                   (not (ramp (cdddar st)))
                   (not (stubp (cdddar st)))

                   (not (romp (cdr st)))
                   (not (ramp (cdr st)))
                   (not (stubp (cdr st)))

                   (not (romp (cddr st)))
                   (not (ramp (cddr st)))
                   (not (stubp (cddr st)))

                   (not (romp (cdddr st)))
                   (not (ramp (cdddr st)))
                   (not (stubp (cdddr st)))

                   (not (romp (cddddr st)))
                   (not (ramp (cddddr st)))
                   (not (stubp (cddddr st)))

                   (not (romp (cdr (cddddr st))))
                   (not (ramp (cdr (cddddr st))))
                   (not (stubp (cdr (cddddr st))))

                   (not (romp (cddr (cddddr st))))
                   (not (ramp (cddr (cddddr st))))
                   (not (stubp (cddr (cddddr st))))

                   (not (romp (cdddr (cddddr st))))
                   (not (ramp (cdddr (cddddr st))))
                   (not (stubp (cdddr (cddddr st))))

                   (not (romp (cddddr (cddddr st))))
                   (not (ramp (cddddr (cddddr st))))
                   (not (stubp (cddddr (cddddr st))))

                   (not (romp (cdr (cddddr (cddddr st)))))
                   (not (ramp (cdr (cddddr (cddddr st)))))
                   (not (stubp (cdr (cddddr (cddddr st)))))

                   (not (romp (cddr (cddddr (cddddr st)))))
                   (not (ramp (cddr (cddddr (cddddr st)))))
                   (not (stubp (cddr (cddddr (cddddr st)))))

                   (not (romp (cdddr (cddddr (cddddr st)))))
                   (not (ramp (cdddr (cddddr (cddddr st)))))
                   (not (stubp (cdddr (cddddr (cddddr st)))))
                   ))
     :hints (("Goal"
              :in-theory (e/d (mem-theory)
                              (bvp-is-true-listp
                               bvp-cvzbv))))))

  (defthm new-machine-state-invariant-implies-good-s
    (implies (new-machine-state-invariant st)
             (good-s st))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (union-theories
                         '(new-machine-state-invariant
                           good-s
                           len
                           memp
                           memory-properp-implies-list-good-s
                           new-machine-state-invariant-implies-good-s-aux-1
                           new-machine-state-invariant-implies-good-s-aux-2
                           new-machine-state-invariant-implies-good-s-aux-3
                           new-machine-state-invariant-implies-good-s-aux-4)
                         (theory 'minimal-theory)))))
  )

(defthm xs-suffice-for-reset-chip-final-state-for-any-unknown-state
  (let ((n (1- (len (reset-sequence-chip-1)))))

    (let ((final-1 (cadr (nth n (simulate 'chip
                                          (reset-sequence-chip-1)
                                          (list (unknown-machine-state))
                                          (chip$netlist)))))
          (final-2 (cadr (nth n (simulate 'chip
                                          (reset-sequence-chip-1)
                                          (list st)
                                          (chip$netlist))))))

      (implies (and (new-machine-state-invariant st)
                    (well-formed-sts 'chip (list st) (chip$netlist)))
               (equal final-1 final-2))))
  :hints (("Goal"
           :in-theory (union-theories
                       '(s-approx-of-list
                         good-s-of-list
                         machine-state-invariant-implies-s-approx
                         new-machine-state-invariant-implies-good-s)
                       (theory 'minimal-theory))
           :use (:instance xs-suffice-for-reset-chip-lemma-instance
                           (st-2 (list st))))))

;; The following is a main theorem.  It follows readily from
;; XS-SUFFICE-FOR-RESET-CHIP-LEMMA-INSTANCE together with the theorem
;; SIMULATE-RESET-CHIP-FINAL-STATE, which essentially tells us that
;; when we simulate from the (UNKNOWN-MACHINE-STATE) we get to
;; (INITIALIZED-MACHINE-STATE).  The main improvement of this theorem
;; over XS-SUFFICE-FOR-RESET-CHIP-LEMMA-INSTANCE is that the
;; hypothesis here avoids the notion of ``approximation'' in favor
;; of a simple invariant on the structure of the state (see
;; NEW-MACHINE-STATE-INVARIANT-IS-NON-TRIVIAL and
;; NEW-MACHINE-STATE-INVARIANT-IMPLIES-MACHINE-STATE-INVARIANT
;; below).

(defthm xs-suffice-for-reset-chip-final-state-for-any-unknown-state-better
  (let ((n (1- (len (reset-sequence-chip-1)))))
    (implies (and (new-machine-state-invariant st)
                  (well-formed-sts 'chip (list st) (chip$netlist)))
             (equal (cadr (nth n (simulate 'chip
                                           (reset-sequence-chip-1)
                                           (list st)
                                           (chip$netlist))))
                    (list (initialized-machine-state)))))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     '(xs-suffice-for-reset-chip-final-state-for-any-unknown-state
       final-state
       car-cons)
     (theory 'minimal-theory))
    :use (simulate-reset-chip-final-state))))

(defthm new-machine-state-invariant-is-non-trivial
  (new-machine-state-invariant (unknown-machine-state)))

(defthm new-machine-state-invariant-implies-machine-state-invariant
  (implies (new-machine-state-invariant machine-state)
           (machine-state-invariant machine-state)))

;; ======================================================================

;; Consider the lemma FM9001=CHIP-SYSTEM from "proofs.lisp".  We can
;; replace the FM9001-STATEP hypothesis in that lemma with a
;; MEMORY-OKP hypothesis for the class of machine states we are
;; considering, i.e., those obtained at the end of the reset sequence.

(defthm fm9001-statep-implies-memory-ok-p-instance
  (let ((st (map-up (list (list (initialized-machine-state))
                          machine-memory))))
    (implies (memory-okp 32 32 (cadr st))
             (fm9001-statep st))))

;; Just a lemma along the way to FM9001=CHIP-SYSTEM-TRUE-AFTER-RESET.

(defthm fm9001=chip-system-true-after-reset-lemma
  (let ((st (map-up (list (list (initialized-machine-state))
                          machine-memory))))
    (implies (and (chip-system& netlist)
                  ;;(fm9001-statep st)
                  (memory-okp 32 32 (cadr st))
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
                      'chip-system
                      inputs
                      (map-down st)
                      netlist
                      (total-microcycles (map-down st)
                                         (map-up-inputs inputs)
                                         n))))))
  :hints (("Goal"
           :use (:instance
                 fm9001=chip-system
                 (st (map-up (list (list (initialized-machine-state))
                                   machine-memory)))))))

;; (defthm map-down-inverts-map-up
;;   (let ((machine-memory
;;          (list memory 0 0 0 t t
;;                (make-list 32)
;;                (make-list 32 :initial-element *x*))))
;;     (let ((st (map-up (list (list (initialized-machine-state))
;;                             (list machine-memory)))))
;;       (implies (memory-okp 32 32 (cadr st))
;;                (equal (map-down st)
;;                       (list (list (initialized-machine-state))
;;                             (list machine-memory)))))))

;; Here is a statement of FM9001=CHIP-SYSTEM, which, when combined
;; with the reset lemma
;; XS-SUFFICE-FOR-RESET-CHIP-FINAL-STATE-FOR-ANY-UNKNOWN-STATE-BETTER
;; above, says that the chip implements its specification assuming
;; that we attach the memory after the reset process.  This is a
;; general statement; without a particular memory design, it seems
;; difficult to come up with a statement that is much ``better'' than
;; this one.

(defthm fm9001=chip-system-true-after-reset
  (let ((machine-memory
         (list memory 0 0 0 t t
               (make-list 32)
               (make-list 32 :initial-element *x*))))
    (let ((st (map-up (list (list (initialized-machine-state))
                            (list machine-memory))))
          (low-st (list (list (initialized-machine-state))
                        (list machine-memory))))
      (implies (and (chip-system& netlist)
                    (memory-okp 32 32 memory)
                    (chip-system-operating-inputs-p
                     inputs
                     (total-microcycles low-st
                                        (map-up-inputs inputs)
                                        n))
                    (operating-inputs-p
                     (map-up-inputs inputs)
                     (total-microcycles low-st
                                        (map-up-inputs inputs)
                                        n)))
               (equal (fm9001 st n)
                      (map-up
                       (de-sim-n
                        'chip-system
                        inputs
                        low-st
                        netlist
                        (total-microcycles low-st
                                           (map-up-inputs inputs)
                                           n)))))))
  :hints (("Goal"
           :use (:instance
                 fm9001=chip-system-true-after-reset-lemma
                 (machine-memory
                  (list
                   (list memory 0 0 0 t t
                         (make-list 32)
                         (make-list 32 :initial-element *x*))))))))

;; Let us compensate now for the corresponding two enables
;; appearing above.

(in-theory (disable b-knownp b-approx))

;; ======================================================================

;; Final Statements

;; Below are our most general statements about the correctness of the
;; FM9001 microprocessor.

;; Some of the earlier lemmas were written in terms of SIMULATE.  Since we
;; are only interested in the final state, we show that SIMULATE contains
;; DE-SIM-N.

(defthm simulate-contains-de-sim-n
  (implies
   (and (not (zp n))
        (<= n (len inputs)))
   (equal (cadr (nth (1- n) (simulate fn inputs st netlist)))
          (de-sim-n fn inputs st netlist n)))
  :hints (("Goal" :in-theory (enable de-sim-n))))

(defthm len-reset-sequence-chip-1
  (equal (len (reset-sequence-chip-1))
         20))

;; RESET-CHIP shows that CHIP can be reset from a completely unknown state.

(defthm reset-chip
  (equal (de-sim-n
          'chip
          (reset-sequence-chip-1)
          (list (unknown-machine-state))
          (chip$netlist)
          (len (reset-sequence-chip-1)))
         (list (initialized-machine-state))))

;; RESET-CHIP-FROM-ANY-STATE shows that the machine can be reset from any
;; state of the proper shape.

(defthm reset-chip-from-any-state
  (implies
   (and (s-approx (list (unknown-machine-state)) any-state)
        (good-s any-state)
        (well-formed-sts 'chip any-state (chip$netlist)))
   (equal (de-sim-n
           'chip
           (reset-sequence-chip-1)
           any-state
           (chip$netlist)
           (len (reset-sequence-chip-1)))
          (list (initialized-machine-state))))
  :hints (("Goal"
           :use (:instance
                 xs-suffice-for-reset-chip-lemma-instance
                 (st-2 any-state)))))

;; CHIP-SYSTEM=FM9001-INTERPRETER$AFTER-RESET is the same as the lemma
;; chip-system=fm9001-interpreter in "proofs.lisp", except that it's
;; specialized to the case where the initial state is made up of the chip
;; state after reset (i.e., (INITIALIZED-MACHINE-STATE)) together with an
;; appropriate machine memory.  Thus, the hypothesis
;; (fm9001-state-structure state) has been omitted and the rather
;; elaborate hypothesis (macrocycle-invariant state) has been replaced by
;; the much weaker hypothesis (memory-okp 32 32 memory).  We can do this
;; because (INITIALIZED-MACHINE-STATE) satisfies the processor state
;; portions of these two hypotheses.

(defthm chip-system=fm9001-interpreter$after-reset
  (let ((st
         (list
          (list (initialized-machine-state))
          (list (list memory 0 clock 0 *x* t
                      (make-list 32)
                      (make-list 32 :initial-element *x*))))))
    (let ((rtl-inputs (map-up-inputs inputs)))
      (let ((clock-cycles (total-microcycles st rtl-inputs instructions)))
        (implies
         (and (chip-system& netlist)
              (memory-okp 32 32 memory)
              (chip-system-operating-inputs-p inputs clock-cycles)
              (operating-inputs-p rtl-inputs clock-cycles))
         (equal (map-up (de-sim-n
                         'chip-system inputs st netlist clock-cycles))
                (fm9001-interpreter (map-up st)
                                    (make-list 4 :initial-element t)
                                    instructions))))))
  :hints (("Goal"
           :in-theory (enable fm9001-state-structure)
           :use (:instance
                 chip-system=fm9001-interpreter
                 (st (list
                      (list (initialized-machine-state))
                      (list (list memory 0 clock 0 *x* t
                                  (make-list 32)
                                  (make-list 32 :initial-element *x*)))))
                 (pc (pairlis$ (make-list 4 :initial-element t)
                               nil))))))


