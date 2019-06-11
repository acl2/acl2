;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "arb-merge1")
(include-book "../fifo/queue40-l")

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "std/lists/sets" :dir :system))

(local (in-theory (disable nth 3v-fix)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of INTERL
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of INTERL
;;
;; Construct a DE module generator for circuits performing the
;; first-come-first-served arbitrated merge using the link-joint model.  These
;; circuits consist of two 40-link queues connected to the two input ports of
;; an arbitrated merge.

(defconst *interl$select-num* *arb-merge$select-num*)
(defconst *interl$prim-go-num* 2)
(defconst *interl$go-num* (+ *interl$prim-go-num*
                             (* 2 *queue40-l$go-num*)
                             *arb-merge$go-num*))

(defun interl$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 3 (* 2 (mbe :logic (nfix data-size)
                 :exec  data-size))))

(defun interl$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (interl$data-ins-len data-size)
     *interl$select-num*
     *interl$go-num*))

;; DE module generator of INTERL

(module-generator
 interl* (data-size)
 (si 'interl data-size)
 (list* 'full-in0 'full-in1 'empty-out-
        (append (sis 'data0-in 0 data-size)
                (sis 'data1-in 0 data-size)
                (cons 'select (sis 'go 0 *interl$go-num*))))
 (list* 'in0-act 'in1-act 'out-act
        (sis 'data-out 0 data-size))
 '(q40-l0 q40-l1)
 (list
  ;; LINKS
  ;; 40-link queue Q40-L0
  (list 'q40-l0
        (list* 'q40-l0-ready-in- 'q40-l0-ready-out
               (sis 'q40-l0-data-out 0 data-size))
        (si 'queue40-l data-size)
        (list* 'in0-act 'out-act0
               (append (sis 'q40-l0-data-in 0 data-size)
                       (sis 'go
                            *interl$prim-go-num*
                            *queue40-l$go-num*))))

  ;; 40-link queue Q40-L1
  (list 'q40-l1
        (list* 'q40-l1-ready-in- 'q40-l1-ready-out
               (sis 'q40-l1-data-out 0 data-size))
        (si 'queue40-l data-size)
        (list* 'in1-act 'out-act1
               (append (sis 'q40-l1-data-in 0 data-size)
                       (sis 'go
                            (+ *interl$prim-go-num*
                               *queue40-l$go-num*)
                            *queue40-l$go-num*))))

  ;; JOINTS
  ;; In0
  (list 'in0-cntl
        '(in0-act)
        'joint-cntl
        (list 'full-in0 'q40-l0-ready-in- (si 'go 0)))
  (list 'in0-op
        (sis 'q40-l0-data-in 0 data-size)
        (si 'v-buf data-size)
        (sis 'data0-in 0 data-size))

  ;; In1
  (list 'in1-cntl
        '(in1-act)
        'joint-cntl
        (list 'full-in1 'q40-l1-ready-in- (si 'go 1)))
  (list 'in1-op
        (sis 'q40-l1-data-in 0 data-size)
        (si 'v-buf data-size)
        (sis 'data1-in 0 data-size))

  ;; arb-merge
  (list 'arb-merge
        (list* 'out-act 'out-act0 'out-act1
               (sis 'data-out 0 data-size))
        (si 'arb-merge data-size)
        (list* 'q40-l0-ready-out 'q40-l1-ready-out 'empty-out-
               (append (sis 'q40-l0-data-out 0 data-size)
                       (sis 'q40-l1-data-out 0 data-size)
                       (cons 'select
                             (sis 'go
                                  (+ *interl$prim-go-num*
                                     (* 2 *queue40-l$go-num*))
                                  *arb-merge$go-num*))))))

 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'interl
                           '(q40-l0 q40-l1)
                           0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; INTERL.

(defund interl$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (interl* data-size)
        (union$ (queue40-l$netlist data-size)
                (arb-merge$netlist data-size)
                :test 'equal)))

;; Recognizer for INTERL

(defund interl& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'interl data-size) netlist)))
    (and (equal (assoc (si 'interl data-size) netlist)
                (interl* data-size))
         (joint-cntl& subnetlist)
         (v-buf& subnetlist data-size)
         (queue40-l& subnetlist data-size)
         (arb-merge& subnetlist data-size))))

;; Sanity check

(local
 (defthmd check-interl$netlist-64
   (and (net-syntax-okp (interl$netlist 64))
        (net-arity-okp (interl$netlist 64))
        (interl& (interl$netlist 64) 64))))

;; Constraints on the state of INTERL

(defund interl$st-format (st data-size)
  (b* ((q40-l0 (nth *interl$q40-l0* st))
       (q40-l1 (nth *interl$q40-l1* st)))
    (and (< 0 data-size)
         (queue40-l$st-format q40-l0 data-size)
         (queue40-l$st-format q40-l1 data-size))))

(defthm interl$st-format=>constraint
  (implies (interl$st-format st data-size)
           (posp data-size))
  :hints (("Goal" :in-theory (enable interl$st-format)))
  :rule-classes :forward-chaining)

(defund interl$valid-st (st data-size)
  (b* ((q40-l0 (nth *interl$q40-l0* st))
       (q40-l1 (nth *interl$q40-l1* st)))
    (and (< 0 data-size)
         (queue40-l$valid-st q40-l0 data-size)
         (queue40-l$valid-st q40-l1 data-size))))

(defthmd interl$valid-st=>constraint
  (implies (interl$valid-st st data-size)
           (posp data-size))
  :hints (("Goal" :in-theory (enable queue40-l$valid-st=>constraint
                                     interl$valid-st)))
  :rule-classes :forward-chaining)

(defthmd interl$valid-st=>st-format
  (implies (interl$valid-st st data-size)
           (interl$st-format st data-size))
  :hints (("Goal" :in-theory (e/d (queue40-l$valid-st=>st-format
                                   interl$st-format
                                   interl$valid-st)
                                  ()))))

;; Extract the input and output signals for INTERL

(progn
  ;; Extract the 1st input data item

  (defun interl$data0-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (mbe :logic (nfix data-size)
               :exec  data-size)
          (nthcdr 3 inputs)))

  (defthm len-interl$data0-in
    (equal (len (interl$data0-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable interl$data0-in))

  ;; Extract the 2nd input data item

  (defun interl$data1-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (b* ((size (mbe :logic (nfix data-size)
                     :exec  data-size)))
      (take size
            (nthcdr (+ 3 size) inputs))))

  (defthm len-interl$data1-in
    (equal (len (interl$data1-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable interl$data1-in))

  ;; Extract the "in0-act" signal

  (defund interl$in0-act (inputs st data-size)
    (b* ((full-in0   (nth 0 inputs))
         (go-signals (nthcdr (+ (interl$data-ins-len data-size)
                                *interl$select-num*)
                             inputs))

         (go-in0 (nth 0 go-signals))

         (q40-l0 (nth *interl$q40-l0* st))
         (q40-l0-ready-in- (queue40-l$ready-in- q40-l0)))

      (joint-act full-in0 q40-l0-ready-in- go-in0)))

  (defthm interl$in0-act-inactive
    (implies (not (nth 0 inputs))
             (not (interl$in0-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable interl$in0-act))))

  ;; Extract the "in1-act" signal

  (defund interl$in1-act (inputs st data-size)
    (b* ((full-in1   (nth 1 inputs))
         (go-signals (nthcdr (+ (interl$data-ins-len data-size)
                                *interl$select-num*)
                             inputs))

         (go-in1 (nth 1 go-signals))

         (q40-l1 (nth *interl$q40-l1* st))
         (q40-l1-ready-in- (queue40-l$ready-in- q40-l1)))

      (joint-act full-in1 q40-l1-ready-in- go-in1)))

  (defthm interl$in1-act-inactive
    (implies (not (nth 1 inputs))
             (not (interl$in1-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable interl$in1-act))))

  ;; Extract the inputs for joint ARB-MERGE

  (defund interl$arb-merge-inputs (inputs st data-size)
    (b* ((empty-out- (nth 2 inputs))
         (select     (nth (interl$data-ins-len data-size) inputs))
         (go-signals (nthcdr (+ (interl$data-ins-len data-size)
                                *interl$select-num*)
                             inputs))

         (arb-merge-go-signals (take *arb-merge$go-num*
                                     (nthcdr (+ *interl$prim-go-num*
                                                *queue40-l$go-num*
                                                *queue40-l$go-num*)
                                             go-signals)))

         (q40-l0 (nth *interl$q40-l0* st))
         (q40-l1 (nth *interl$q40-l1* st))

         (q40-l0-ready-out (queue40-l$ready-out q40-l0))
         (q40-l0-data-out (queue40-l$data-out q40-l0))
         (q40-l1-ready-out (queue40-l$ready-out q40-l1))
         (q40-l1-data-out (queue40-l$data-out q40-l1)))
      (list* q40-l0-ready-out q40-l1-ready-out empty-out-
             (append q40-l0-data-out q40-l1-data-out
                     (cons select arb-merge-go-signals)))))

  ;; Extract the "out-act0" signal

  (defund interl$out-act0 (inputs st data-size)
    (b* ((arb-merge-inputs (interl$arb-merge-inputs inputs st data-size)))
      (arb-merge$act0 arb-merge-inputs data-size)))

  (defthm interl$out-act0-inactive
    (implies (equal (nth 2 inputs) t)
             (not (interl$out-act0 inputs st data-size)))
    :hints (("Goal" :in-theory (enable interl$arb-merge-inputs
                                       interl$out-act0))))

  ;; Extract the "out-act1" signal

  (defund interl$out-act1 (inputs st data-size)
    (b* ((arb-merge-inputs (interl$arb-merge-inputs inputs st data-size)))
      (arb-merge$act1 arb-merge-inputs data-size)))

  (defthm interl$out-act1-inactive
    (implies (equal (nth 2 inputs) t)
             (not (interl$out-act1 inputs st data-size)))
    :hints (("Goal" :in-theory (enable interl$arb-merge-inputs
                                       interl$out-act1))))

  (defthm interl$out-act-mutually-exclusive
    (implies (and (interl$valid-st st data-size)
                  (interl$out-act0 inputs st data-size))
             (not (interl$out-act1 inputs st data-size)))
    :hints (("Goal" :in-theory (enable interl$valid-st
                                       interl$arb-merge-inputs
                                       interl$out-act0
                                       interl$out-act1))))

  ;; Extract the "out-act" signal

  (defund interl$out-act (inputs st data-size)
    (f-or (interl$out-act0 inputs st data-size)
          (interl$out-act1 inputs st data-size)))

  (defthm interl$out-act-inactive
    (implies (equal (nth 2 inputs) t)
             (not (interl$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable interl$out-act))))

  ;; Extract the inputs for link Q40-L0

  (defund interl$q40-l0-inputs (inputs st data-size)
    (b* ((in0-act (interl$in0-act inputs st data-size))
         (data0-in (interl$data0-in inputs data-size))
         (go-signals (nthcdr (+ (interl$data-ins-len data-size)
                                *interl$select-num*)
                             inputs))

         (q40-l0-go-signals (take *queue40-l$go-num*
                                  (nthcdr *interl$prim-go-num*
                                          go-signals)))

         (arb-merge-inputs (interl$arb-merge-inputs inputs st data-size))
         (out-act0 (arb-merge$act0 arb-merge-inputs data-size)))

      (list* in0-act out-act0
             (append data0-in q40-l0-go-signals))))

  ;; Extract the inputs for link Q40-L1

  (defund interl$q40-l1-inputs (inputs st data-size)
    (b* ((in1-act (interl$in1-act inputs st data-size))
         (data1-in (interl$data1-in inputs data-size))
         (go-signals (nthcdr (+ (interl$data-ins-len data-size)
                                *interl$select-num*)
                             inputs))

         (q40-l1-go-signals (take *queue40-l$go-num*
                                  (nthcdr (+ *interl$prim-go-num*
                                             *queue40-l$go-num*)
                                          go-signals)))

         (arb-merge-inputs (interl$arb-merge-inputs inputs st data-size))
         (out-act1 (arb-merge$act1 arb-merge-inputs data-size)))

      (list* in1-act out-act1
             (append data1-in q40-l1-go-signals))))

  ;; Extract the output data

  (defund interl$data-out (inputs st data-size)
    (b* ((arb-merge-inputs (interl$arb-merge-inputs inputs st data-size)))
      (arb-merge$data-out arb-merge-inputs data-size)))

  (defthm len-interl$data-out-1
    (implies (interl$st-format st data-size)
             (equal (len (interl$data-out inputs st data-size))
                    data-size))
    :hints (("Goal" :in-theory (enable interl$st-format
                                       interl$data-out))))

  (defthm len-interl$data-out-2
    (implies (interl$valid-st st data-size)
             (equal (len (interl$data-out inputs st data-size))
                    data-size))
    :hints (("Goal" :in-theory (enable queue40-l$valid-st=>constraint
                                       interl$valid-st
                                       interl$data-out))))

  (defun interl$outputs (inputs st data-size)
    (list* (interl$in0-act inputs st data-size)
           (interl$in1-act inputs st data-size)
           (interl$out-act inputs st data-size)
           (interl$data-out inputs st data-size)))
  )

;; The value lemma for INTERL

(defthm interl$value
  (b* ((inputs (list* full-in0 full-in1 empty-out-
                      (append data0-in data1-in
                              (cons select go-signals)))))
    (implies (and (interl& netlist data-size)
                  (true-listp data0-in)
                  (equal (len data0-in) data-size)
                  (true-listp data1-in)
                  (equal (len data1-in) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *interl$go-num*)
                  (interl$st-format st data-size))
             (equal (se (si 'interl data-size) inputs st netlist)
                    (interl$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'interl data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            interl&
                            interl*$destructure
                            interl$st-format
                            arb-merge$act
                            interl$arb-merge-inputs
                            interl$in0-act
                            interl$in1-act
                            interl$out-act0
                            interl$out-act1
                            interl$out-act
                            interl$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of INTERL.

(defun interl$step (inputs st data-size)
  (b* ((q40-l0    (nth *interl$q40-l0* st))
       (q40-l1    (nth *interl$q40-l1* st))

       (q40-l0-inputs (interl$q40-l0-inputs inputs st data-size))
       (q40-l1-inputs (interl$q40-l1-inputs inputs st data-size)))
    (list
      ;; Q40-L0
     (queue40-l$step q40-l0-inputs q40-l0 data-size)
     ;; Q40-L1
     (queue40-l$step q40-l1-inputs q40-l1 data-size))))

;; The state lemma for INTERL

(defthm interl$state
  (b* ((inputs (list* full-in0 full-in1 empty-out-
                      (append data0-in data1-in
                              (cons select go-signals)))))
    (implies (and (interl& netlist data-size)
                  (true-listp data0-in)
                  (equal (len data0-in) data-size)
                  (true-listp data1-in)
                  (equal (len data1-in) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *interl$go-num*)
                  (interl$st-format st data-size))
             (equal (de (si 'interl data-size) inputs st netlist)
                    (interl$step inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'interl data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            interl&
                            interl*$destructure
                            interl$st-format
                            interl$data0-in
                            interl$data1-in
                            interl$q40-l0-inputs
                            interl$q40-l1-inputs
                            interl$arb-merge-inputs
                            interl$in0-act
                            interl$in1-act)
                           (de-module-disabled-rules)))))

(in-theory (disable interl$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund interl$input-format (inputs data-size)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-size))))
  (b* ((full-in0   (nth 0 inputs))
       (full-in1   (nth 1 inputs))
       (empty-out- (nth 2 inputs))
       (data0-in   (interl$data0-in inputs data-size))
       (data1-in   (interl$data1-in inputs data-size))
       (select     (nth (interl$data-ins-len data-size) inputs))
       (go-signals (nthcdr (+ (interl$data-ins-len data-size)
                              *interl$select-num*)
                           inputs)))
    (and
     (booleanp full-in0)
     (booleanp full-in1)
     (booleanp empty-out-)
     (or (not full-in0) (bvp data0-in))
     (or (not full-in1) (bvp data1-in))
     (true-listp go-signals)
     (= (len go-signals) *interl$go-num*)
     (equal inputs
            (list* full-in0 full-in1 empty-out-
                   (append data0-in data1-in (cons select go-signals)))))))

(local
 (defthm interl$input-format=>q40-l0$input-format
   (implies (and (interl$input-format inputs data-size)
                 (interl$valid-st st data-size))
            (queue40-l$input-format
             (interl$q40-l0-inputs inputs st data-size)
             (nth *interl$q40-l0* st)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (queue40-l$input-format
                             queue40-l$in-act
                             queue40-l$out-act
                             queue40-l$data-in
                             arb-merge$act0
                             interl$input-format
                             interl$valid-st
                             interl$q40-l0-inputs
                             interl$arb-merge-inputs
                             interl$in0-act)
                            (nfix
                             link$st-format))))))

(local
 (defthm interl$input-format=>q40-l1$input-format
   (implies (and (interl$input-format inputs data-size)
                 (interl$valid-st st data-size))
            (queue40-l$input-format
             (interl$q40-l1-inputs inputs st data-size)
             (nth *interl$q40-l1* st)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (queue40-l$input-format
                             queue40-l$in-act
                             queue40-l$out-act
                             queue40-l$data-in
                             arb-merge$act1
                             interl$input-format
                             interl$valid-st
                             interl$q40-l1-inputs
                             interl$arb-merge-inputs
                             interl$in1-act)
                            (nfix
                             link$st-format))))))

(defthm booleanp-interl$in0-act
  (implies (and (interl$input-format inputs data-size)
                (interl$valid-st st data-size))
           (booleanp (interl$in0-act inputs st data-size)))
  :hints (("Goal" :in-theory (enable interl$input-format
                                     interl$valid-st
                                     interl$in0-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-interl$in1-act
  (implies (and (interl$input-format inputs data-size)
                (interl$valid-st st data-size))
           (booleanp (interl$in1-act inputs st data-size)))
  :hints (("Goal" :in-theory (enable interl$input-format
                                     interl$valid-st
                                     interl$in1-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-interl$out0-act
  (implies (and (interl$input-format inputs data-size)
                (interl$valid-st st data-size))
           (booleanp (interl$out-act0 inputs st data-size)))
  :hints (("Goal" :in-theory (enable arb-merge$act0
                                     interl$input-format
                                     interl$valid-st
                                     interl$arb-merge-inputs
                                     interl$out-act0
                                     interl$out-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-interl$out1-act
  (implies (and (interl$input-format inputs data-size)
                (interl$valid-st st data-size))
           (booleanp (interl$out-act1 inputs st data-size)))
  :hints (("Goal" :in-theory (enable arb-merge$act1
                                     interl$input-format
                                     interl$valid-st
                                     interl$arb-merge-inputs
                                     interl$out-act1
                                     interl$out-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-interl$out-act
  (implies (and (interl$input-format inputs data-size)
                (interl$valid-st st data-size))
           (booleanp (interl$out-act inputs st data-size)))
  :hints (("Goal" :in-theory (enable interl$out-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-interl$data-out
  (implies (and (interl$input-format inputs data-size)
                (interl$valid-st st data-size)
                (interl$out-act inputs st data-size))
           (bvp (interl$data-out inputs st data-size)))
  :hints (("Goal"
           :in-theory (enable arb-merge$act0
                              arb-merge$act1
                              arb-merge$data0-in
                              arb-merge$data1-in
                              arb-merge$data-out
                              interl$input-format
                              interl$valid-st
                              interl$out-act0
                              interl$out-act1
                              interl$out-act
                              interl$arb-merge-inputs
                              interl$data-out))))

(simulate-lemma interl)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction functions for INTERL

(defund interl$extract0 (st)
  (b* ((q40-l0 (nth *interl$q40-l0* st)))
    (queue40-l$extract q40-l0)))

(defund interl$extract1 (st)
  (b* ((q40-l1 (nth *interl$q40-l1* st)))
    (queue40-l$extract q40-l1)))

(defthm interl$extract0-not-empty
  (implies (and (interl$out-act0 inputs st data-size)
                (interl$valid-st st data-size))
           (< 0 (len (interl$extract0 st))))
  :hints (("Goal"
           :in-theory (e/d (arb-merge$act0
                            interl$arb-merge-inputs
                            interl$valid-st
                            interl$extract0
                            interl$out-act0)
                           ())))
  :rule-classes :linear)

(defthm interl$extract1-not-empty
  (implies (and (interl$out-act1 inputs st data-size)
                (interl$valid-st st data-size))
           (< 0 (len (interl$extract1 st))))
  :hints (("Goal"
           :in-theory (e/d (arb-merge$act1
                            interl$arb-merge-inputs
                            interl$valid-st
                            interl$extract1
                            interl$out-act1)
                           ())))
  :rule-classes :linear)

;; The extracted next-state functions for INTERL.  Note that these functions
;; avoid exploring the internal computation of INTERL.

(defund interl$extracted0-step (inputs st data-size)
  (b* ((data (interl$data0-in inputs data-size))
       (extracted-st (interl$extract0 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (interl$out-act0 inputs st data-size) t)
      (cond
       ((equal (interl$in0-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (interl$in0-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

(defund interl$extracted1-step (inputs st data-size)
  (b* ((data (interl$data1-in inputs data-size))
       (extracted-st (interl$extract1 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (interl$out-act1 inputs st data-size) t)
      (cond
       ((equal (interl$in1-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (interl$in1-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm interl$q40-l0-data-in-rewrite
     (equal (queue40-l$data-in
             (interl$q40-l0-inputs inputs st data-size)
             data-size)
            (interl$data0-in inputs data-size))
     :hints (("Goal"
              :in-theory (enable queue40-l$data-in
                                 interl$data0-in
                                 interl$q40-l0-inputs)))))

  (local
   (defthm interl$q40-l1-data-in-rewrite
     (equal (queue40-l$data-in
             (interl$q40-l1-inputs inputs st data-size)
             data-size)
            (interl$data1-in inputs data-size))
     :hints (("Goal"
              :in-theory (enable queue40-l$data-in
                                 interl$data1-in
                                 interl$q40-l1-inputs)))))

  (local
   (defthm interl$q40-l0-in-act-rewrite
     (equal (queue40-l$in-act (interl$q40-l0-inputs inputs st data-size))
            (interl$in0-act inputs st data-size))
     :hints (("Goal" :in-theory (enable queue40-l$in-act
                                        interl$in0-act
                                        interl$q40-l0-inputs)))))

  (local
   (defthm interl$q40-l0-out-act-rewrite
     (equal (queue40-l$out-act (interl$q40-l0-inputs inputs st data-size))
            (interl$out-act0 inputs st data-size))
     :hints (("Goal" :in-theory (enable queue40-l$out-act
                                        interl$out-act0
                                        interl$q40-l0-inputs)))))

  (local
   (defthm interl$q40-l1-in-act-rewrite
     (equal (queue40-l$in-act (interl$q40-l1-inputs inputs st data-size))
            (interl$in1-act inputs st data-size))
     :hints (("Goal" :in-theory (enable queue40-l$in-act
                                        interl$in1-act
                                        interl$q40-l1-inputs)))))

  (local
   (defthm interl$q40-l1-out-act-rewrite
     (equal (queue40-l$out-act (interl$q40-l1-inputs inputs st data-size))
            (interl$out-act1 inputs st data-size))
     :hints (("Goal" :in-theory (enable queue40-l$out-act
                                        interl$out-act1
                                        interl$q40-l1-inputs)))))

  (defthm interl$extracted-step-correct
    (b* ((next-st (interl$step inputs st data-size)))
      (implies (and (interl$input-format inputs data-size)
                    (interl$valid-st st data-size))
               (and (equal (interl$extract0 next-st)
                           (interl$extracted0-step inputs st data-size))
                    (equal (interl$extract1 next-st)
                           (interl$extracted1-step inputs st data-size)))))
    :hints (("Goal"
             :in-theory (e/d (queue40-l$extracted-step
                              queue40-l$extracted-step
                              interl$extracted0-step
                              interl$extracted1-step
                              interl$valid-st
                              interl$step
                              interl$extract0
                              interl$extract1)
                             (nthcdr)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that interl$valid-st is an invariant.

(defthm interl$valid-st-preserved
  (implies (and (interl$input-format inputs data-size)
                (interl$valid-st st data-size))
           (interl$valid-st (interl$step inputs st data-size)
                            data-size))
  :hints (("Goal"
           :in-theory (e/d (interl$valid-st
                            interl$step)
                           ()))))

(encapsulate
  ()

  (local
   (defthm interl$data-out-rewrite-1
     (implies (and (interl$valid-st st data-size)
                   (interl$out-act0 inputs st data-size))
              (equal (interl$data-out inputs st data-size)
                     (queue40-l$data-out (nth *interl$q40-l0* st))))
     :hints (("Goal"
              :in-theory (enable queue40-l$valid-st=>constraint
                                 arb-merge$act0
                                 arb-merge$act1
                                 arb-merge$data0-in
                                 arb-merge$data-out
                                 interl$valid-st
                                 interl$arb-merge-inputs
                                 interl$out-act0
                                 interl$data-out)))))

  (local
   (defthm interl$data-out-rewrite-2
     (implies (and (interl$input-format inputs data-size)
                   (interl$valid-st st data-size)
                   (interl$out-act1 inputs st data-size))
              (equal (interl$data-out inputs st data-size)
                     (queue40-l$data-out (nth *interl$q40-l1* st))))
     :hints (("Goal"
              :in-theory (enable queue40-l$valid-st=>constraint
                                 arb-merge$act0
                                 arb-merge$act1
                                 arb-merge$data1-in
                                 arb-merge$data-out
                                 interl$input-format
                                 interl$valid-st
                                 interl$arb-merge-inputs
                                 interl$out-act1
                                 interl$data-out)))))

  (local
   (defthm interl$out-act0-rewrite
     (equal (interl$out-act0 inputs st data-size)
            (queue40-l$out-act (interl$q40-l0-inputs inputs st data-size)))
     :hints (("Goal" :in-theory (enable queue40-l$out-act
                                        interl$out-act0
                                        interl$q40-l0-inputs)))))

  (local
   (defthm interl$out-act1-rewrite
     (equal (interl$out-act1 inputs st data-size)
            (queue40-l$out-act (interl$q40-l1-inputs inputs st data-size)))
     :hints (("Goal" :in-theory (enable queue40-l$out-act
                                        interl$out-act1
                                        interl$q40-l1-inputs)))))

  (defthm interl$extract0-lemma
    (implies (and (interl$input-format inputs data-size)
                  (interl$valid-st st data-size)
                  (interl$out-act0 inputs st data-size))
             (equal (list (interl$data-out inputs st data-size))
                    (nthcdr (1- (len (interl$extract0 st)))
                            (interl$extract0 st))))
    :hints (("Goal"
             :use interl$input-format=>q40-l0$input-format
             :in-theory (e/d (interl$valid-st
                              interl$extract0)
                             (interl$input-format=>q40-l0$input-format)))))

  (defthm interl$extract1-lemma
    (implies (and (interl$input-format inputs data-size)
                  (interl$valid-st st data-size)
                  (interl$out-act1 inputs st data-size))
             (equal (list (interl$data-out inputs st data-size))
                    (nthcdr (1- (len (interl$extract1 st)))
                            (interl$extract1 st))))
    :hints (("Goal"
             :use interl$input-format=>q40-l1$input-format
             :in-theory (e/d (interl$valid-st
                              interl$extract1)
                             (interl$input-format=>q40-l1$input-format)))))
  )

;; Extract the accepted input sequences

(seq-gen interl in0 in0-act 0
         (interl$data0-in inputs data-size))

(seq-gen interl in1 in1-act 1
         (interl$data1-in inputs data-size))

;; Extract the valid output sequence

(seq-gen interl out out-act 2
         (interl$data-out inputs st data-size)
         :netlist-data (nthcdr 3 outputs))

;; The multi-step input-output relationship

;; Let in0-seq and in1-seq represent two input sequences connected to Q40-L0
;; and Q40-L1, respectively.  We might expect the output sequence is any
;; interleaving of in0-seq and in1-seq.  More generally, our formalization also
;; takes into account that an initial state of INTERL may contain some valid
;; data, and there can be some valid data remaining in the final state after
;; executing INTERL an arbitrary number of steps.  We then prove that for any
;; interleaving x of two data sequences remaining in the final state, the
;; concatenation of x and the output sequence must be a member of (seq0 x
;; seq1); where seq0 is the concatenation of in0-seq and the valid data
;; sequence in Q40-L0 at the intial state, and seq1 is the concatenation of
;; in1-seq and the valid data sequence in Q40-L1 at the intial state.

(progn
  (defthm member-append-interleave-1-instance
    (implies (and (member (append a b) (interleave y z))
                  (equal y++x1 (append y x1))
                  (true-listp x1)
                  (true-listp z))
             (member (append a b x1)
                     (interleave y++x1 z)))
    :hints (("Goal"
             :use (:instance member-append-interleave-1
                             (x (append a b))))))

  (defthm member-append-interleave-2-instance
    (implies (and (member (append a b) (interleave y z))
                  (equal z++x1 (append z x1))
                  (true-listp x1)
                  (true-listp y))
             (member (append a b x1)
                     (interleave y z++x1)))
    :hints (("Goal"
             :use (:instance member-append-interleave-2
                             (x (append a b))))))

  (defthmd interl$dataflow-correct
    (b* ((extracted0-st (interl$extract0 st))
         (extracted1-st (interl$extract1 st))
         (final-st (interl$run inputs-seq st data-size n))
         (final-extracted0-st (interl$extract0 final-st))
         (final-extracted1-st (interl$extract1 final-st)))
      (implies
       (and (interl$input-format-n inputs-seq data-size n)
            (interl$valid-st st data-size)
            (member x (interleave final-extracted0-st final-extracted1-st)))
       (member
        (append x (interl$out-seq inputs-seq st data-size n))
        (interleave (append (interl$in0-seq inputs-seq st data-size n)
                            extracted0-st)
                    (append (interl$in1-seq inputs-seq st data-size n)
                            extracted1-st)))))
    :hints (("Goal" :in-theory (enable member-of-true-list-list-is-true-list
                                       interl$out-act
                                       interl$extracted0-step
                                       interl$extracted1-step))))

  (defthmd interl$functionally-correct
    (b* ((extracted0-st (interl$extract0 st))
         (extracted1-st (interl$extract1 st))
         (final-st (de-n (si 'interl data-size) inputs-seq st netlist n))
         (final-extracted0-st (interl$extract0 final-st))
         (final-extracted1-st (interl$extract1 final-st)))
      (implies
       (and (interl& netlist data-size)
            (interl$input-format-n inputs-seq data-size n)
            (interl$valid-st st data-size)
            (member x (interleave final-extracted0-st final-extracted1-st)))
       (member
        (append x (interl$out-seq-netlist
                   inputs-seq st netlist data-size n))
        (interleave (append (interl$in0-seq-netlist
                             inputs-seq st netlist data-size n)
                            extracted0-st)
                    (append (interl$in1-seq-netlist
                             inputs-seq st netlist data-size n)
                            extracted1-st)))))
    :hints (("Goal"
             :use interl$dataflow-correct
             :in-theory (enable interl$valid-st=>st-format
                                interl$de-n))))
  )

