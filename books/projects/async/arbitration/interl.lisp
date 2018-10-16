;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2018

(in-package "ADE")

(include-book "arb-merge")
(include-book "../fifo/queue20-l")

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
;; circuits consist of two 20-link queues connected to the two input ports of
;; an arbitrated merge.

(defconst *interl$select-num* *arb-merge$select-num*)
(defconst *interl$prim-go-num* 2)
(defconst *interl$go-num* (+ *interl$prim-go-num*
                             (* 2 *queue20-l$go-num*)
                             *arb-merge$go-num*))
(defconst *interl$st-len* 3)

(defun interl$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 3 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun interl$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (interl$data-ins-len data-width)
     *interl$select-num*
     *interl$go-num*))

;; DE module generator of INTERL

(module-generator
 interl* (data-width)
 (si 'interl data-width)
 (list* 'full-in0 'full-in1 'empty-out-
        (append (sis 'data0-in 0 data-width)
                (sis 'data1-in 0 data-width)
                (cons 'select (sis 'go 0 *interl$go-num*))))
 (list* 'in0-act 'in1-act 'out-act
        (sis 'data-out 0 data-width))
 '(q20-l0 q20-l1 arb-merge)
 (list
  ;; LINKS
  ;; 20-link queue Q20-L0
  (list 'q20-l0
        (list* 'q20-l0-ready-in- 'q20-l0-ready-out
               (sis 'q20-l0-data-out 0 data-width))
        (si 'queue20-l data-width)
        (list* 'in0-act 'out-act0
               (append (sis 'q20-l0-data-in 0 data-width)
                       (sis 'go
                            *interl$prim-go-num*
                            *queue20-l$go-num*))))

  ;; 20-link queue Q20-L1
  (list 'q20-l1
        (list* 'q20-l1-ready-in- 'q20-l1-ready-out
               (sis 'q20-l1-data-out 0 data-width))
        (si 'queue20-l data-width)
        (list* 'in1-act 'out-act1
               (append (sis 'q20-l1-data-in 0 data-width)
                       (sis 'go
                            (+ *interl$prim-go-num*
                               *queue20-l$go-num*)
                            *queue20-l$go-num*))))

  ;; JOINTS
  ;; In0
  (list 'in0-cntl
        '(in0-act)
        'joint-cntl
        (list 'full-in0 'q20-l0-ready-in- (si 'go 0)))
  (list 'in0-op
        (sis 'q20-l0-data-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'data0-in 0 data-width))

  ;; In1
  (list 'in1-cntl
        '(in1-act)
        'joint-cntl
        (list 'full-in1 'q20-l1-ready-in- (si 'go 1)))
  (list 'in1-op
        (sis 'q20-l1-data-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'data1-in 0 data-width))

  ;; Arb-merge
  (list 'arb-merge
        (list* 'out-act 'out-act0 'out-act1
               (sis 'data-out 0 data-width))
        (si 'arb-merge data-width)
        (list* 'q20-l0-ready-out 'q20-l1-ready-out 'empty-out-
               (append (sis 'q20-l0-data-out 0 data-width)
                       (sis 'q20-l1-data-out 0 data-width)
                       (cons 'select
                             (sis 'go
                                  (+ *interl$prim-go-num*
                                     (* 2 *queue20-l$go-num*))
                                  *arb-merge$go-num*))))))

 :guard (natp data-width))

(make-event
 `(progn
    ,@(state-accessors-gen 'interl
                           '(q20-l0 q20-l1 arb-merge)
                           0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; INTERL.

(defun interl$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (interl* data-width)
        (union$ (queue20-l$netlist data-width)
                (arb-merge$netlist data-width)
                :test 'equal)))

;; Recognizer for INTERL

(defund interl& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (and (equal (assoc (si 'interl data-width) netlist)
              (interl* data-width))
       (b* ((netlist (delete-to-eq (si 'interl data-width) netlist)))
         (and (joint-cntl& netlist)
              (v-buf& netlist data-width)
              (queue20-l& netlist data-width)
              (arb-merge& netlist data-width)))))

;; Sanity check

(local
 (defthmd check-interl$netlist-64
   (and (net-syntax-okp (interl$netlist 64))
        (net-arity-okp (interl$netlist 64))
        (interl& (interl$netlist 64) 64))))

;; Constraints on the state of INTERL

(defund interl$st-format (st data-width)
  (b* ((q20-l0 (get-field *interl$q20-l0* st))
       (q20-l1 (get-field *interl$q20-l1* st))
       (arb-merge (get-field *interl$arb-merge* st)))
    (and (< 0 data-width)
         (queue20-l$st-format q20-l0 data-width)
         (queue20-l$st-format q20-l1 data-width)
         (arb-merge$st-format arb-merge))))

(defthm interl$st-format=>data-width-constraint
  (implies (interl$st-format st data-width)
           (posp data-width))
  :hints (("Goal" :in-theory (enable interl$st-format)))
  :rule-classes :forward-chaining)

(defund interl$valid-st (st data-width)
  (b* ((q20-l0 (get-field *interl$q20-l0* st))
       (q20-l1 (get-field *interl$q20-l1* st))
       (arb-merge (get-field *interl$arb-merge* st)))
    (and (< 0 data-width)
         (queue20-l$valid-st q20-l0 data-width)
         (queue20-l$valid-st q20-l1 data-width)
         (arb-merge$valid-st arb-merge))))

(defthmd interl$valid-st=>data-width-constraint
  (implies (interl$valid-st st data-width)
           (posp data-width))
  :hints (("Goal" :in-theory (enable queue20-l$valid-st=>data-width-constraint
                                     interl$valid-st)))
  :rule-classes :forward-chaining)

(defthmd interl$valid-st=>st-format
  (implies (interl$valid-st st data-width)
           (interl$st-format st data-width))
  :hints (("Goal" :in-theory (e/d (queue20-l$valid-st=>st-format
                                   arb-merge$valid-st=>st-format
                                   interl$st-format
                                   interl$valid-st)
                                  ()))))

;; Extract the input and output signals for INTERL

(progn
  ;; Extract the 1st input data item

  (defun interl$data0-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 3 inputs)))

  (defthm len-interl$data0-in
    (equal (len (interl$data0-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable interl$data0-in))

  ;; Extract the 2nd input data item

  (defun interl$data1-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (b* ((width (mbe :logic (nfix data-width)
                     :exec  data-width)))
      (take width
            (nthcdr (+ 3 width) inputs))))

  (defthm len-interl$data1-in
    (equal (len (interl$data1-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable interl$data1-in))

  ;; Extract the "in0-act" signal

  (defund interl$in0-act (inputs st data-width)
    (b* ((full-in0   (nth 0 inputs))
         (go-signals (nthcdr (+ (interl$data-ins-len data-width)
                                *interl$select-num*)
                             inputs))

         (go-in0 (nth 0 go-signals))

         (q20-l0 (get-field *interl$q20-l0* st))
         (q20-l0-ready-in- (queue20-l$ready-in- q20-l0)))

      (joint-act full-in0 q20-l0-ready-in- go-in0)))

  (defthm interl$in0-act-inactive
    (implies (not (nth 0 inputs))
             (not (interl$in0-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable interl$in0-act))))

  ;; Extract the "in1-act" signal

  (defund interl$in1-act (inputs st data-width)
    (b* ((full-in1   (nth 1 inputs))
         (go-signals (nthcdr (+ (interl$data-ins-len data-width)
                                *interl$select-num*)
                             inputs))

         (go-in1 (nth 1 go-signals))

         (q20-l1 (get-field *interl$q20-l1* st))
         (q20-l1-ready-in- (queue20-l$ready-in- q20-l1)))

      (joint-act full-in1 q20-l1-ready-in- go-in1)))

  (defthm interl$in1-act-inactive
    (implies (not (nth 1 inputs))
             (not (interl$in1-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable interl$in1-act))))

  ;; Extract the inputs for joint ARB-MERGE

  (defund interl$arb-merge-inputs (inputs st data-width)
    (b* ((empty-out- (nth 2 inputs))
         (select     (nth (interl$data-ins-len data-width) inputs))
         (go-signals (nthcdr (+ (interl$data-ins-len data-width)
                                *interl$select-num*)
                             inputs))

         (arb-merge-go-signals (take *arb-merge$go-num*
                                     (nthcdr (+ *interl$prim-go-num*
                                                *queue20-l$go-num*
                                                *queue20-l$go-num*)
                                             go-signals)))

         (q20-l0 (get-field *interl$q20-l0* st))
         (q20-l1 (get-field *interl$q20-l1* st))

         (q20-l0-ready-out (queue20-l$ready-out q20-l0))
         (q20-l0-data-out (queue20-l$data-out q20-l0))
         (q20-l1-ready-out (queue20-l$ready-out q20-l1))
         (q20-l1-data-out (queue20-l$data-out q20-l1)))
      (list* q20-l0-ready-out q20-l1-ready-out empty-out-
             (append q20-l0-data-out q20-l1-data-out
                     (cons select arb-merge-go-signals)))))

  ;; Extract the "out-act0" signal

  (defund interl$out-act0 (inputs st data-width)
    (b* ((arb-merge-inputs (interl$arb-merge-inputs inputs st data-width))
         (arb-merge (get-field *interl$arb-merge* st)))
      (arb-merge$act0 arb-merge-inputs arb-merge data-width)))

  (defthm interl$out-act0-inactive
    (implies (equal (nth 2 inputs) t)
             (not (interl$out-act0 inputs st data-width)))
    :hints (("Goal" :in-theory (enable interl$arb-merge-inputs
                                       interl$out-act0))))

  ;; Extract the "out-act1" signal

  (defund interl$out-act1 (inputs st data-width)
    (b* ((arb-merge-inputs (interl$arb-merge-inputs inputs st data-width))
         (arb-merge (get-field *interl$arb-merge* st)))
      (arb-merge$act1 arb-merge-inputs arb-merge data-width)))

  (defthm interl$out-act1-inactive
    (implies (equal (nth 2 inputs) t)
             (not (interl$out-act1 inputs st data-width)))
    :hints (("Goal" :in-theory (enable interl$arb-merge-inputs
                                       interl$out-act1))))

  (defthm interl$out-act-mutually-exclusive
    (implies (and (interl$valid-st st data-width)
                  (interl$out-act0 inputs st data-width))
             (not (interl$out-act1 inputs st data-width)))
    :hints (("Goal" :in-theory (enable interl$valid-st
                                       interl$arb-merge-inputs
                                       interl$out-act0
                                       interl$out-act1))))

  ;; Extract the "out-act" signal

  (defund interl$out-act (inputs st data-width)
    (f-or (interl$out-act0 inputs st data-width)
          (interl$out-act1 inputs st data-width)))

  (defthm interl$out-act-inactive
    (implies (equal (nth 2 inputs) t)
             (not (interl$out-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable interl$out-act))))

  ;; Extract the inputs for link Q20-L0

  (defund interl$q20-l0-inputs (inputs st data-width)
    (b* ((in0-act (interl$in0-act inputs st data-width))
         (data0-in (interl$data0-in inputs data-width))
         (go-signals (nthcdr (+ (interl$data-ins-len data-width)
                                *interl$select-num*)
                             inputs))

         (q20-l0-go-signals (take *queue20-l$go-num*
                                  (nthcdr *interl$prim-go-num*
                                          go-signals)))

         (arb-merge (get-field *interl$arb-merge* st))

         (arb-merge-inputs (interl$arb-merge-inputs inputs st data-width))
         (out-act0 (arb-merge$act0 arb-merge-inputs arb-merge data-width)))

      (list* in0-act out-act0
             (append data0-in q20-l0-go-signals))))

  ;; Extract the inputs for link Q20-L1

  (defund interl$q20-l1-inputs (inputs st data-width)
    (b* ((in1-act (interl$in1-act inputs st data-width))
         (data1-in (interl$data1-in inputs data-width))
         (go-signals (nthcdr (+ (interl$data-ins-len data-width)
                                *interl$select-num*)
                             inputs))

         (q20-l1-go-signals (take *queue20-l$go-num*
                                  (nthcdr (+ *interl$prim-go-num*
                                             *queue20-l$go-num*)
                                          go-signals)))

         (arb-merge (get-field *interl$arb-merge* st))

         (arb-merge-inputs (interl$arb-merge-inputs inputs st data-width))
         (out-act1 (arb-merge$act1 arb-merge-inputs arb-merge data-width)))

      (list* in1-act out-act1
             (append data1-in q20-l1-go-signals))))

  ;; Extract the output data

  (defund interl$data-out (inputs st data-width)
    (b* ((arb-merge-inputs (interl$arb-merge-inputs inputs st data-width))
         (arb-merge (get-field *interl$arb-merge* st)))
      (arb-merge$data-out arb-merge-inputs arb-merge data-width)))

  (defthm len-interl$data-out-1
    (implies (interl$st-format st data-width)
             (equal (len (interl$data-out inputs st data-width))
                    data-width))
    :hints (("Goal" :in-theory (enable interl$st-format
                                       interl$data-out))))

  (defthm len-interl$data-out-2
    (implies (interl$valid-st st data-width)
             (equal (len (interl$data-out inputs st data-width))
                    data-width))
    :hints (("Goal" :in-theory (enable queue20-l$valid-st=>data-width-constraint
                                       interl$valid-st
                                       interl$data-out))))

  (defun interl$outputs (inputs st data-width)
    (list* (interl$in0-act inputs st data-width)
           (interl$in1-act inputs st data-width)
           (interl$out-act inputs st data-width)
           (interl$data-out inputs st data-width)))
  )

;; Prove that INTERL is not a DE primitive.

(not-primp-lemma interl)

;; The value lemma for INTERL

(defthm interl$value
  (b* ((inputs (list* full-in0 full-in1 empty-out-
                      (append data0-in data1-in
                              (cons select go-signals)))))
    (implies (and (interl& netlist data-width)
                  (true-listp data0-in)
                  (equal (len data0-in) data-width)
                  (true-listp data1-in)
                  (equal (len data1-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *interl$go-num*)
                  (interl$st-format st data-width))
             (equal (se (si 'interl data-width) inputs st netlist)
                    (interl$outputs inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'interl data-width) inputs st netlist))
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

(defun interl$step (inputs st data-width)
  (b* ((q20-l0    (get-field *interl$q20-l0* st))
       (q20-l1    (get-field *interl$q20-l1* st))
       (arb-merge (get-field *interl$arb-merge* st))

       (q20-l0-inputs (interl$q20-l0-inputs inputs st data-width))
       (q20-l1-inputs (interl$q20-l1-inputs inputs st data-width))
       (arb-merge-inputs (interl$arb-merge-inputs inputs st data-width)))
    (list
      ;; Q20-L0
     (queue20-l$step q20-l0-inputs q20-l0 data-width)
     ;; Q20-L1
     (queue20-l$step q20-l1-inputs q20-l1 data-width)
     ;; Joint arb-merge
     (arb-merge$step arb-merge-inputs arb-merge data-width))))

(defthm len-of-interl$step
  (equal (len (interl$step inputs st data-width))
         *interl$st-len*))

;; The state lemma for INTERL

(defthm interl$state
  (b* ((inputs (list* full-in0 full-in1 empty-out-
                      (append data0-in data1-in
                              (cons select go-signals)))))
    (implies (and (interl& netlist data-width)
                  (true-listp data0-in)
                  (equal (len data0-in) data-width)
                  (true-listp data1-in)
                  (equal (len data1-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *interl$go-num*)
                  (interl$st-format st data-width))
             (equal (de (si 'interl data-width) inputs st netlist)
                    (interl$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'interl data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            interl&
                            interl*$destructure
                            interl$st-format
                            interl$data0-in
                            interl$data1-in
                            interl$q20-l0-inputs
                            interl$q20-l1-inputs
                            interl$arb-merge-inputs
                            interl$in0-act
                            interl$in1-act)
                           (de-module-disabled-rules)))))

(in-theory (disable interl$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund interl$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in0   (nth 0 inputs))
       (full-in1   (nth 1 inputs))
       (empty-out- (nth 2 inputs))
       (data0-in   (interl$data0-in inputs data-width))
       (data1-in   (interl$data1-in inputs data-width))
       (select     (nth (interl$data-ins-len data-width) inputs))
       (go-signals (nthcdr (+ (interl$data-ins-len data-width)
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

(local (in-theory (enable booleanp-car-of-bv)))

(local
 (defthm booleanp-cadr-of-bv
   (implies (bvp x)
            (booleanp (cadr x)))
   :hints (("Goal" :in-theory (enable bvp)))
   :rule-classes :type-prescription))

(local
 (defthm interl$input-format=>q20-l0$input-format
   (implies (and (interl$input-format inputs data-width)
                 (interl$valid-st st data-width))
            (queue20-l$input-format
             (interl$q20-l0-inputs inputs st data-width)
             (nth *interl$q20-l0* st)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             f-and4
                             f-and5
                             queue20-l$input-format
                             queue20-l$in-act
                             queue20-l$out-act
                             queue20-l$data-in
                             arb-merge$valid-st
                             arb-merge$act0
                             interl$input-format
                             interl$valid-st
                             interl$q20-l0-inputs
                             interl$arb-merge-inputs
                             interl$in0-act)
                            (nfix
                             link$st-format))))))

(local
 (defthm interl$input-format=>q20-l1$input-format
   (implies (and (interl$input-format inputs data-width)
                 (interl$valid-st st data-width))
            (queue20-l$input-format
             (interl$q20-l1-inputs inputs st data-width)
             (nth *interl$q20-l1* st)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             f-and4
                             f-and5
                             queue20-l$input-format
                             queue20-l$in-act
                             queue20-l$out-act
                             queue20-l$data-in
                             arb-merge$valid-st
                             arb-merge$act1
                             interl$input-format
                             interl$valid-st
                             interl$q20-l1-inputs
                             interl$arb-merge-inputs
                             interl$in1-act)
                            (nfix
                             link$st-format))))))

(local
 (defthm interl$input-format=>arb-merge$input-format
   (implies (and (interl$input-format inputs data-width)
                 (interl$valid-st st data-width))
            (arb-merge$input-format
             (interl$arb-merge-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (open-nth
                             queue20-l$valid-st=>data-width-constraint
                             arb-merge$input-format
                             arb-merge$data0-in
                             arb-merge$data1-in
                             interl$input-format
                             interl$valid-st
                             interl$arb-merge-inputs)
                            ())))))

(defthm booleanp-interl$in0-act
  (implies (and (interl$input-format inputs data-width)
                (interl$valid-st st data-width))
           (booleanp (interl$in0-act inputs st data-width)))
  :hints (("Goal" :in-theory (enable interl$input-format
                                     interl$valid-st
                                     interl$in0-act)))
  :rule-classes :type-prescription)

(defthm booleanp-interl$in1-act
  (implies (and (interl$input-format inputs data-width)
                (interl$valid-st st data-width))
           (booleanp (interl$in1-act inputs st data-width)))
  :hints (("Goal" :in-theory (enable interl$input-format
                                     interl$valid-st
                                     interl$in1-act)))
  :rule-classes :type-prescription)

(defthm booleanp-interl$out0-act
  (implies (and (interl$input-format inputs data-width)
                (interl$valid-st st data-width))
           (booleanp (interl$out-act0 inputs st data-width)))
  :hints (("Goal" :in-theory (enable f-and4
                                     f-and5
                                     arb-merge$valid-st
                                     arb-merge$act0
                                     interl$input-format
                                     interl$valid-st
                                     interl$arb-merge-inputs
                                     interl$out-act0
                                     interl$out-act)))
  :rule-classes :type-prescription)

(defthm booleanp-interl$out1-act
  (implies (and (interl$input-format inputs data-width)
                (interl$valid-st st data-width))
           (booleanp (interl$out-act1 inputs st data-width)))
  :hints (("Goal" :in-theory (enable f-and4
                                     f-and5
                                     arb-merge$valid-st
                                     arb-merge$act1
                                     interl$input-format
                                     interl$valid-st
                                     interl$arb-merge-inputs
                                     interl$out-act1
                                     interl$out-act)))
  :rule-classes :type-prescription)

(defthm booleanp-interl$out-act
  (implies (and (interl$input-format inputs data-width)
                (interl$valid-st st data-width))
           (booleanp (interl$out-act inputs st data-width)))
  :hints (("Goal" :in-theory (enable interl$out-act)))
  :rule-classes :type-prescription)

(defthm bvp-interl$data-out
  (implies (and (interl$input-format inputs data-width)
                (interl$valid-st st data-width)
                (interl$out-act inputs st data-width))
           (bvp (interl$data-out inputs st data-width)))
  :hints (("Goal"
           :in-theory (enable f-and4
                              f-and5
                              arb-merge$valid-st
                              arb-merge$act0
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
  (b* ((q20-l0 (get-field *interl$q20-l0* st)))
    (queue20-l$extract q20-l0)))

(defund interl$extract1 (st)
  (b* ((q20-l1 (get-field *interl$q20-l1* st)))
    (queue20-l$extract q20-l1)))

(defthm interl$extract0-not-empty
  (implies (and (interl$out-act0 inputs st data-width)
                (interl$valid-st st data-width))
           (< 0 (len (interl$extract0 st))))
  :hints (("Goal"
           :in-theory (e/d (f-and
                            f-and4
                            f-and5
                            3v-fix
                            arb-merge$valid-st
                            arb-merge$act0
                            interl$arb-merge-inputs
                            interl$valid-st
                            interl$extract0
                            interl$out-act0)
                           ())))
  :rule-classes :linear)

(defthm interl$extract1-not-empty
  (implies (and (interl$out-act1 inputs st data-width)
                (interl$valid-st st data-width))
           (< 0 (len (interl$extract1 st))))
  :hints (("Goal"
           :in-theory (e/d (f-and
                            f-and4
                            f-and5
                            3v-fix
                            arb-merge$valid-st
                            arb-merge$act1
                            interl$arb-merge-inputs
                            interl$valid-st
                            interl$extract1
                            interl$out-act1)
                           ())))
  :rule-classes :linear)

;; The extracted next-state functions for INTERL.  Note that these functions
;; avoid exploring the internal computation of INTERL.

(defund interl$extracted0-step (inputs st data-width)
  (b* ((data (interl$data0-in inputs data-width))
       (extracted-st (interl$extract0 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (interl$out-act0 inputs st data-width) t)
      (cond
       ((equal (interl$in0-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (interl$in0-act inputs st data-width) t)
          (cons data extracted-st))
         (t extracted-st))))))

(defund interl$extracted1-step (inputs st data-width)
  (b* ((data (interl$data1-in inputs data-width))
       (extracted-st (interl$extract1 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (interl$out-act1 inputs st data-width) t)
      (cond
       ((equal (interl$in1-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (interl$in1-act inputs st data-width) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm interl$q20-l0-data-in-rewrite
     (equal (queue20-l$data-in
             (interl$q20-l0-inputs inputs st data-width)
             data-width)
            (interl$data0-in inputs data-width))
     :hints (("Goal"
              :in-theory (enable queue20-l$data-in
                                 interl$data0-in
                                 interl$q20-l0-inputs)))))

  (local
   (defthm interl$q20-l1-data-in-rewrite
     (equal (queue20-l$data-in
             (interl$q20-l1-inputs inputs st data-width)
             data-width)
            (interl$data1-in inputs data-width))
     :hints (("Goal"
              :in-theory (enable queue20-l$data-in
                                 interl$data1-in
                                 interl$q20-l1-inputs)))))

  (local
   (defthm interl$q20-l0-in-act-rewrite
     (equal (queue20-l$in-act (interl$q20-l0-inputs inputs st data-width))
            (interl$in0-act inputs st data-width))
     :hints (("Goal" :in-theory (enable queue20-l$in-act
                                        interl$in0-act
                                        interl$q20-l0-inputs)))))

  (local
   (defthm interl$q20-l0-out-act-rewrite
     (equal (queue20-l$out-act (interl$q20-l0-inputs inputs st data-width))
            (interl$out-act0 inputs st data-width))
     :hints (("Goal" :in-theory (enable queue20-l$out-act
                                        interl$out-act0
                                        interl$q20-l0-inputs)))))

  (local
   (defthm interl$q20-l1-in-act-rewrite
     (equal (queue20-l$in-act (interl$q20-l1-inputs inputs st data-width))
            (interl$in1-act inputs st data-width))
     :hints (("Goal" :in-theory (enable queue20-l$in-act
                                        interl$in1-act
                                        interl$q20-l1-inputs)))))

  (local
   (defthm interl$q20-l1-out-act-rewrite
     (equal (queue20-l$out-act (interl$q20-l1-inputs inputs st data-width))
            (interl$out-act1 inputs st data-width))
     :hints (("Goal" :in-theory (enable queue20-l$out-act
                                        interl$out-act1
                                        interl$q20-l1-inputs)))))

  (defthm interl$extracted-step-correct
    (b* ((next-st (interl$step inputs st data-width)))
      (implies (and (interl$input-format inputs data-width)
                    (interl$valid-st st data-width))
               (and (equal (interl$extract0 next-st)
                           (interl$extracted0-step inputs st data-width))
                    (equal (interl$extract1 next-st)
                           (interl$extracted1-step inputs st data-width)))))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              queue20-l$extracted-step
                              queue20-l$extracted-step
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
  (implies (and (interl$input-format inputs data-width)
                (interl$valid-st st data-width))
           (interl$valid-st (interl$step inputs st data-width)
                            data-width))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            interl$valid-st
                            interl$step)
                           ()))))

(encapsulate
  ()

  (local
   (defthm interl$data-out-rewrite-1
     (implies (and (interl$valid-st st data-width)
                   (interl$out-act0 inputs st data-width))
              (equal (interl$data-out inputs st data-width)
                     (queue20-l$data-out (nth *interl$q20-l0* st))))
     :hints (("Goal"
              :in-theory (enable get-field
                                 f-and4
                                 f-and5
                                 queue20-l$valid-st=>data-width-constraint
                                 arb-merge$valid-st
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
     (implies (and (interl$input-format inputs data-width)
                   (interl$valid-st st data-width)
                   (interl$out-act1 inputs st data-width))
              (equal (interl$data-out inputs st data-width)
                     (queue20-l$data-out (nth *interl$q20-l1* st))))
     :hints (("Goal"
              :in-theory (enable get-field
                                 f-and4
                                 f-and5
                                 queue20-l$valid-st=>data-width-constraint
                                 arb-merge$valid-st
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
     (equal (interl$out-act0 inputs st data-width)
            (queue20-l$out-act (interl$q20-l0-inputs inputs st data-width)))
     :hints (("Goal" :in-theory (enable queue20-l$out-act
                                        interl$out-act0
                                        interl$q20-l0-inputs)))))

  (local
   (defthm interl$out-act1-rewrite
     (equal (interl$out-act1 inputs st data-width)
            (queue20-l$out-act (interl$q20-l1-inputs inputs st data-width)))
     :hints (("Goal" :in-theory (enable queue20-l$out-act
                                        interl$out-act1
                                        interl$q20-l1-inputs)))))

  (defthm interl$extract0-lemma
    (implies (and (interl$input-format inputs data-width)
                  (interl$valid-st st data-width)
                  (interl$out-act0 inputs st data-width))
             (equal (list (interl$data-out inputs st data-width))
                    (nthcdr (1- (len (interl$extract0 st)))
                            (interl$extract0 st))))
    :hints (("Goal"
             :use interl$input-format=>q20-l0$input-format
             :in-theory (e/d (get-field
                              interl$valid-st
                              interl$extract0)
                             (interl$input-format=>q20-l0$input-format)))))

  (defthm interl$extract1-lemma
    (implies (and (interl$input-format inputs data-width)
                  (interl$valid-st st data-width)
                  (interl$out-act1 inputs st data-width))
             (equal (list (interl$data-out inputs st data-width))
                    (nthcdr (1- (len (interl$extract1 st)))
                            (interl$extract1 st))))
    :hints (("Goal"
             :use interl$input-format=>q20-l1$input-format
             :in-theory (e/d (get-field
                              interl$valid-st
                              interl$extract1)
                             (interl$input-format=>q20-l1$input-format)))))
  )

;; Extract the accepted input sequences

(seq-gen interl in0 in0-act 0
         (interl$data0-in inputs data-width))

(seq-gen interl in1 in1-act 1
         (interl$data1-in inputs data-width))

;; Extract the valid output sequence

(seq-gen interl out out-act 2
         (interl$data-out inputs st data-width)
         :netlist-data (nthcdr 3 outputs))

;; The multi-step input-output relationship

;; Let in0-seq and in1-seq represent two input sequences connected to Q20-L0
;; and Q20-L1, respectively.  We might expect the output sequence is any
;; interleaving of in0-seq and in1-seq.  More generally, our formalization also
;; takes into account that an initial state of INTERL may contain some valid
;; data, and there can be some valid data remaining in the final state after
;; executing INTERL an arbitrary number of steps.  We then prove that for any
;; interleaving x of two data sequences remaining in the final state, the
;; concatenation of x and the output sequence must be a member of (seq0 x
;; seq1); where seq0 is the concatenation of in0-seq and the valid data
;; sequence in Q20-L0 at the intial state, and seq1 is the concatenation of
;; in1-seq and the valid data sequence in Q20-L1 at the intial state.

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
         (final-st (interl$run inputs-seq st data-width n))
         (final-extracted0-st (interl$extract0 final-st))
         (final-extracted1-st (interl$extract1 final-st)))
      (implies
       (and (interl$input-format-n inputs-seq data-width n)
            (interl$valid-st st data-width)
            (member x (interleave final-extracted0-st final-extracted1-st)))
       (member
        (append x (interl$out-seq inputs-seq st data-width n))
        (interleave (append (interl$in0-seq inputs-seq st data-width n)
                            extracted0-st)
                    (append (interl$in1-seq inputs-seq st data-width n)
                            extracted1-st)))))
    :hints (("Goal" :in-theory (enable member-of-true-list-list-is-true-list
                                       interl$out-act
                                       interl$extracted0-step
                                       interl$extracted1-step))))

  (defthmd interl$functionally-correct
    (b* ((extracted0-st (interl$extract0 st))
         (extracted1-st (interl$extract1 st))
         (final-st (de-n (si 'interl data-width) inputs-seq st netlist n))
         (final-extracted0-st (interl$extract0 final-st))
         (final-extracted1-st (interl$extract1 final-st)))
      (implies
       (and (interl& netlist data-width)
            (interl$input-format-n inputs-seq data-width n)
            (interl$valid-st st data-width)
            (member x (interleave final-extracted0-st final-extracted1-st)))
       (member
        (append x (interl$netlist-out-seq
                   inputs-seq st netlist data-width n))
        (interleave (append (interl$netlist-in0-seq
                             inputs-seq st netlist data-width n)
                            extracted0-st)
                    (append (interl$netlist-in1-seq
                             inputs-seq st netlist data-width n)
                            extracted1-st)))))
    :hints (("Goal"
             :use interl$dataflow-correct
             :in-theory (enable interl$valid-st=>st-format
                                interl$de-n))))
  )

