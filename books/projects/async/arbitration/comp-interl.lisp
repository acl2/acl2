;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "interl2")
(include-book "interl-ll")

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "std/lists/sets" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of COMP-INTERL2
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of COMP-INTERL2
;;
;; Construct a DE module generator for circuits performing
;; first-come-first-served arbitrated merges.  Prove the value and state lemmas
;; for this module generator.

;; ->|
;;   |INTERL0 ->|
;; ->|          |
;;              |INTERL-LL ->
;; ->|          |
;;   |INTERL1 ->|
;; ->|

(defconst *comp-interl2$select-num* (+ (* 2 *interl$select-num*)
                                       *interl-ll$select-num*))
(defconst *comp-interl2$go-num* (+ (* 2 *interl$go-num*)
                                   *interl-ll$go-num*))

(defun comp-interl2$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 5 (* 4 (mbe :logic (nfix data-size)
                 :exec  data-size))))

(defun comp-interl2$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (comp-interl2$data-ins-len data-size)
     *comp-interl2$select-num*
     *comp-interl2$go-num*))

;; DE module generator of COMP-INTERL2

(module-generator
 comp-interl2* (data-size)
 (si 'comp-interl2 data-size)
 (list* 'full-in0 'full-in1 'full-in2 'full-in3 'empty-out-
        (append (sis 'data0-in 0 data-size)
                (sis 'data1-in 0 data-size)
                (sis 'data2-in 0 data-size)
                (sis 'data3-in 0 data-size)
                (sis 'select 0 *comp-interl2$select-num*)
                (sis 'go 0 *comp-interl2$go-num*)))
 (list* 'in0-act 'in1-act 'in2-act 'in3-act 'out-act
        (sis 'data-out 0 data-size))
 '(interl0 interl1 interl-ll)
 (list
  ;; LEFT HALF-LINK
  ;; INTERL-LL
  (list 'interl-ll
        (list* 'interl-ll-ready-in0- 'interl-ll-ready-in1- 'out-act
               (sis 'data-out 0 data-size))
        (si 'interl-ll data-size)
        (list* 'interl0-out-act 'interl1-out-act 'empty-out-
               (append (sis 'interl0-data-out 0 data-size)
                       (sis 'interl1-data-out 0 data-size)
                       (cons (si 'select (* 2 *interl$select-num*))
                             (sis 'go (* 2 *interl$go-num*)
                                  *interl-ll$go-num*)))))

  ;; JOINTS
  ;; INTERL0
  (list 'interl0
        (list* 'in0-act 'in1-act 'interl0-out-act
               (sis 'interl0-data-out 0 data-size))
        (si 'interl data-size)
        (list* 'full-in0 'full-in1 'interl-ll-ready-in0-
               (append (sis 'data0-in 0 data-size)
                       (sis 'data1-in 0 data-size)
                       (cons (si 'select 0)
                             (sis 'go 0 *interl$go-num*)))))

  ;; INTERL1
  (list 'interl1
        (list* 'in2-act 'in3-act 'interl1-out-act
               (sis 'interl1-data-out 0 data-size))
        (si 'interl data-size)
        (list* 'full-in2 'full-in3 'interl-ll-ready-in1-
               (append (sis 'data2-in 0 data-size)
                       (sis 'data3-in 0 data-size)
                       (cons (si 'select *interl$select-num*)
                             (sis 'go *interl$go-num* *interl$go-num*))))))

 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'comp-interl2 '(interl0 interl1 interl-ll) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; COMP-INTERL2.

(defund comp-interl2$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (comp-interl2* data-size)
        (union$ (interl$netlist data-size)
                (interl-ll$netlist data-size)
                :test 'equal)))

;; Recognizer for COMP-INTERL2

(defund comp-interl2& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'comp-interl2 data-size) netlist)))
    (and (equal (assoc (si 'comp-interl2 data-size) netlist)
                (comp-interl2* data-size))
         (interl& subnetlist data-size)
         (interl-ll& subnetlist data-size))))

;; Sanity check

(local
 (defthmd check-comp-interl2$netlist-64
   (and (net-syntax-okp (comp-interl2$netlist 64))
        (net-arity-okp (comp-interl2$netlist 64))
        (comp-interl2& (comp-interl2$netlist 64) 64))))

;; Constraints on the state of COMP-INTERL2

(defund comp-interl2$st-format (st data-size)
  (b* ((interl0 (nth *comp-interl2$interl0* st))
       (interl1 (nth *comp-interl2$interl1* st))
       (interl-ll (nth *comp-interl2$interl-ll* st)))
    (and (< 0 data-size)
         (interl$st-format interl0 data-size)
         (interl$st-format interl1 data-size)
         (interl-ll$st-format interl-ll data-size))))

(defthm comp-interl2$st-format=>constraint
  (implies (comp-interl2$st-format st data-size)
           (posp data-size))
  :hints (("Goal" :in-theory (enable comp-interl2$st-format)))
  :rule-classes :forward-chaining)

(defund comp-interl2$valid-st (st data-size)
  (b* ((interl0 (nth *comp-interl2$interl0* st))
       (interl1 (nth *comp-interl2$interl1* st))
       (interl-ll (nth *comp-interl2$interl-ll* st)))
    (and (< 0 data-size)
         (interl$valid-st interl0 data-size)
         (interl$valid-st interl1 data-size)
         (interl-ll$valid-st interl-ll data-size))))

(defthmd comp-interl2$valid-st=>constraint
  (implies (comp-interl2$valid-st st data-size)
           (posp data-size))
  :hints (("Goal" :in-theory (enable interl$valid-st=>constraint
                                     comp-interl2$valid-st)))
  :rule-classes :forward-chaining)

(defthmd comp-interl2$valid-st=>st-format
  (implies (comp-interl2$valid-st st data-size)
           (comp-interl2$st-format st data-size))
  :hints (("Goal" :in-theory (e/d (interl$valid-st=>st-format
                                   interl-ll$valid-st=>st-format
                                   comp-interl2$st-format
                                   comp-interl2$valid-st)
                                  ()))))

;; Extract the input and output signals for COMP-INTERL2

(progn
  ;; Extract the 1st input data item

  (defun comp-interl2$data0-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (mbe :logic (nfix data-size)
               :exec  data-size)
          (nthcdr 5 inputs)))

  (defthm len-comp-interl2$data0-in
    (equal (len (comp-interl2$data0-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable comp-interl2$data0-in))

  ;; Extract the 2nd input data item

  (defun comp-interl2$data1-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (b* ((size (mbe :logic (nfix data-size)
                     :exec  data-size)))
      (take size
            (nthcdr (+ 5 size) inputs))))

  (defthm len-comp-interl2$data1-in
    (equal (len (comp-interl2$data1-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable comp-interl2$data1-in))

  ;; Extract the 3rd input data item

  (defun comp-interl2$data2-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (b* ((size (mbe :logic (nfix data-size)
                     :exec  data-size)))
      (take size
            (nthcdr (+ 5 (* 2 size)) inputs))))

  (defthm len-comp-interl2$data2-in
    (equal (len (comp-interl2$data2-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable comp-interl2$data2-in))

  ;; Extract the 4th input data item

  (defun comp-interl2$data3-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (b* ((size (mbe :logic (nfix data-size)
                     :exec  data-size)))
      (take size
            (nthcdr (+ 5 (* 3 size)) inputs))))

  (defthm len-comp-interl2$data3-in
    (equal (len (comp-interl2$data3-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable comp-interl2$data3-in))

  ;; Extract the inputs for joint INTERL0

  (defund comp-interl2$interl0-inputs (inputs st data-size)
    (b* ((full-in0 (nth 0 inputs))
         (full-in1 (nth 1 inputs))
         (data0-in (comp-interl2$data0-in inputs data-size))
         (data1-in (comp-interl2$data1-in inputs data-size))
         (select0  (nth (comp-interl2$data-ins-len data-size) inputs))
         (go-signals (nthcdr (+ (comp-interl2$data-ins-len data-size)
                                *comp-interl2$select-num*)
                             inputs))

         (interl0-go-signals (take *interl$go-num* go-signals))

         (interl-ll (nth *comp-interl2$interl-ll* st))
         (interl-ll-ready-in0- (interl-ll$ready-in0- interl-ll)))
      (list* full-in0 full-in1 interl-ll-ready-in0-
             (append data0-in data1-in
                     (cons select0 interl0-go-signals)))))

  ;; Extract the "out-act0" signal for joint INTERL0

  (defund comp-interl2$interl0-out-act0 (inputs st data-size)
    (b* ((interl0-inputs (comp-interl2$interl0-inputs inputs st data-size))
         (interl0 (nth *comp-interl2$interl0* st)))
      (interl$out-act0 interl0-inputs interl0 data-size)))

  ;; Extract the "out-act1" signal for joint INTERL0

  (defund comp-interl2$interl0-out-act1 (inputs st data-size)
    (b* ((interl0-inputs (comp-interl2$interl0-inputs inputs st data-size))
         (interl0 (nth *comp-interl2$interl0* st)))
      (interl$out-act1 interl0-inputs interl0 data-size)))

  (defthm comp-interl2$interl0-out-act-mutually-exclusive
    (implies (and (comp-interl2$valid-st st data-size)
                  (comp-interl2$interl0-out-act0 inputs st data-size))
             (not (comp-interl2$interl0-out-act1 inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl2$valid-st
                                       comp-interl2$interl0-out-act0
                                       comp-interl2$interl0-out-act1))))

  ;; Extract the "out-act" signal for joint INTERL0

  (defund comp-interl2$interl0-out-act (inputs st data-size)
    (f-or (comp-interl2$interl0-out-act0 inputs st data-size)
          (comp-interl2$interl0-out-act1 inputs st data-size)))

  ;; Extract the output data from joint INTERL0

  (defund comp-interl2$interl0-data-out (inputs st data-size)
    (b* ((interl0-inputs (comp-interl2$interl0-inputs inputs st data-size))
         (interl0 (nth *comp-interl2$interl0* st)))
      (interl$data-out interl0-inputs interl0 data-size)))

  ;; Extract the inputs for joint INTERL1

  (defund comp-interl2$interl1-inputs (inputs st data-size)
    (b* ((full-in2 (nth 2 inputs))
         (full-in3 (nth 3 inputs))
         (data2-in (comp-interl2$data2-in inputs data-size))
         (data3-in (comp-interl2$data3-in inputs data-size))
         (select1  (nth (+ (comp-interl2$data-ins-len data-size)
                           *interl$select-num*)
                        inputs))
         (go-signals (nthcdr (+ (comp-interl2$data-ins-len data-size)
                                *comp-interl2$select-num*)
                             inputs))

         (interl1-go-signals (take *interl$go-num*
                                 (nthcdr *interl$go-num* go-signals)))

         (interl-ll (nth *comp-interl2$interl-ll* st))
         (interl-ll-ready-in1- (interl-ll$ready-in1- interl-ll)))
      (list* full-in2 full-in3 interl-ll-ready-in1-
             (append data2-in data3-in
                     (cons select1 interl1-go-signals)))))

  ;; Extract the "out-act0" signal for joint INTERL1

  (defund comp-interl2$interl1-out-act0 (inputs st data-size)
    (b* ((interl1-inputs (comp-interl2$interl1-inputs inputs st data-size))
         (interl1 (nth *comp-interl2$interl1* st)))
      (interl$out-act0 interl1-inputs interl1 data-size)))

  ;; Extract the "out-act1" signal for joint INTERL1

  (defund comp-interl2$interl1-out-act1 (inputs st data-size)
    (b* ((interl1-inputs (comp-interl2$interl1-inputs inputs st data-size))
         (interl1 (nth *comp-interl2$interl1* st)))
      (interl$out-act1 interl1-inputs interl1 data-size)))

  (defthm comp-interl2$interl1-out-act-mutually-exclusive
    (implies (and (comp-interl2$valid-st st data-size)
                  (comp-interl2$interl1-out-act0 inputs st data-size))
             (not (comp-interl2$interl1-out-act1 inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl2$valid-st
                                       comp-interl2$interl1-out-act0
                                       comp-interl2$interl1-out-act1))))

  ;; Extract the "out-act" signal for joint INTERL1

  (defund comp-interl2$interl1-out-act (inputs st data-size)
    (f-or (comp-interl2$interl1-out-act0 inputs st data-size)
          (comp-interl2$interl1-out-act1 inputs st data-size)))

  ;; Extract the output data from joint INTERL1

  (defund comp-interl2$interl1-data-out (inputs st data-size)
    (b* ((interl1-inputs (comp-interl2$interl1-inputs inputs st data-size))
         (interl1 (nth *comp-interl2$interl1* st)))
      (interl$data-out interl1-inputs interl1 data-size)))

  ;; Extract the inputs for joint INTERL-LL

  (defund comp-interl2$interl-ll-inputs (inputs st data-size)
    (b* ((empty-out- (nth 4 inputs))
         (select2 (nth (+ (comp-interl2$data-ins-len data-size)
                          (* 2 *interl$select-num*))
                       inputs))
         (go-signals (nthcdr (+ (comp-interl2$data-ins-len data-size)
                                *comp-interl2$select-num*)
                             inputs))

         (interl-ll-go-signals
          (take *interl-ll$go-num*
                (nthcdr (* 2 *interl$go-num*) go-signals)))

         (interl0-out-act
          (comp-interl2$interl0-out-act inputs st data-size))
         (interl0-data-out
          (comp-interl2$interl0-data-out inputs st data-size))
         (interl1-out-act
          (comp-interl2$interl1-out-act inputs st data-size))
         (interl1-data-out
          (comp-interl2$interl1-data-out inputs st data-size)))
      (list* interl0-out-act interl1-out-act empty-out-
             (append interl0-data-out
                     interl1-data-out
                     (cons select2 interl-ll-go-signals)))))

  ;; Extract the "in0-act" signal

  (defund comp-interl2$in0-act (inputs st data-size)
    (b* ((interl0-inputs (comp-interl2$interl0-inputs inputs st data-size))
         (interl0 (nth *comp-interl2$interl0* st)))
      (interl$in0-act interl0-inputs interl0 data-size)))

  (defthm comp-interl2$in0-act-inactive
    (implies (not (nth 0 inputs))
             (not (comp-interl2$in0-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl2$interl0-inputs
                                       comp-interl2$in0-act))))

  ;; Extract the "in1-act" signal

  (defund comp-interl2$in1-act (inputs st data-size)
    (b* ((interl0-inputs (comp-interl2$interl0-inputs inputs st data-size))
         (interl0 (nth *comp-interl2$interl0* st)))
      (interl$in1-act interl0-inputs interl0 data-size)))

  (defthm comp-interl2$in1-act-inactive
    (implies (not (nth 1 inputs))
             (not (comp-interl2$in1-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl2$interl0-inputs
                                       comp-interl2$in1-act))))

  ;; Extract the "in2-act" signal

  (defund comp-interl2$in2-act (inputs st data-size)
    (b* ((interl1-inputs (comp-interl2$interl1-inputs inputs st data-size))
         (interl1 (nth *comp-interl2$interl1* st)))
      (interl$in0-act interl1-inputs interl1 data-size)))

  (defthm comp-interl2$in2-act-inactive
    (implies (not (nth 2 inputs))
             (not (comp-interl2$in2-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl2$interl1-inputs
                                       comp-interl2$in2-act))))

  ;; Extract the "in3-act" signal

  (defund comp-interl2$in3-act (inputs st data-size)
    (b* ((interl1-inputs (comp-interl2$interl1-inputs inputs st data-size))
         (interl1 (nth *comp-interl2$interl1* st)))
      (interl$in1-act interl1-inputs interl1 data-size)))

  (defthm comp-interl2$in3-act-inactive
    (implies (not (nth 3 inputs))
             (not (comp-interl2$in3-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl2$interl1-inputs
                                       comp-interl2$in3-act))))

  ;; Extract the "out-act0" signal

  (defund comp-interl2$out-act0 (inputs st data-size)
    (b* ((interl-ll-inputs
          (comp-interl2$interl-ll-inputs inputs st data-size))
         (interl-ll (nth *comp-interl2$interl-ll* st)))
      (interl-ll$out-act0 interl-ll-inputs interl-ll data-size)))

  (defthm comp-interl2$out-act0-inactive
    (implies (equal (nth 4 inputs) t)
             (not (comp-interl2$out-act0 inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl2$interl-ll-inputs
                                       comp-interl2$out-act0))))

  ;; Extract the "out-act1" signal

  (defund comp-interl2$out-act1 (inputs st data-size)
    (b* ((interl-ll-inputs
          (comp-interl2$interl-ll-inputs inputs st data-size))
         (interl-ll (nth *comp-interl2$interl-ll* st)))
      (interl-ll$out-act1 interl-ll-inputs interl-ll data-size)))

  (defthm comp-interl2$out-act1-inactive
    (implies (equal (nth 4 inputs) t)
             (not (comp-interl2$out-act1 inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl2$interl-ll-inputs
                                       comp-interl2$out-act1))))

  (defthm comp-interl2$out-act-mutually-exclusive
    (implies (and (comp-interl2$valid-st st data-size)
                  (comp-interl2$out-act0 inputs st data-size))
             (not (comp-interl2$out-act1 inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl2$valid-st
                                       comp-interl2$out-act0
                                       comp-interl2$out-act1))))

  ;; Extract the "out-act" signal

  (defund comp-interl2$out-act (inputs st data-size)
    (f-or (comp-interl2$out-act0 inputs st data-size)
          (comp-interl2$out-act1 inputs st data-size)))

  (defthm comp-interl2$out-act-inactive
    (implies (equal (nth 4 inputs) t)
             (not (comp-interl2$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl2$out-act))))

  ;; Extract the output data

  (defund comp-interl2$data-out (inputs st data-size)
    (b* ((interl-ll-inputs (comp-interl2$interl-ll-inputs inputs st data-size))
         (interl-ll (nth *comp-interl2$interl-ll* st)))
      (interl-ll$data-out interl-ll-inputs interl-ll data-size)))

  (defthm len-comp-interl2$data-out-1
    (implies (comp-interl2$st-format st data-size)
             (equal (len (comp-interl2$data-out inputs st data-size))
                    data-size))
    :hints (("Goal" :in-theory (enable comp-interl2$st-format
                                       comp-interl2$data-out))))

  (defthm len-comp-interl2$data-out-2
    (implies (comp-interl2$valid-st st data-size)
             (equal (len (comp-interl2$data-out inputs st data-size))
                    data-size))
    :hints (("Goal" :in-theory (enable comp-interl2$valid-st
                                       comp-interl2$data-out))))

  (defun comp-interl2$outputs (inputs st data-size)
    (list* (comp-interl2$in0-act inputs st data-size)
           (comp-interl2$in1-act inputs st data-size)
           (comp-interl2$in2-act inputs st data-size)
           (comp-interl2$in3-act inputs st data-size)
           (comp-interl2$out-act inputs st data-size)
           (comp-interl2$data-out inputs st data-size)))
  )

;; The value lemma for COMP-INTERL2

(defthm comp-interl2$value
  (b* ((inputs (list* full-in0 full-in1 full-in2 full-in3 empty-out-
                      (append data0-in data1-in data2-in data3-in
                              selects go-signals))))
    (implies (and (comp-interl2& netlist data-size)
                  (true-listp data0-in)
                  (equal (len data0-in) data-size)
                  (true-listp data1-in)
                  (equal (len data1-in) data-size)
                  (true-listp data2-in)
                  (equal (len data2-in) data-size)
                  (true-listp data3-in)
                  (equal (len data3-in) data-size)
                  (true-listp selects)
                  (equal (len selects) *comp-interl2$select-num*)
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-interl2$go-num*)
                  (comp-interl2$st-format st data-size))
             (equal (se (si 'comp-interl2 data-size) inputs st netlist)
                    (comp-interl2$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'comp-interl2 data-size)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            comp-interl2&
                            comp-interl2*$destructure
                            comp-interl2$st-format
                            interl-ll$arb-merge-inputs
                            interl-ll$out-act0
                            interl-ll$out-act1
                            interl-ll$out-act
                            interl-ll$data-out
                            comp-interl2$data0-in
                            comp-interl2$data1-in
                            comp-interl2$data2-in
                            comp-interl2$data3-in
                            comp-interl2$interl0-inputs
                            comp-interl2$interl1-inputs
                            comp-interl2$interl-ll-inputs
                            comp-interl2$interl0-data-out
                            comp-interl2$interl1-data-out
                            comp-interl2$in0-act
                            comp-interl2$in1-act
                            comp-interl2$in2-act
                            comp-interl2$in3-act
                            comp-interl2$out-act0
                            comp-interl2$out-act1
                            comp-interl2$out-act
                            comp-interl2$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of COMP-INTERL2.

(defun comp-interl2$step (inputs st data-size)
  (b* ((interl0 (nth *comp-interl2$interl0* st))
       (interl1 (nth *comp-interl2$interl1* st))
       (interl-ll (nth *comp-interl2$interl-ll* st))

       (interl0-inputs (comp-interl2$interl0-inputs inputs st data-size))
       (interl1-inputs (comp-interl2$interl1-inputs inputs st data-size))
       (interl-ll-inputs
        (comp-interl2$interl-ll-inputs inputs st data-size)))
    (list
     ;; Joint INTERL0
     (interl$step interl0-inputs interl0 data-size)
     ;; Joint INTERL1
     (interl$step interl1-inputs interl1 data-size)
     ;; Joint INTERL-LL
     (interl-ll$step interl-ll-inputs interl-ll data-size))))

;; The state lemma for COMP-INTERL2

(defthm comp-interl2$state
  (b* ((inputs (list* full-in0 full-in1 full-in2 full-in3 empty-out-
                      (append data0-in data1-in data2-in data3-in
                              selects go-signals))))
    (implies (and (comp-interl2& netlist data-size)
                  (true-listp data0-in)
                  (equal (len data0-in) data-size)
                  (true-listp data1-in)
                  (equal (len data1-in) data-size)
                  (true-listp data2-in)
                  (equal (len data2-in) data-size)
                  (true-listp data3-in)
                  (equal (len data3-in) data-size)
                  (true-listp selects)
                  (equal (len selects) *comp-interl2$select-num*)
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-interl2$go-num*)
                  (comp-interl2$st-format st data-size))
             (equal (de (si 'comp-interl2 data-size) inputs st netlist)
                    (comp-interl2$step inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'comp-interl2 data-size)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            comp-interl2&
                            comp-interl2*$destructure
                            comp-interl2$st-format
                            interl$out-act
                            comp-interl2$data0-in
                            comp-interl2$data1-in
                            comp-interl2$data2-in
                            comp-interl2$data3-in
                            comp-interl2$interl0-out-act0
                            comp-interl2$interl0-out-act1
                            comp-interl2$interl0-out-act
                            comp-interl2$interl0-data-out
                            comp-interl2$interl1-out-act0
                            comp-interl2$interl1-out-act1
                            comp-interl2$interl1-out-act
                            comp-interl2$interl1-data-out
                            comp-interl2$interl0-inputs
                            comp-interl2$interl1-inputs
                            comp-interl2$interl-ll-inputs)
                           (de-module-disabled-rules)))))

(in-theory (disable comp-interl2$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund comp-interl2$input-format (inputs data-size)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-size))))
  (b* ((full-in0   (nth 0 inputs))
       (full-in1   (nth 1 inputs))
       (full-in2   (nth 2 inputs))
       (full-in3   (nth 3 inputs))
       (empty-out- (nth 4 inputs))
       (data0-in   (comp-interl2$data0-in inputs data-size))
       (data1-in   (comp-interl2$data1-in inputs data-size))
       (data2-in   (comp-interl2$data2-in inputs data-size))
       (data3-in   (comp-interl2$data3-in inputs data-size))
       (selects    (take *comp-interl2$select-num*
                         (nthcdr (comp-interl2$data-ins-len data-size)
                                 inputs)))
       (go-signals (nthcdr (+ (comp-interl2$data-ins-len data-size)
                              *comp-interl2$select-num*)
                           inputs)))
    (and
     (booleanp full-in0)
     (booleanp full-in1)
     (booleanp full-in2)
     (booleanp full-in3)
     (booleanp empty-out-)
     (or (not full-in0) (bvp data0-in))
     (or (not full-in1) (bvp data1-in))
     (or (not full-in2) (bvp data2-in))
     (or (not full-in3) (bvp data3-in))
     (true-listp selects)
     (= (len selects) *comp-interl2$select-num*)
     (true-listp go-signals)
     (= (len go-signals) *comp-interl2$go-num*)
     (equal inputs
            (list* full-in0 full-in1 full-in2 full-in3 empty-out-
                   (append data0-in data1-in data2-in data3-in
                           selects go-signals))))))

(local
 (defthm comp-interl2$input-format=>interl0$input-format
   (implies (and (comp-interl2$input-format inputs data-size)
                 (comp-interl2$valid-st st data-size))
            (interl$input-format
             (comp-interl2$interl0-inputs inputs st data-size)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (open-nth
                             interl$valid-st=>constraint
                             interl$input-format
                             interl$data0-in
                             interl$data1-in
                             comp-interl2$input-format
                             comp-interl2$valid-st
                             comp-interl2$interl0-inputs)
                            ())))))

(local
 (defthm comp-interl2$input-format=>interl1$input-format
   (implies (and (comp-interl2$input-format inputs data-size)
                 (comp-interl2$valid-st st data-size))
            (interl$input-format
             (comp-interl2$interl1-inputs inputs st data-size)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (open-nth
                             interl$valid-st=>constraint
                             interl$input-format
                             interl$data0-in
                             interl$data1-in
                             comp-interl2$input-format
                             comp-interl2$valid-st
                             comp-interl2$interl1-inputs)
                            ())))))

(local
 (encapsulate
   ()

   (local
    (defthm comp-interl2$input-format=>interl-ll$input-format-aux-1
      (equal (caddr (comp-interl2$interl0-inputs inputs st data-size))
             (interl-ll$ready-in0- (nth *comp-interl2$interl-ll* st)))
      :hints (("Goal" :in-theory (enable comp-interl2$interl0-inputs)))))

   (local
    (defthm comp-interl2$input-format=>interl-ll$input-format-aux-2
      (equal (caddr (comp-interl2$interl1-inputs inputs st data-size))
             (interl-ll$ready-in1- (nth *comp-interl2$interl-ll* st)))
      :hints (("Goal" :in-theory (enable comp-interl2$interl1-inputs)))))

   (local
    (defthm comp-interl2$input-format=>interl-ll$input-format-aux-3
      (implies
       (and (comp-interl2$input-format inputs data-size)
            (comp-interl2$valid-st st data-size))
       (and (booleanp (interl$out-act0
                       (comp-interl2$interl0-inputs inputs st data-size)
                       (car st)
                       data-size))
            (booleanp (interl$out-act1
                       (comp-interl2$interl0-inputs inputs st data-size)
                       (car st)
                       data-size))))
      :hints
      (("Goal"
        :use (comp-interl2$input-format=>interl0$input-format)
        :in-theory (e/d (open-nth
                         comp-interl2$input-format
                         comp-interl2$valid-st)
                        (comp-interl2$input-format=>interl0$input-format
                         append
                         take-of-too-many
                         len-nthcdr))))))

   (local
    (defthm comp-interl2$input-format=>interl-ll$input-format-aux-4
      (implies
       (and (comp-interl2$input-format inputs data-size)
            (comp-interl2$valid-st st data-size))
       (and (booleanp (interl$out-act0
                       (comp-interl2$interl1-inputs inputs st data-size)
                       (cadr st)
                       data-size))
            (booleanp (interl$out-act1
                       (comp-interl2$interl1-inputs inputs st data-size)
                       (cadr st)
                       data-size))))
      :hints
      (("Goal"
        :use (comp-interl2$input-format=>interl1$input-format)
        :in-theory (e/d (open-nth
                         comp-interl2$input-format
                         comp-interl2$valid-st)
                        (comp-interl2$input-format=>interl1$input-format
                         append
                         take-of-too-many
                         len-nthcdr))))))

   (defthm comp-interl2$input-format=>interl-ll$input-format
     (implies (and (comp-interl2$input-format inputs data-size)
                   (comp-interl2$valid-st st data-size))
              (interl-ll$input-format
               (comp-interl2$interl-ll-inputs inputs st data-size)
               (nth *comp-interl2$interl-ll* st)
               data-size))
     :hints (("Goal"
              :in-theory (e/d (open-nth
                               interl$out-act
                               interl-ll$valid-st=>constraint
                               interl-ll$input-format
                               interl-ll$data0-in
                               interl-ll$data1-in
                               interl-ll$in0-act
                               interl-ll$in1-act
                               comp-interl2$input-format
                               comp-interl2$valid-st
                               comp-interl2$interl0-out-act0
                               comp-interl2$interl0-out-act1
                               comp-interl2$interl0-out-act
                               comp-interl2$interl0-data-out
                               comp-interl2$interl1-out-act0
                               comp-interl2$interl1-out-act1
                               comp-interl2$interl1-out-act
                               comp-interl2$interl1-data-out
                               comp-interl2$interl-ll-inputs)
                              (b-or
                               not
                               len-nthcdr
                               append
                               take-of-too-many
                               take)))))
   ))

(defthm booleanp-comp-interl2$in0-act
  (implies (and (comp-interl2$input-format inputs data-size)
                (comp-interl2$valid-st st data-size))
           (booleanp (comp-interl2$in0-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (enable comp-interl2$valid-st
                              comp-interl2$in0-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-interl2$in1-act
  (implies (and (comp-interl2$input-format inputs data-size)
                (comp-interl2$valid-st st data-size))
           (booleanp (comp-interl2$in1-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (enable comp-interl2$valid-st
                              comp-interl2$in1-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-interl2$in2-act
  (implies (and (comp-interl2$input-format inputs data-size)
                (comp-interl2$valid-st st data-size))
           (booleanp (comp-interl2$in2-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (enable comp-interl2$valid-st
                              comp-interl2$in2-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-interl2$in3-act
  (implies (and (comp-interl2$input-format inputs data-size)
                (comp-interl2$valid-st st data-size))
           (booleanp (comp-interl2$in3-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (enable comp-interl2$valid-st
                              comp-interl2$in3-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-interl2$out-act0
  (implies (and (comp-interl2$input-format inputs data-size)
                (comp-interl2$valid-st st data-size))
           (booleanp (comp-interl2$out-act0 inputs st data-size)))
  :hints (("Goal"
           :in-theory (enable comp-interl2$valid-st
                              comp-interl2$out-act0)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-interl2$out-act1
  (implies (and (comp-interl2$input-format inputs data-size)
                (comp-interl2$valid-st st data-size))
           (booleanp (comp-interl2$out-act1 inputs st data-size)))
  :hints (("Goal"
           :in-theory (enable comp-interl2$valid-st
                              comp-interl2$out-act1)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-interl2$out-act
  (implies (and (comp-interl2$input-format inputs data-size)
                (comp-interl2$valid-st st data-size))
           (booleanp (comp-interl2$out-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (e/d (comp-interl2$out-act)
                           ())))
  :rule-classes (:rewrite :type-prescription))

(encapsulate
  ()

  (local
   (defthm comp-interl2$out-act-rewrite
     (equal (comp-interl2$out-act inputs st data-size)
            (b* ((interl-ll-inputs
                  (comp-interl2$interl-ll-inputs inputs st data-size))
                 (interl-ll (nth *comp-interl2$interl-ll* st)))
              (interl-ll$out-act interl-ll-inputs interl-ll data-size)))
     :hints (("Goal" :in-theory (enable interl-ll$out-act
                                        comp-interl2$out-act0
                                        comp-interl2$out-act1
                                        comp-interl2$out-act)))))

  (defthm bvp-comp-interl2$data-out
    (implies (and (comp-interl2$input-format inputs data-size)
                  (comp-interl2$valid-st st data-size)
                  (comp-interl2$out-act inputs st data-size))
             (bvp (comp-interl2$data-out inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl2$valid-st
                                       comp-interl2$data-out))))
  )

(simulate-lemma comp-interl2)

;; ======================================================================

;; 3. Single-Step-Update Property

(defun interleave-rec (e l)
  (declare (xargs :guard t))
  (if (atom l)
      nil
    (append (interleave e (car l))
            (interleave-rec e (cdr l)))))

(defthm true-list-listp-interleave-rec
  (implies (and (true-listp e)
                (true-list-listp l))
           (true-list-listp (interleave-rec e l)))
  :rule-classes (:rewrite :type-prescription))

(defthm interleave-is-subset-of-interleave-rec
  (implies (member e2 x)
           (subsetp (interleave e1 e2) (interleave-rec e1 x))))

(defthm subsetp-interleave-rec
  (implies (subsetp x y)
           (subsetp (interleave-rec e x) (interleave-rec e y))))

(defthm subsetp-prepend-rec-of-interleave-rec-1
  (implies (and (true-list-listp y)
                (true-listp z))
           (subsetp (prepend-rec (interleave-rec x y) z)
                    (interleave-rec (append x z) y))))

(defthm subsetp-prepend-rec-of-interleave-rec-2
  (implies (and (true-listp x)
                (true-listp z))
           (subsetp (prepend-rec (interleave-rec x y) z)
                    (interleave-rec x (prepend-rec y z)))))

(in-theory (disable interleave-rec))

(defun interleave2 (l1 l2)
  (declare (xargs :guard t))
  (if (atom l1)
      nil
    (append (interleave-rec (car l1) l2)
            (interleave2 (cdr l1) l2))))

(defthm true-list-listp-interleave2
  (implies (and (true-list-listp l1)
                (true-list-listp l2))
           (true-list-listp (interleave2 l1 l2)))
  :rule-classes (:rewrite :type-prescription))

(defthm interleave-rec-is-subset-of-interleave2
  (implies (member e x)
           (subsetp (interleave-rec e y)
                    (interleave2 x y))))

(defthm subsetp-interleave2
  (implies (and (subsetp x1 x2)
                (subsetp y1 y2))
           (subsetp (interleave2 x1 y1) (interleave2 x2 y2)))
  :hints (("Subgoal *1/3"
           :use (:instance subsetp-interleave-rec
                           (e (car x1))
                           (x y1)
                           (y y2))
           :in-theory (disable subsetp-interleave-rec))))

(defthm subsetp-prepend-rec-interleave2-1
  (implies (and (true-list-listp y)
                (true-listp z))
           (subsetp (prepend-rec (interleave2 x y) z)
                    (interleave2 (prepend-rec x z) y))))

(defthm subsetp-prepend-rec-interleave2-2
  (implies (and (true-list-listp x)
                (true-listp z))
           (subsetp (prepend-rec (interleave2 x y) z)
                    (interleave2 x (prepend-rec y z)))))

(defthm member-append-interleave2-1
  (implies (and (member x (interleave2 y z))
                (true-listp x1)
                (true-list-listp z))
           (member (append x x1)
                   (interleave2 (prepend-rec y x1) z)))
  :hints (("Goal"
           :in-theory (disable subsetp-prepend-rec-interleave2-1)
           :use (:instance subsetp-prepend-rec-interleave2-1
                           (x y)
                           (y z)
                           (z x1)))))

(defthm member-append-interleave2-2
  (implies (and (member x (interleave2 y z))
                (true-listp x1)
                (true-list-listp y))
           (member (append x x1)
                   (interleave2 y (prepend-rec z x1))))
  :hints (("Goal"
           :in-theory (disable subsetp-prepend-rec-interleave2-2)
           :use (:instance subsetp-prepend-rec-interleave2-2
                           (x y)
                           (y z)
                           (z x1)))))

(progn
  (defthm member-append-interleave2-1-instance-1
    (implies (and (member (append a b) (interleave2 (prepend-rec y1 y2) z))
                  (equal y++x1 (prepend-rec y1 (append y2 x1)))
                  (true-listp x1)
                  (true-list-listp z))
             (member (append a b x1)
                     (interleave2 y++x1 z)))
    :hints (("Goal"
             :use (:instance member-append-interleave2-1
                             (x (append a b))
                             (y (prepend-rec y1 y2))))))

  (defthm member-append-interleave2-1-instance-2
    (implies
     (and (member (append a b)
                  (interleave2 (prepend-rec (interleave y1 y2)
                                            (cons e1 y3))
                               z))
          (equal y1e1 (append y1 (list e1)))
          (equal y3++x1 (append y3 x1))
          (true-listp x1)
          (true-listp y2)
          (true-list-listp z))
     (member (append a b x1)
             (interleave2 (prepend-rec (interleave y1e1 y2) y3++x1)
                          z)))
    :hints (("Goal"
             :in-theory (disable member-append-interleave2-1-instance-1)
             :use (:instance member-append-interleave2-1-instance-1
                             (y1 (interleave y1e1 y2))
                             (y2 y3)
                             (y++x1 (prepend-rec (interleave y1e1 y2)
                                                 y3++x1))))))

  (defthm member-append-interleave2-1-instance-3
    (implies
     (and (member (append a b)
                  (interleave2 (prepend-rec (interleave y1 y2)
                                            (cons e1 y3))
                               z))
          (equal y2e1 (append y2 (list e1)))
          (equal y3++x1 (append y3 x1))
          (true-listp x1)
          (true-listp y1)
          (true-list-listp z))
     (member (append a b x1)
             (interleave2 (prepend-rec (interleave y1 y2e1) y3++x1)
                          z)))
    :hints (("Goal"
             :in-theory (disable member-append-interleave2-1-instance-1)
             :use (:instance member-append-interleave2-1-instance-1
                             (y1 (interleave y1 y2e1))
                             (y2 y3)
                             (y++x1 (prepend-rec (interleave y1 y2e1)
                                                 y3++x1))))))

  (defthm member-append-interleave2-1-instance-4
    (implies
     (and (member (append a b)
                  (interleave2 (prepend-rec y1 y2)
                               (prepend-rec (interleave z1 z2)
                                            (cons e z3))))
          (equal y++x1 (prepend-rec y1 (append y2 x1)))
          (equal z1e (append z1 (list e)))
          (true-listp x1)
          (true-listp z2)
          (true-listp z3))
     (member (append a b x1)
             (interleave2 y++x1
                          (prepend-rec (interleave z1e z2) z3))))
    :hints (("Goal"
             :in-theory (disable member-append-interleave2-1-instance-1)
             :use (:instance member-append-interleave2-1-instance-1
                             (z (prepend-rec (interleave z1 z2)
                                             (cons e z3)))))))

  (defthm member-append-interleave2-1-instance-5
    (implies
     (and (member (append a b)
                  (interleave2 (prepend-rec y1 y2)
                               (prepend-rec (interleave z1 z2)
                                            (cons e z3))))
          (equal y++x1 (prepend-rec y1 (append y2 x1)))
          (equal z2e (append z2 (list e)))
          (true-listp x1)
          (true-listp z1)
          (true-listp z3))
     (member (append a b x1)
             (interleave2 y++x1
                          (prepend-rec (interleave z1 z2e) z3))))
    :hints (("Goal"
             :in-theory (disable member-append-interleave2-1-instance-1)
             :use (:instance member-append-interleave2-1-instance-1
                             (z (prepend-rec (interleave z1 z2)
                                             (cons e z3)))))))

  (defthm member-append-interleave2-1-instance-6
    (implies
     (and (member (append a b)
                  (interleave2 (prepend-rec (interleave y1 y2)
                                            (cons e1 y3))
                               (prepend-rec (interleave z1 z2)
                                            (cons e2 z3))))
          (equal y1e1 (append y1 (list e1)))
          (equal y3++x1 (append y3 x1))
          (equal z1e2 (append z1 (list e2)))
          (true-listp x1)
          (true-listp y2)
          (true-listp z2)
          (true-listp z3))
     (member (append a b x1)
             (interleave2 (prepend-rec (interleave y1e1 y2) y3++x1)
                          (prepend-rec (interleave z1e2 z2) z3))))
    :hints (("Goal"
             :in-theory (disable member-append-interleave2-1-instance-4)
             :use (:instance member-append-interleave2-1-instance-4
                             (y1 (interleave y1e1 y2))
                             (y2 y3)
                             (y++x1 (prepend-rec (interleave y1e1 y2)
                                                 y3++x1))
                             (e e2)
                             (z1e z1e2)))))

  (defthm member-append-interleave2-1-instance-7
    (implies
     (and (member (append a b)
                  (interleave2 (prepend-rec (interleave y1 y2)
                                            (cons e1 y3))
                               (prepend-rec (interleave z1 z2)
                                            (cons e2 z3))))
          (equal y2e1 (append y2 (list e1)))
          (equal y3++x1 (append y3 x1))
          (equal z1e2 (append z1 (list e2)))
          (true-listp x1)
          (true-listp y1)
          (true-listp z2)
          (true-listp z3))
     (member (append a b x1)
             (interleave2 (prepend-rec (interleave y1 y2e1) y3++x1)
                          (prepend-rec (interleave z1e2 z2) z3))))
    :hints (("Goal"
             :in-theory (disable member-append-interleave2-1-instance-4)
             :use (:instance member-append-interleave2-1-instance-4
                             (y1 (interleave y1 y2e1))
                             (y2 y3)
                             (y++x1 (prepend-rec (interleave y1 y2e1)
                                                 y3++x1))
                             (e e2)
                             (z1e z1e2)))))

  (defthm member-append-interleave2-1-instance-8
    (implies
     (and (member (append a b)
                  (interleave2 (prepend-rec (interleave y1 y2)
                                            (cons e1 y3))
                               (prepend-rec (interleave z1 z2)
                                            (cons e2 z3))))
          (equal y1e1 (append y1 (list e1)))
          (equal y3++x1 (append y3 x1))
          (equal z2e2 (append z2 (list e2)))
          (true-listp x1)
          (true-listp y2)
          (true-listp z1)
          (true-listp z3))
     (member (append a b x1)
             (interleave2 (prepend-rec (interleave y1e1 y2) y3++x1)
                          (prepend-rec (interleave z1 z2e2) z3))))
    :hints (("Goal"
             :in-theory (disable member-append-interleave2-1-instance-5)
             :use (:instance member-append-interleave2-1-instance-5
                             (y1 (interleave y1e1 y2))
                             (y2 y3)
                             (y++x1 (prepend-rec (interleave y1e1 y2)
                                                 y3++x1))
                             (e e2)
                             (z2e z2e2)))))

  (defthm member-append-interleave2-1-instance-9
    (implies
     (and (member (append a b)
                  (interleave2 (prepend-rec (interleave y1 y2)
                                            (cons e1 y3))
                               (prepend-rec (interleave z1 z2)
                                            (cons e2 z3))))
          (equal y2e1 (append y2 (list e1)))
          (equal y3++x1 (append y3 x1))
          (equal z2e2 (append z2 (list e2)))
          (true-listp x1)
          (true-listp y1)
          (true-listp z1)
          (true-listp z3))
     (member (append a b x1)
             (interleave2 (prepend-rec (interleave y1 y2e1) y3++x1)
                          (prepend-rec (interleave z1 z2e2) z3))))
    :hints (("Goal"
             :in-theory (disable member-append-interleave2-1-instance-5)
             :use (:instance member-append-interleave2-1-instance-5
                             (y1 (interleave y1 y2e1))
                             (y2 y3)
                             (y++x1 (prepend-rec (interleave y1 y2e1)
                                                 y3++x1))
                             (e e2)
                             (z2e z2e2)))))
  )

(progn
  (defthm member-append-interleave2-2-instance-1
    (implies (and (member (append a b) (interleave2 y (prepend-rec z1 z2)))
                  (equal z++x1 (prepend-rec z1 (append z2 x1)))
                  (true-listp x1)
                  (true-list-listp y))
             (member (append a b x1)
                     (interleave2 y z++x1)))
    :hints (("Goal"
             :use (:instance member-append-interleave2-2
                             (x (append a b))
                             (z (prepend-rec z1 z2))))))

  (defthm member-append-interleave2-2-instance-2
    (implies
     (and (member (append a b)
                  (interleave2 y
                               (prepend-rec (interleave z1 z2)
                                            (cons e2 z3))))
          (equal z1e2 (append z1 (list e2)))
          (equal z3++x1 (append z3 x1))
          (true-listp x1)
          (true-list-listp y)
          (true-listp z2))
     (member (append a b x1)
             (interleave2 y
                          (prepend-rec (interleave z1e2 z2) z3++x1))))
    :hints (("Goal"
             :in-theory (disable member-append-interleave2-2-instance-1)
             :use (:instance member-append-interleave2-2-instance-1
                             (z1 (interleave z1e2 z2))
                             (z2 z3)
                             (z++x1 (prepend-rec (interleave z1e2 z2)
                                                 z3++x1))))))

  (defthm member-append-interleave2-2-instance-3
    (implies
     (and (member (append a b)
                  (interleave2 y
                               (prepend-rec (interleave z1 z2)
                                            (cons e2 z3))))
          (equal z2e2 (append z2 (list e2)))
          (equal z3++x1 (append z3 x1))
          (true-listp x1)
          (true-list-listp y)
          (true-listp z1))
     (member (append a b x1)
             (interleave2 y
                          (prepend-rec (interleave z1 z2e2) z3++x1))))
    :hints (("Goal"
             :in-theory (disable member-append-interleave2-2-instance-1)
             :use (:instance member-append-interleave2-2-instance-1
                             (z1 (interleave z1 z2e2))
                             (z2 z3)
                             (z++x1 (prepend-rec (interleave z1 z2e2)
                                                 z3++x1))))))

  (defthm member-append-interleave2-2-instance-4
    (implies
     (and (member (append a b)
                  (interleave2 (prepend-rec (interleave y1 y2)
                                            (cons e y3))
                               (prepend-rec z1 z2)))
          (equal y1e (append y1 (list e)))
          (equal z++x1 (prepend-rec z1 (append z2 x1)))
          (true-listp x1)
          (true-listp y2)
          (true-listp y3))
     (member (append a b x1)
             (interleave2 (prepend-rec (interleave y1e y2) y3)
                          z++x1)))
    :hints (("Goal"
             :in-theory (disable member-append-interleave2-2-instance-1)
             :use (:instance member-append-interleave2-2-instance-1
                             (y (prepend-rec (interleave y1 y2)
                                             (cons e y3)))))))

  (defthm member-append-interleave2-2-instance-5
    (implies
     (and (member (append a b)
                  (interleave2 (prepend-rec (interleave y1 y2)
                                            (cons e y3))
                               (prepend-rec z1 z2)))
          (equal y2e (append y2 (list e)))
          (equal z++x1 (prepend-rec z1 (append z2 x1)))
          (true-listp x1)
          (true-listp y1)
          (true-listp y3))
     (member (append a b x1)
             (interleave2 (prepend-rec (interleave y1 y2e) y3)
                          z++x1)))
    :hints (("Goal"
             :in-theory (disable member-append-interleave2-2-instance-1)
             :use (:instance member-append-interleave2-2-instance-1
                             (y (prepend-rec (interleave y1 y2)
                                             (cons e y3)))))))

  (defthm member-append-interleave2-2-instance-6
    (implies
     (and (member (append a b)
                  (interleave2 (prepend-rec (interleave y1 y2)
                                            (cons e1 y3))
                               (prepend-rec (interleave z1 z2)
                                            (cons e2 z3))))
          (equal y1e1 (append y1 (list e1)))
          (equal z1e2 (append z1 (list e2)))
          (equal z3++x1 (append z3 x1))
          (true-listp x1)
          (true-listp y2)
          (true-listp y3)
          (true-listp z2))
     (member (append a b x1)
             (interleave2 (prepend-rec (interleave y1e1 y2) y3)
                          (prepend-rec (interleave z1e2 z2) z3++x1))))
    :hints (("Goal"
             :in-theory (disable member-append-interleave2-2-instance-4)
             :use (:instance member-append-interleave2-2-instance-4
                             (e e1)
                             (y1e y1e1)
                             (z1 (interleave z1e2 z2))
                             (z2 z3)
                             (z++x1 (prepend-rec (interleave z1e2 z2)
                                                 z3++x1))))))

  (defthm member-append-interleave2-2-instance-7
    (implies
     (and (member (append a b)
                  (interleave2 (prepend-rec (interleave y1 y2)
                                            (cons e1 y3))
                               (prepend-rec (interleave z1 z2)
                                            (cons e2 z3))))
          (equal y1e1 (append y1 (list e1)))
          (equal z2e2 (append z2 (list e2)))
          (equal z3++x1 (append z3 x1))
          (true-listp x1)
          (true-listp y2)
          (true-listp y3)
          (true-listp z1))
     (member (append a b x1)
             (interleave2 (prepend-rec (interleave y1e1 y2) y3)
                          (prepend-rec (interleave z1 z2e2) z3++x1))))
    :hints (("Goal"
             :in-theory (disable member-append-interleave2-2-instance-4)
             :use (:instance member-append-interleave2-2-instance-4
                             (e e1)
                             (y1e y1e1)
                             (z1 (interleave z1 z2e2))
                             (z2 z3)
                             (z++x1 (prepend-rec (interleave z1 z2e2)
                                                 z3++x1))))))

  (defthm member-append-interleave2-2-instance-8
    (implies
     (and (member (append a b)
                  (interleave2 (prepend-rec (interleave y1 y2)
                                            (cons e1 y3))
                               (prepend-rec (interleave z1 z2)
                                            (cons e2 z3))))
          (equal y2e1 (append y2 (list e1)))
          (equal z1e2 (append z1 (list e2)))
          (equal z3++x1 (append z3 x1))
          (true-listp x1)
          (true-listp y1)
          (true-listp y3)
          (true-listp z2))
     (member (append a b x1)
             (interleave2 (prepend-rec (interleave y1 y2e1) y3)
                          (prepend-rec (interleave z1e2 z2) z3++x1))))
    :hints (("Goal"
             :in-theory (disable member-append-interleave2-2-instance-5)
             :use (:instance member-append-interleave2-2-instance-5
                             (e e1)
                             (y2e y2e1)
                             (z1 (interleave z1e2 z2))
                             (z2 z3)
                             (z++x1 (prepend-rec (interleave z1e2 z2)
                                                 z3++x1))))))

  (defthm member-append-interleave2-2-instance-9
    (implies
     (and (member (append a b)
                  (interleave2 (prepend-rec (interleave y1 y2)
                                            (cons e1 y3))
                               (prepend-rec (interleave z1 z2)
                                            (cons e2 z3))))
          (equal y2e1 (append y2 (list e1)))
          (equal z2e2 (append z2 (list e2)))
          (equal z3++x1 (append z3 x1))
          (true-listp x1)
          (true-listp y1)
          (true-listp y3)
          (true-listp z1))
     (member (append a b x1)
             (interleave2 (prepend-rec (interleave y1 y2e1) y3)
                          (prepend-rec (interleave z1 z2e2) z3++x1))))
    :hints (("Goal"
             :in-theory (disable member-append-interleave2-2-instance-5)
             :use (:instance member-append-interleave2-2-instance-5
                             (e e1)
                             (y2e y2e1)
                             (z1 (interleave z1 z2e2))
                             (z2 z3)
                             (z++x1 (prepend-rec (interleave z1 z2e2)
                                                 z3++x1))))))
  )

(in-theory (disable interleave2))

;; The extraction functions for COMP-INTERL2

(defund comp-interl2$extract0 (st)
  (b* ((interl0 (nth *comp-interl2$interl0* st)))
    (interl$extract0 interl0)))

(defund comp-interl2$extract1 (st)
  (b* ((interl0 (nth *comp-interl2$interl0* st)))
    (interl$extract1 interl0)))

(defund comp-interl2$extract2 (st)
  (b* ((interl1 (nth *comp-interl2$interl1* st)))
    (interl$extract0 interl1)))

(defund comp-interl2$extract3 (st)
  (b* ((interl1 (nth *comp-interl2$interl1* st)))
    (interl$extract1 interl1)))

(defund comp-interl2$extract4 (st)
  (b* ((interl-ll (nth *comp-interl2$interl-ll* st)))
    (interl-ll$extract0 interl-ll)))

(defund comp-interl2$extract5 (st)
  (b* ((interl-ll (nth *comp-interl2$interl-ll* st)))
    (interl-ll$extract1 interl-ll)))

(defthm comp-interl2$extract0-not-empty
  (implies (and (comp-interl2$interl0-out-act0 inputs st data-size)
                (comp-interl2$valid-st st data-size))
           (< 0 (len (comp-interl2$extract0 st))))
  :hints (("Goal"
           :in-theory (e/d (comp-interl2$interl0-out-act0
                            comp-interl2$valid-st
                            comp-interl2$extract0)
                           ())))
  :rule-classes :linear)

(defthm comp-interl2$extract1-not-empty
  (implies (and (comp-interl2$interl0-out-act1 inputs st data-size)
                (comp-interl2$valid-st st data-size))
           (< 0 (len (comp-interl2$extract1 st))))
  :hints (("Goal"
           :in-theory (e/d (comp-interl2$interl0-out-act1
                            comp-interl2$valid-st
                            comp-interl2$extract1)
                           ())))
  :rule-classes :linear)

(defthm comp-interl2$extract2-not-empty
  (implies (and (comp-interl2$interl1-out-act0 inputs st data-size)
                (comp-interl2$valid-st st data-size))
           (< 0 (len (comp-interl2$extract2 st))))
  :hints (("Goal"
           :in-theory (e/d (comp-interl2$interl1-out-act0
                            comp-interl2$valid-st
                            comp-interl2$extract2)
                           ())))
  :rule-classes :linear)

(defthm comp-interl2$extract3-not-empty
  (implies (and (comp-interl2$interl1-out-act1 inputs st data-size)
                (comp-interl2$valid-st st data-size))
           (< 0 (len (comp-interl2$extract3 st))))
  :hints (("Goal"
           :in-theory (e/d (comp-interl2$interl1-out-act1
                            comp-interl2$valid-st
                            comp-interl2$extract3)
                           ())))
  :rule-classes :linear)

(defthm comp-interl2$extract4-not-empty
  (implies (and (comp-interl2$out-act0 inputs st data-size)
                (comp-interl2$valid-st st data-size))
           (< 0 (len (comp-interl2$extract4 st))))
  :hints (("Goal"
           :in-theory (e/d (comp-interl2$out-act0
                            comp-interl2$valid-st
                            comp-interl2$extract4)
                           ())))
  :rule-classes :linear)

(defthm comp-interl2$extract5-not-empty
  (implies (and (comp-interl2$out-act1 inputs st data-size)
                (comp-interl2$valid-st st data-size))
           (< 0 (len (comp-interl2$extract5 st))))
  :hints (("Goal"
           :in-theory (e/d (comp-interl2$out-act1
                            comp-interl2$valid-st
                            comp-interl2$extract5)
                           ())))
  :rule-classes :linear)

;; The extracted next-state functions for COMP-INTERL2.  Note that these
;; functions avoid exploring the internal computation of COMP-INTERL2.

(defund comp-interl2$extracted0-step (inputs st data-size)
  (b* ((data (comp-interl2$data0-in inputs data-size))
       (extracted-st (comp-interl2$extract0 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-interl2$interl0-out-act0 inputs st data-size) t)
      (cond
       ((equal (comp-interl2$in0-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (comp-interl2$in0-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

(defund comp-interl2$extracted1-step (inputs st data-size)
  (b* ((data (comp-interl2$data1-in inputs data-size))
       (extracted-st (comp-interl2$extract1 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-interl2$interl0-out-act1 inputs st data-size) t)
      (cond
       ((equal (comp-interl2$in1-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (comp-interl2$in1-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

(defund comp-interl2$extracted2-step (inputs st data-size)
  (b* ((data (comp-interl2$data2-in inputs data-size))
       (extracted-st (comp-interl2$extract2 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-interl2$interl1-out-act0 inputs st data-size) t)
      (cond
       ((equal (comp-interl2$in2-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (comp-interl2$in2-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

(defund comp-interl2$extracted3-step (inputs st data-size)
  (b* ((data (comp-interl2$data3-in inputs data-size))
       (extracted-st (comp-interl2$extract3 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-interl2$interl1-out-act1 inputs st data-size) t)
      (cond
       ((equal (comp-interl2$in3-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (comp-interl2$in3-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

(defund comp-interl2$extracted4-step (inputs st data-size)
  (b* ((data (comp-interl2$interl0-data-out inputs st data-size))
       (extracted-st (comp-interl2$extract4 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-interl2$out-act0 inputs st data-size) t)
      (cond
       ((equal (comp-interl2$interl0-out-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (comp-interl2$interl0-out-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

(defund comp-interl2$extracted5-step (inputs st data-size)
  (b* ((data (comp-interl2$interl1-data-out inputs st data-size))
       (extracted-st (comp-interl2$extract5 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-interl2$out-act1 inputs st data-size) t)
      (cond
       ((equal (comp-interl2$interl1-out-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (comp-interl2$interl1-out-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm comp-interl2$extracted0+1-step-correct-aux-1
     (equal (interl$data0-in
             (comp-interl2$interl0-inputs inputs st data-size)
             data-size)
            (comp-interl2$data0-in inputs data-size))
     :hints (("Goal" :in-theory (enable comp-interl2$interl0-inputs
                                        interl$data0-in)))))

  (local
   (defthm comp-interl2$extracted0+1-step-correct-aux-2
     (equal (interl$data1-in
             (comp-interl2$interl0-inputs inputs st data-size)
             data-size)
            (comp-interl2$data1-in inputs data-size))
     :hints (("Goal" :in-theory (enable comp-interl2$interl0-inputs
                                        comp-interl2$data1-in
                                        interl$data1-in)))))

  (defthm comp-interl2$extracted0+1-step-correct
    (b* ((next-st (comp-interl2$step inputs st data-size)))
      (implies
       (and (comp-interl2$input-format inputs data-size)
            (comp-interl2$valid-st st data-size))
       (and (equal (comp-interl2$extract0 next-st)
                   (comp-interl2$extracted0-step inputs st data-size))
            (equal (comp-interl2$extract1 next-st)
                   (comp-interl2$extracted1-step inputs st data-size)))))
    :hints (("Goal"
             :in-theory (e/d (interl$extracted0-step
                              interl$extracted1-step
                              comp-interl2$extracted0-step
                              comp-interl2$extracted1-step
                              comp-interl2$valid-st
                              comp-interl2$step
                              comp-interl2$interl0-out-act0
                              comp-interl2$interl0-out-act1
                              comp-interl2$in0-act
                              comp-interl2$in1-act
                              comp-interl2$extract0
                              comp-interl2$extract1)
                             ()))))

  (local
   (defthm comp-interl2$extracted2+3-step-correct-aux-1
     (equal (interl$data0-in
             (comp-interl2$interl1-inputs inputs st data-size)
             data-size)
            (comp-interl2$data2-in inputs data-size))
     :hints (("Goal" :in-theory (enable comp-interl2$interl1-inputs
                                        interl$data0-in)))))

  (local
   (defthm comp-interl2$extracted2+3-step-correct-aux-2
     (equal (interl$data1-in
             (comp-interl2$interl1-inputs inputs st data-size)
             data-size)
            (comp-interl2$data3-in inputs data-size))
     :hints (("Goal" :in-theory (enable comp-interl2$interl1-inputs
                                        comp-interl2$data3-in
                                        interl$data1-in)))))

  (defthm comp-interl2$extracted2+3-step-correct
    (b* ((next-st (comp-interl2$step inputs st data-size)))
      (implies
       (and (comp-interl2$input-format inputs data-size)
            (comp-interl2$valid-st st data-size))
       (and (equal (comp-interl2$extract2 next-st)
                   (comp-interl2$extracted2-step inputs st data-size))
            (equal (comp-interl2$extract3 next-st)
                   (comp-interl2$extracted3-step inputs st data-size)))))
    :hints (("Goal"
             :in-theory (e/d (interl$extracted0-step
                              interl$extracted1-step
                              comp-interl2$extracted2-step
                              comp-interl2$extracted3-step
                              comp-interl2$valid-st
                              comp-interl2$step
                              comp-interl2$interl1-out-act0
                              comp-interl2$interl1-out-act1
                              comp-interl2$in2-act
                              comp-interl2$in3-act
                              comp-interl2$extract2
                              comp-interl2$extract3)
                             ()))))

  (local
   (defthm comp-interl2$extracted4+5-step-correct-aux-1
     (b* ((interl0 (nth *comp-interl2$interl0* st))
          (interl1 (nth *comp-interl2$interl1* st))
          (interl-ll-inputs
           (comp-interl2$interl-ll-inputs inputs st data-size)))
       (implies
        (and (interl$valid-st interl0 data-size)
             (interl$valid-st interl1 data-size))
        (equal (interl-ll$data0-in interl-ll-inputs data-size)
               (comp-interl2$interl0-data-out inputs st data-size))))
     :hints (("Goal"
              :in-theory (enable interl$valid-st=>constraint
                                 interl-ll$data0-in
                                 comp-interl2$interl-ll-inputs
                                 comp-interl2$interl0-data-out
                                 comp-interl2$interl1-data-out)))))

  (local
   (defthm comp-interl2$extracted4+5-step-correct-aux-2
     (b* ((interl0 (nth *comp-interl2$interl0* st))
          (interl1 (nth *comp-interl2$interl1* st))
          (interl-ll-inputs
           (comp-interl2$interl-ll-inputs inputs st data-size)))
       (implies
        (and (interl$valid-st interl0 data-size)
             (interl$valid-st interl1 data-size))
        (equal (interl-ll$data1-in interl-ll-inputs data-size)
               (comp-interl2$interl1-data-out inputs st data-size))))
     :hints (("Goal"
              :in-theory (enable interl$valid-st=>constraint
                                 interl-ll$data1-in
                                 comp-interl2$interl-ll-inputs
                                 comp-interl2$interl0-data-out
                                 comp-interl2$interl1-data-out)))))

  (local
   (defthm comp-interl2$interl-ll-in0-act-=-interl0-out-act
     (equal (interl-ll$in0-act
             (comp-interl2$interl-ll-inputs inputs st data-size))
            (interl$out-act
             (comp-interl2$interl0-inputs inputs st data-size)
             (nth *comp-interl2$interl0* st)
             data-size))
     :hints (("Goal"
              :in-theory (enable interl$out-act
                                 interl-ll$in0-act
                                 comp-interl2$interl0-out-act0
                                 comp-interl2$interl0-out-act1
                                 comp-interl2$interl0-out-act
                                 comp-interl2$interl0-inputs
                                 comp-interl2$interl-ll-inputs)))))

  (local
   (defthm comp-interl2$interl-ll-in1-act-=-interl1-out-act
     (equal (interl-ll$in1-act
             (comp-interl2$interl-ll-inputs inputs st data-size))
            (interl$out-act
             (comp-interl2$interl1-inputs inputs st data-size)
             (nth *comp-interl2$interl1* st)
             data-size))
     :hints (("Goal"
              :in-theory (enable interl$out-act
                                 interl-ll$in1-act
                                 comp-interl2$interl1-out-act0
                                 comp-interl2$interl1-out-act1
                                 comp-interl2$interl1-out-act
                                 comp-interl2$interl1-inputs
                                 comp-interl2$interl-ll-inputs)))))

  (defthm comp-interl2$extracted4+5-step-correct
    (b* ((next-st (comp-interl2$step inputs st data-size)))
      (implies
       (and (comp-interl2$input-format inputs data-size)
            (comp-interl2$valid-st st data-size))
       (and (equal (comp-interl2$extract4 next-st)
                   (comp-interl2$extracted4-step inputs st data-size))
            (equal (comp-interl2$extract5 next-st)
                   (comp-interl2$extracted5-step inputs st data-size)))))
    :hints (("Goal"
             :in-theory (e/d (interl$out-act
                              interl-ll$extracted0-step
                              interl-ll$extracted1-step
                              comp-interl2$extracted4-step
                              comp-interl2$extracted5-step
                              comp-interl2$valid-st
                              comp-interl2$step
                              comp-interl2$interl0-out-act0
                              comp-interl2$interl0-out-act1
                              comp-interl2$interl0-out-act
                              comp-interl2$interl1-out-act0
                              comp-interl2$interl1-out-act1
                              comp-interl2$interl1-out-act
                              comp-interl2$out-act0
                              comp-interl2$out-act1
                              comp-interl2$extract4
                              comp-interl2$extract5)
                             ()))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that comp-interl2$valid-st is an invariant.

(defthm comp-interl2$valid-st-preserved
  (implies (and (comp-interl2$input-format inputs data-size)
                (comp-interl2$valid-st st data-size))
           (comp-interl2$valid-st (comp-interl2$step inputs st data-size)
                               data-size))
  :hints (("Goal"
           :in-theory (e/d (comp-interl2$valid-st
                            comp-interl2$step)
                           ()))))

(defthm comp-interl2$extract0-lemma
  (implies
   (and (comp-interl2$input-format inputs data-size)
        (comp-interl2$valid-st st data-size)
        (comp-interl2$interl0-out-act0 inputs st data-size))
   (equal (list (comp-interl2$interl0-data-out inputs st data-size))
          (nthcdr (1- (len (comp-interl2$extract0 st)))
                  (comp-interl2$extract0 st))))
  :hints (("Goal"
           :in-theory (enable comp-interl2$valid-st
                              comp-interl2$extract0
                              comp-interl2$interl0-out-act0
                              comp-interl2$interl0-data-out))))

(defthm comp-interl2$extract1-lemma
  (implies
   (and (comp-interl2$input-format inputs data-size)
        (comp-interl2$valid-st st data-size)
        (comp-interl2$interl0-out-act1 inputs st data-size))
   (equal (list (comp-interl2$interl0-data-out inputs st data-size))
          (nthcdr (1- (len (comp-interl2$extract1 st)))
                  (comp-interl2$extract1 st))))
  :hints (("Goal"
           :in-theory (enable comp-interl2$valid-st
                              comp-interl2$extract1
                              comp-interl2$interl0-out-act1
                              comp-interl2$interl0-data-out))))

(defthm comp-interl2$extract2-lemma
  (implies
   (and (comp-interl2$input-format inputs data-size)
        (comp-interl2$valid-st st data-size)
        (comp-interl2$interl1-out-act0 inputs st data-size))
   (equal (list (comp-interl2$interl1-data-out inputs st data-size))
          (nthcdr (1- (len (comp-interl2$extract2 st)))
                  (comp-interl2$extract2 st))))
  :hints (("Goal"
           :in-theory (enable comp-interl2$valid-st
                              comp-interl2$extract2
                              comp-interl2$interl1-out-act0
                              comp-interl2$interl1-data-out))))

(defthm comp-interl2$extract3-lemma
  (implies
   (and (comp-interl2$input-format inputs data-size)
        (comp-interl2$valid-st st data-size)
        (comp-interl2$interl1-out-act1 inputs st data-size))
   (equal (list (comp-interl2$interl1-data-out inputs st data-size))
          (nthcdr (1- (len (comp-interl2$extract3 st)))
                  (comp-interl2$extract3 st))))
  :hints (("Goal"
           :in-theory (enable comp-interl2$valid-st
                              comp-interl2$extract3
                              comp-interl2$interl1-out-act1
                              comp-interl2$interl1-data-out))))

(defthm comp-interl2$extract4-lemma
  (implies (and (comp-interl2$input-format inputs data-size)
                (comp-interl2$valid-st st data-size)
                (comp-interl2$out-act0 inputs st data-size))
           (equal (list (comp-interl2$data-out inputs st data-size))
                  (nthcdr (1- (len (comp-interl2$extract4 st)))
                          (comp-interl2$extract4 st))))
  :hints (("Goal"
           :in-theory (enable comp-interl2$valid-st
                              comp-interl2$extract4
                              comp-interl2$out-act0
                              comp-interl2$data-out))))

(defthm comp-interl2$extract5-lemma
  (implies (and (comp-interl2$input-format inputs data-size)
                (comp-interl2$valid-st st data-size)
                (comp-interl2$out-act1 inputs st data-size))
           (equal (list (comp-interl2$data-out inputs st data-size))
                  (nthcdr (1- (len (comp-interl2$extract5 st)))
                          (comp-interl2$extract5 st))))
  :hints (("Goal"
           :in-theory (enable comp-interl2$valid-st
                              comp-interl2$extract5
                              comp-interl2$out-act1
                              comp-interl2$data-out))))

;; Extract the accepted input sequences

(seq-gen comp-interl2 in0 in0-act 0
         (comp-interl2$data0-in inputs data-size))

(seq-gen comp-interl2 in1 in1-act 1
         (comp-interl2$data1-in inputs data-size))

(seq-gen comp-interl2 in2 in2-act 2
         (comp-interl2$data2-in inputs data-size))

(seq-gen comp-interl2 in3 in3-act 3
         (comp-interl2$data3-in inputs data-size))

;; Extract the valid output sequence

(seq-gen comp-interl2 out out-act 4
         (comp-interl2$data-out inputs st data-size)
         :netlist-data (nthcdr 5 outputs))

;; The multi-step input-output relationship

(defthmd comp-interl2$dataflow-correct
  (b* ((extracted0-st (comp-interl2$extract0 st))
       (extracted1-st (comp-interl2$extract1 st))
       (extracted2-st (comp-interl2$extract2 st))
       (extracted3-st (comp-interl2$extract3 st))
       (extracted4-st (comp-interl2$extract4 st))
       (extracted5-st (comp-interl2$extract5 st))
       (final-st (comp-interl2$run inputs-seq st data-size n))
       (final-extracted0-st (comp-interl2$extract0 final-st))
       (final-extracted1-st (comp-interl2$extract1 final-st))
       (final-extracted2-st (comp-interl2$extract2 final-st))
       (final-extracted3-st (comp-interl2$extract3 final-st))
       (final-extracted4-st (comp-interl2$extract4 final-st))
       (final-extracted5-st (comp-interl2$extract5 final-st)))
    (implies
     (and (comp-interl2$input-format-n inputs-seq data-size n)
          (comp-interl2$valid-st st data-size)
          (member x
                  (interleave2
                   (prepend-rec (interleave final-extracted0-st
                                            final-extracted1-st)
                                final-extracted4-st)
                   (prepend-rec (interleave final-extracted2-st
                                            final-extracted3-st)
                                final-extracted5-st))))
     (member
      (append x (comp-interl2$out-seq inputs-seq st data-size n))
      (interleave2
       (prepend-rec
        (interleave
         (append (comp-interl2$in0-seq inputs-seq st data-size n)
                 extracted0-st)
         (append (comp-interl2$in1-seq inputs-seq st data-size n)
                 extracted1-st))
        extracted4-st)
       (prepend-rec
        (interleave
         (append (comp-interl2$in2-seq inputs-seq st data-size n)
                 extracted2-st)
         (append (comp-interl2$in3-seq inputs-seq st data-size n)
                 extracted3-st))
        extracted5-st)))))
  :hints (("Goal" :in-theory (e/d (f-or
                                   member-of-true-list-list-is-true-list
                                   comp-interl2$out-act
                                   comp-interl2$interl0-out-act
                                   comp-interl2$interl1-out-act
                                   comp-interl2$extracted0-step
                                   comp-interl2$extracted1-step
                                   comp-interl2$extracted2-step
                                   comp-interl2$extracted3-step
                                   comp-interl2$extracted4-step
                                   comp-interl2$extracted5-step)
                                  (f-gates=b-gates
                                   zp-open
                                   member
                                   append
                                   prepend-rec
                                   take-of-too-many
                                   take)))))

(defthmd comp-interl2$functionally-correct
  (b* ((extracted0-st (comp-interl2$extract0 st))
       (extracted1-st (comp-interl2$extract1 st))
       (extracted2-st (comp-interl2$extract2 st))
       (extracted3-st (comp-interl2$extract3 st))
       (extracted4-st (comp-interl2$extract4 st))
       (extracted5-st (comp-interl2$extract5 st))
       (final-st (de-n (si 'comp-interl2 data-size) inputs-seq st netlist n))
       (final-extracted0-st (comp-interl2$extract0 final-st))
       (final-extracted1-st (comp-interl2$extract1 final-st))
       (final-extracted2-st (comp-interl2$extract2 final-st))
       (final-extracted3-st (comp-interl2$extract3 final-st))
       (final-extracted4-st (comp-interl2$extract4 final-st))
       (final-extracted5-st (comp-interl2$extract5 final-st)))
    (implies
     (and (comp-interl2& netlist data-size)
          (comp-interl2$input-format-n inputs-seq data-size n)
          (comp-interl2$valid-st st data-size)
          (member x
                  (interleave2
                   (prepend-rec (interleave final-extracted0-st
                                            final-extracted1-st)
                                final-extracted4-st)
                   (prepend-rec (interleave final-extracted2-st
                                            final-extracted3-st)
                                final-extracted5-st))))
     (member
      (append x (comp-interl2$out-seq-netlist
                 inputs-seq st netlist data-size n))
      (interleave2
       (prepend-rec
        (interleave
         (append (comp-interl2$in0-seq-netlist
                  inputs-seq st netlist data-size n)
                 extracted0-st)
         (append (comp-interl2$in1-seq-netlist
                  inputs-seq st netlist data-size n)
                 extracted1-st))
        extracted4-st)
       (prepend-rec
        (interleave
         (append (comp-interl2$in2-seq-netlist
                  inputs-seq st netlist data-size n)
                 extracted2-st)
         (append (comp-interl2$in3-seq-netlist
                  inputs-seq st netlist data-size n)
                 extracted3-st))
        extracted5-st)))))
  :hints (("Goal"
           :use comp-interl2$dataflow-correct
           :in-theory (enable comp-interl2$valid-st=>st-format
                              comp-interl2$de-n))))

;; Simulators for COMP-INTERL2

;; (progn
;;   (defun comp-interl2$map-to-links (st)
;;     (b* ((interl0 (nth *comp-interl2$interl0* st))
;;          (interl1 (nth *comp-interl2$interl1* st))
;;          (interl-ll (nth *comp-interl2$interl-ll* st)))
;;       (append (list (cons 'interl0 (interl$map-to-links interl0)))
;;               (list (cons 'interl1 (interl$map-to-links interl1)))
;;               (list (cons 'interl-ll (interl-ll$map-to-links interl-ll))))))

;;   (defun comp-interl2$map-to-links-list (x)
;;     (if (atom x)
;;         nil
;;       (cons (comp-interl2$map-to-links (car x))
;;             (comp-interl2$map-to-links-list (cdr x)))))

;;   (defund comp-interl2$st-gen (data-size)
;;     (declare (xargs :guard (natp data-size)))
;;     (b* ((interl0 (interl$st-gen data-size))
;;          (interl1 (interl$st-gen data-size))
;;          (interl-ll (interl-ll$st-gen data-size)))
;;       (list interl0 interl1 interl-ll)))

;;   (defund comp-interl2$ins-and-st-test (data-size n state)
;;     (declare (xargs :guard (and (natp data-size)
;;                                 (natp n))
;;                     :verify-guards nil
;;                     :stobjs state))
;;     (b* ((num-signals (comp-interl2$ins-len data-size))
;;          ((mv inputs-seq state)
;;           (signal-vals-gen num-signals n state nil))
;;          (st (comp-interl2$st-gen data-size)))
;;       (mv (and (comp-interl2$input-format-n inputs-seq data-size n)
;;                (comp-interl2$valid-st st data-size))
;;           state)))

;;   (local
;;    (defthm comp-interl2$ins-and-st-test-ok
;;      (comp-interl2$ins-and-st-test 4 10 state)))

;;   (defund comp-interl2$sim (data-size n state)
;;     (declare (xargs :guard (and (natp data-size)
;;                                 (natp n))
;;                     :verify-guards nil
;;                     :stobjs state))
;;     (b* ((num-signals (comp-interl2$ins-len data-size))
;;          ((mv inputs-seq state)
;;           (signal-vals-gen num-signals n state nil))
;;          (st (comp-interl2$st-gen data-size)))
;;       (mv (pretty-list
;;            (remove-dup-neighbors
;;             (comp-interl2$map-to-links-list
;;              (de-sim-trace (si 'comp-interl2 data-size)
;;                            inputs-seq
;;                            st
;;                            (comp-interl2$netlist data-size))))
;;            0)
;;           state)))

;;   (defund comp-interl2$in-out-sim (data-size n state)
;;     (declare (xargs :guard (and (natp data-size)
;;                                 (natp n))
;;                     :verify-guards nil
;;                     :stobjs state))
;;     (b* ((num-signals (comp-interl2$ins-len data-size))
;;          ((mv inputs-seq state)
;;           (signal-vals-gen num-signals n state nil))
;;          (st (comp-interl2$st-gen data-size)))
;;       (mv
;;        (append
;;         (list (cons 'in0-seq
;;                     (v-to-nat-lst
;;                      (comp-interl2$in0-seq inputs-seq st data-size n))))
;;         (list (cons 'in1-seq
;;                     (v-to-nat-lst
;;                      (comp-interl2$in1-seq inputs-seq st data-size n))))
;;         (list (cons 'in2-seq
;;                     (v-to-nat-lst
;;                      (comp-interl2$in2-seq inputs-seq st data-size n))))
;;         (list (cons 'in3-seq
;;                     (v-to-nat-lst
;;                      (comp-interl2$in3-seq inputs-seq st data-size n))))
;;         (list (cons 'out-seq
;;                     (v-to-nat-lst
;;                      (comp-interl2$out-seq inputs-seq st data-size n)))))
;;        state)))
;;   )
