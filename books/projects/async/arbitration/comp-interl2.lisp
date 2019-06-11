;; Copyright (C) 2019, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "interl2")

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "std/lists/sets" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of COMP-INTERL
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of COMP-INTERL
;;
;; Construct a DE module generator for circuits performing
;; first-come-first-served arbitrated merges.  Prove the value and state lemmas
;; for this module generator.

;; ->|
;;   |INTERL0 -L0->|
;; ->|             |
;;                 |INTERL2 ->
;; ->|             |
;;   |INTERL1 -L1->|
;; ->|

(defconst *comp-interl$select-num* (* 3 *interl$select-num*))
(defconst *comp-interl$go-num* (* 3 *interl$go-num*))

(defun comp-interl$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 5 (* 4 (mbe :logic (nfix data-size)
                 :exec  data-size))))

(defun comp-interl$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (comp-interl$data-ins-len data-size)
     *comp-interl$select-num*
     *comp-interl$go-num*))

;; DE module generator of COMP-INTERL

(module-generator
 comp-interl* (data-size)
 (si 'comp-interl data-size)
 (list* 'full-in0 'full-in1 'full-in2 'full-in3 'empty-out-
        (append (sis 'data0-in 0 data-size)
                (sis 'data1-in 0 data-size)
                (sis 'data2-in 0 data-size)
                (sis 'data3-in 0 data-size)
                (sis 'select 0 *comp-interl$select-num*)
                (sis 'go 0 *comp-interl$go-num*)))
 (list* 'in0-act 'in1-act 'in2-act 'in3-act 'out-act
        (sis 'data-out 0 data-size))
 '(l0 l1 interl0 interl1 interl2)
 (list
  ;; LINKS
  ;; L0
  (list 'l0
        (list* 'l0-status (sis 'd0-out 0 data-size))
        (si 'link data-size)
        (list* 'interl0-out-act 'interl2-in0-act (sis 'd0-in 0 data-size)))

  ;; L1
  (list 'l1
        (list* 'l1-status (sis 'd1-out 0 data-size))
        (si 'link data-size)
        (list* 'interl1-out-act 'interl2-in1-act (sis 'd1-in 0 data-size)))

  ;; JOINTS
  ;; INTERL0
  (list 'interl0
        (list* 'in0-act 'in1-act 'interl0-out-act
               (sis 'd0-in 0 data-size))
        (si 'interl data-size)
        (list* 'full-in0 'full-in1 'l0-status
               (append (sis 'data0-in 0 data-size)
                       (sis 'data1-in 0 data-size)
                       (cons (si 'select 0)
                             (sis 'go 0 *interl$go-num*)))))

  ;; INTERL1
  (list 'interl1
        (list* 'in2-act 'in3-act 'interl1-out-act
               (sis 'd1-in 0 data-size))
        (si 'interl data-size)
        (list* 'full-in2 'full-in3 'l1-status
               (append (sis 'data2-in 0 data-size)
                       (sis 'data3-in 0 data-size)
                       (cons (si 'select *interl$select-num*)
                             (sis 'go *interl$go-num* *interl$go-num*)))))

  ;; INTERL2
  (list 'interl2
        (list* 'interl2-in0-act 'interl2-in1-act 'out-act
               (sis 'data-out 0 data-size))
        (si 'interl data-size)
        (list* 'l0-status 'l1-status 'empty-out-
               (append (sis 'd0-out 0 data-size)
                       (sis 'd1-out 0 data-size)
                       (cons (si 'select (* 2 *interl$select-num*))
                             (sis 'go (* 2 *interl$go-num*) *interl$go-num*))))))

 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'comp-interl '(l0 l1 interl0 interl1 interl2) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; COMP-INTERL.

(defund comp-interl$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (comp-interl* data-size)
        (union$ (interl$netlist data-size)
                :test 'equal)))

;; Recognizer for COMP-INTERL

(defund comp-interl& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'comp-interl data-size) netlist)))
    (and (equal (assoc (si 'comp-interl data-size) netlist)
                (comp-interl* data-size))
         (link& subnetlist data-size)
         (interl& subnetlist data-size))))

;; Sanity check

(local
 (defthmd check-comp-interl$netlist-64
   (and (net-syntax-okp (comp-interl$netlist 64))
        (net-arity-okp (comp-interl$netlist 64))
        (comp-interl& (comp-interl$netlist 64) 64))))

;; Constraints on the state of COMP-INTERL

(defund comp-interl$st-format (st data-size)
  (b* ((l0 (nth *comp-interl$l0* st))
       (l1 (nth *comp-interl$l1* st))
       (interl0 (nth *comp-interl$interl0* st))
       (interl1 (nth *comp-interl$interl1* st))
       (interl2 (nth *comp-interl$interl2* st)))
    (and (< 0 data-size)
         (link$st-format l0 data-size)
         (link$st-format l1 data-size)
         (interl$st-format interl0 data-size)
         (interl$st-format interl1 data-size)
         (interl$st-format interl2 data-size))))

(defthm comp-interl$st-format=>constraint
  (implies (comp-interl$st-format st data-size)
           (posp data-size))
  :hints (("Goal" :in-theory (enable comp-interl$st-format)))
  :rule-classes :forward-chaining)

(defund comp-interl$valid-st (st data-size)
  (b* ((l0 (nth *comp-interl$l0* st))
       (l1 (nth *comp-interl$l1* st))
       (interl0 (nth *comp-interl$interl0* st))
       (interl1 (nth *comp-interl$interl1* st))
       (interl2 (nth *comp-interl$interl2* st)))
    (and (< 0 data-size)
         (link$valid-st l0 data-size)
         (link$valid-st l1 data-size)
         (interl$valid-st interl0 data-size)
         (interl$valid-st interl1 data-size)
         (interl$valid-st interl2 data-size))))

(defthmd comp-interl$valid-st=>constraint
  (implies (comp-interl$valid-st st data-size)
           (posp data-size))
  :hints (("Goal" :in-theory (enable comp-interl$valid-st)))
  :rule-classes :forward-chaining)

(defthmd comp-interl$valid-st=>st-format
  (implies (comp-interl$valid-st st data-size)
           (comp-interl$st-format st data-size))
  :hints (("Goal" :in-theory (e/d (interl$valid-st=>st-format
                                   comp-interl$st-format
                                   comp-interl$valid-st)
                                  (link$st-format)))))

;; Extract the input and output signals for COMP-INTERL

(progn
  ;; Extract the 1st input data item

  (defun comp-interl$data0-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (mbe :logic (nfix data-size)
               :exec  data-size)
          (nthcdr 5 inputs)))

  (defthm len-comp-interl$data0-in
    (equal (len (comp-interl$data0-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable comp-interl$data0-in))

  ;; Extract the 2nd input data item

  (defun comp-interl$data1-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (b* ((size (mbe :logic (nfix data-size)
                     :exec  data-size)))
      (take size
            (nthcdr (+ 5 size) inputs))))

  (defthm len-comp-interl$data1-in
    (equal (len (comp-interl$data1-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable comp-interl$data1-in))

  ;; Extract the 3rd input data item

  (defun comp-interl$data2-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (b* ((size (mbe :logic (nfix data-size)
                     :exec  data-size)))
      (take size
            (nthcdr (+ 5 (* 2 size)) inputs))))

  (defthm len-comp-interl$data2-in
    (equal (len (comp-interl$data2-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable comp-interl$data2-in))

  ;; Extract the 4th input data item

  (defun comp-interl$data3-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (b* ((size (mbe :logic (nfix data-size)
                     :exec  data-size)))
      (take size
            (nthcdr (+ 5 (* 3 size)) inputs))))

  (defthm len-comp-interl$data3-in
    (equal (len (comp-interl$data3-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable comp-interl$data3-in))

  ;; Extract the inputs for joint INTERL0

  (defund comp-interl$interl0-inputs (inputs st data-size)
    (b* ((full-in0 (nth 0 inputs))
         (full-in1 (nth 1 inputs))
         (data0-in (comp-interl$data0-in inputs data-size))
         (data1-in (comp-interl$data1-in inputs data-size))
         (select0  (nth (comp-interl$data-ins-len data-size) inputs))
         (go-signals (nthcdr (+ (comp-interl$data-ins-len data-size)
                                *comp-interl$select-num*)
                             inputs))

         (interl0-go-signals (take *interl$go-num* go-signals))

         (l0 (nth *comp-interl$l0* st))
         (l0.s (nth *link$s* l0)))
      (list* full-in0 full-in1 (f-buf (car l0.s))
             (append data0-in data1-in
                     (cons select0 interl0-go-signals)))))

  ;; Extract the "out-act0" signal for joint INTERL0

  (defund comp-interl$interl0-out-act0 (inputs st data-size)
    (b* ((interl0-inputs (comp-interl$interl0-inputs inputs st data-size))
         (interl0 (nth *comp-interl$interl0* st)))
      (interl$out-act0 interl0-inputs interl0 data-size)))

  ;; Extract the "out-act1" signal for joint INTERL0

  (defund comp-interl$interl0-out-act1 (inputs st data-size)
    (b* ((interl0-inputs (comp-interl$interl0-inputs inputs st data-size))
         (interl0 (nth *comp-interl$interl0* st)))
      (interl$out-act1 interl0-inputs interl0 data-size)))

  (defthm comp-interl$interl0-out-act-mutually-exclusive
    (implies (and (comp-interl$valid-st st data-size)
                  (comp-interl$interl0-out-act0 inputs st data-size))
             (not (comp-interl$interl0-out-act1 inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl$valid-st
                                       comp-interl$interl0-out-act0
                                       comp-interl$interl0-out-act1))))

  ;; Extract the "out-act" signal for joint INTERL0

  (defund comp-interl$interl0-out-act (inputs st data-size)
    (f-or (comp-interl$interl0-out-act0 inputs st data-size)
          (comp-interl$interl0-out-act1 inputs st data-size)))

  ;; Extract the output data from joint INTERL0

  (defund comp-interl$interl0-data-out (inputs st data-size)
    (b* ((interl0-inputs (comp-interl$interl0-inputs inputs st data-size))
         (interl0 (nth *comp-interl$interl0* st)))
      (interl$data-out interl0-inputs interl0 data-size)))

  ;; Extract the inputs for joint INTERL1

  (defund comp-interl$interl1-inputs (inputs st data-size)
    (b* ((full-in2 (nth 2 inputs))
         (full-in3 (nth 3 inputs))
         (data2-in (comp-interl$data2-in inputs data-size))
         (data3-in (comp-interl$data3-in inputs data-size))
         (select1  (nth (+ (comp-interl$data-ins-len data-size)
                           *interl$select-num*)
                        inputs))
         (go-signals (nthcdr (+ (comp-interl$data-ins-len data-size)
                                *comp-interl$select-num*)
                             inputs))

         (interl1-go-signals (take *interl$go-num*
                                   (nthcdr *interl$go-num* go-signals)))

         (l1 (nth *comp-interl$l1* st))
         (l1.s (nth *link$s* l1)))
      (list* full-in2 full-in3 (f-buf (car l1.s))
             (append data2-in data3-in
                     (cons select1 interl1-go-signals)))))

  ;; Extract the "out-act0" signal for joint INTERL1

  (defund comp-interl$interl1-out-act0 (inputs st data-size)
    (b* ((interl1-inputs (comp-interl$interl1-inputs inputs st data-size))
         (interl1 (nth *comp-interl$interl1* st)))
      (interl$out-act0 interl1-inputs interl1 data-size)))

  ;; Extract the "out-act1" signal for joint INTERL1

  (defund comp-interl$interl1-out-act1 (inputs st data-size)
    (b* ((interl1-inputs (comp-interl$interl1-inputs inputs st data-size))
         (interl1 (nth *comp-interl$interl1* st)))
      (interl$out-act1 interl1-inputs interl1 data-size)))

  (defthm comp-interl$interl1-out-act-mutually-exclusive
    (implies (and (comp-interl$valid-st st data-size)
                  (comp-interl$interl1-out-act0 inputs st data-size))
             (not (comp-interl$interl1-out-act1 inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl$valid-st
                                       comp-interl$interl1-out-act0
                                       comp-interl$interl1-out-act1))))

  ;; Extract the "out-act" signal for joint INTERL1

  (defund comp-interl$interl1-out-act (inputs st data-size)
    (f-or (comp-interl$interl1-out-act0 inputs st data-size)
          (comp-interl$interl1-out-act1 inputs st data-size)))

  ;; Extract the output data from joint INTERL1

  (defund comp-interl$interl1-data-out (inputs st data-size)
    (b* ((interl1-inputs (comp-interl$interl1-inputs inputs st data-size))
         (interl1 (nth *comp-interl$interl1* st)))
      (interl$data-out interl1-inputs interl1 data-size)))

  ;; Extract the inputs for joint INTERL2

  (defund comp-interl$interl2-inputs (inputs st data-size)
    (b* ((empty-out- (nth 4 inputs))
         (select2 (nth (+ (comp-interl$data-ins-len data-size)
                          (* 2 *interl$select-num*))
                       inputs))
         (go-signals (nthcdr (+ (comp-interl$data-ins-len data-size)
                                *comp-interl$select-num*)
                             inputs))

         (interl2-go-signals (take *interl$go-num*
                                   (nthcdr (* 2 *interl$go-num*) go-signals)))

         (l0 (nth *comp-interl$l0* st))
         (l0.s (nth *link$s* l0))
         (l0.d (nth *link$d* l0))
         (l1 (nth *comp-interl$l1* st))
         (l1.s (nth *link$s* l1))
         (l1.d (nth *link$d* l1)))
      (list* (f-buf (car l0.s)) (f-buf (car l1.s)) empty-out-
             (append (v-threefix (strip-cars l0.d))
                     (v-threefix (strip-cars l1.d))
                     (cons select2 interl2-go-signals)))))

  ;; Extract the "in0-act" signal

  (defund comp-interl$in0-act (inputs st data-size)
    (b* ((interl0-inputs (comp-interl$interl0-inputs inputs st data-size))
         (interl0 (nth *comp-interl$interl0* st)))
      (interl$in0-act interl0-inputs interl0 data-size)))

  (defthm comp-interl$in0-act-inactive
    (implies (not (nth 0 inputs))
             (not (comp-interl$in0-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl$interl0-inputs
                                       comp-interl$in0-act))))

  ;; Extract the "in1-act" signal

  (defund comp-interl$in1-act (inputs st data-size)
    (b* ((interl0-inputs (comp-interl$interl0-inputs inputs st data-size))
         (interl0 (nth *comp-interl$interl0* st)))
      (interl$in1-act interl0-inputs interl0 data-size)))

  (defthm comp-interl$in1-act-inactive
    (implies (not (nth 1 inputs))
             (not (comp-interl$in1-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl$interl0-inputs
                                       comp-interl$in1-act))))

  ;; Extract the "in2-act" signal

  (defund comp-interl$in2-act (inputs st data-size)
    (b* ((interl1-inputs (comp-interl$interl1-inputs inputs st data-size))
         (interl1 (nth *comp-interl$interl1* st)))
      (interl$in0-act interl1-inputs interl1 data-size)))

  (defthm comp-interl$in2-act-inactive
    (implies (not (nth 2 inputs))
             (not (comp-interl$in2-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl$interl1-inputs
                                       comp-interl$in2-act))))

  ;; Extract the "in3-act" signal

  (defund comp-interl$in3-act (inputs st data-size)
    (b* ((interl1-inputs (comp-interl$interl1-inputs inputs st data-size))
         (interl1 (nth *comp-interl$interl1* st)))
      (interl$in1-act interl1-inputs interl1 data-size)))

  (defthm comp-interl$in3-act-inactive
    (implies (not (nth 3 inputs))
             (not (comp-interl$in3-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl$interl1-inputs
                                       comp-interl$in3-act))))

  ;; Extract the "out-act0" signal

  (defund comp-interl$out-act0 (inputs st data-size)
    (b* ((interl2-inputs (comp-interl$interl2-inputs inputs st data-size))
         (interl2 (nth *comp-interl$interl2* st)))
      (interl$out-act0 interl2-inputs interl2 data-size)))

  (defthm comp-interl$out-act0-inactive
    (implies (equal (nth 4 inputs) t)
             (not (comp-interl$out-act0 inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl$interl2-inputs
                                       comp-interl$out-act0))))

  ;; Extract the "out-act1" signal

  (defund comp-interl$out-act1 (inputs st data-size)
    (b* ((interl2-inputs (comp-interl$interl2-inputs inputs st data-size))
         (interl2 (nth *comp-interl$interl2* st)))
      (interl$out-act1 interl2-inputs interl2 data-size)))

  (defthm comp-interl$out-act1-inactive
    (implies (equal (nth 4 inputs) t)
             (not (comp-interl$out-act1 inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl$interl2-inputs
                                       comp-interl$out-act1))))

  (defthm comp-interl$out-act-mutually-exclusive
    (implies (and (comp-interl$valid-st st data-size)
                  (comp-interl$out-act0 inputs st data-size))
             (not (comp-interl$out-act1 inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl$valid-st
                                       comp-interl$out-act0
                                       comp-interl$out-act1))))

  ;; Extract the "out-act" signal

  (defund comp-interl$out-act (inputs st data-size)
    (f-or (comp-interl$out-act0 inputs st data-size)
          (comp-interl$out-act1 inputs st data-size)))

  (defthm comp-interl$out-act-inactive
    (implies (equal (nth 4 inputs) t)
             (not (comp-interl$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl$out-act))))

  ;; Extract the output data

  (defund comp-interl$data-out (inputs st data-size)
    (b* ((interl2-inputs (comp-interl$interl2-inputs inputs st data-size))
         (interl2 (nth *comp-interl$interl2* st)))
      (interl$data-out interl2-inputs interl2 data-size)))

  (defthm len-comp-interl$data-out-1
    (implies (comp-interl$st-format st data-size)
             (equal (len (comp-interl$data-out inputs st data-size))
                    data-size))
    :hints (("Goal" :in-theory (enable comp-interl$st-format
                                       comp-interl$data-out))))

  (defthm len-comp-interl$data-out-2
    (implies (comp-interl$valid-st st data-size)
             (equal (len (comp-interl$data-out inputs st data-size))
                    data-size))
    :hints (("Goal" :in-theory (enable comp-interl$valid-st
                                       comp-interl$data-out))))

  (defun comp-interl$outputs (inputs st data-size)
    (list* (comp-interl$in0-act inputs st data-size)
           (comp-interl$in1-act inputs st data-size)
           (comp-interl$in2-act inputs st data-size)
           (comp-interl$in3-act inputs st data-size)
           (comp-interl$out-act inputs st data-size)
           (comp-interl$data-out inputs st data-size)))
  )

;; The value lemma for COMP-INTERL

(defthm comp-interl$value
  (b* ((inputs (list* full-in0 full-in1 full-in2 full-in3 empty-out-
                      (append data0-in data1-in data2-in data3-in
                              selects go-signals))))
    (implies (and (comp-interl& netlist data-size)
                  (true-listp data0-in)
                  (equal (len data0-in) data-size)
                  (true-listp data1-in)
                  (equal (len data1-in) data-size)
                  (true-listp data2-in)
                  (equal (len data2-in) data-size)
                  (true-listp data3-in)
                  (equal (len data3-in) data-size)
                  (true-listp selects)
                  (equal (len selects) *comp-interl$select-num*)
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-interl$go-num*)
                  (comp-interl$st-format st data-size))
             (equal (se (si 'comp-interl data-size) inputs st netlist)
                    (comp-interl$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'comp-interl data-size)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            comp-interl&
                            comp-interl*$destructure
                            comp-interl$st-format
                            interl$out-act
                            comp-interl$data0-in
                            comp-interl$data1-in
                            comp-interl$data2-in
                            comp-interl$data3-in
                            comp-interl$interl0-inputs
                            comp-interl$interl1-inputs
                            comp-interl$interl2-inputs
                            comp-interl$in0-act
                            comp-interl$in1-act
                            comp-interl$in2-act
                            comp-interl$in3-act
                            comp-interl$out-act0
                            comp-interl$out-act1
                            comp-interl$out-act
                            comp-interl$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of COMP-INTERL.

(defun comp-interl$step (inputs st data-size)
  (b* ((l0 (nth *comp-interl$l0* st))
       (l1 (nth *comp-interl$l1* st))
       (interl0 (nth *comp-interl$interl0* st))
       (interl1 (nth *comp-interl$interl1* st))
       (interl2 (nth *comp-interl$interl2* st))

       (interl0-inputs (comp-interl$interl0-inputs inputs st data-size))
       (interl1-inputs (comp-interl$interl1-inputs inputs st data-size))
       (interl2-inputs (comp-interl$interl2-inputs inputs st data-size))

       (interl0-out-act (interl$out-act interl0-inputs interl0 data-size))
       (interl1-out-act (interl$out-act interl1-inputs interl1 data-size))
       (interl2-in0-act (interl$in0-act interl2-inputs interl2 data-size))
       (interl2-in1-act (interl$in1-act interl2-inputs interl2 data-size))

       (d0-in (interl$data-out interl0-inputs interl0 data-size))
       (d1-in (interl$data-out interl1-inputs interl1 data-size))

       (l0-inputs (list* interl0-out-act interl2-in0-act d0-in))
       (l1-inputs (list* interl1-out-act interl2-in1-act d1-in)))
    (list
     ;; L0
     (link$step l0-inputs l0 data-size)
     ;; L1
     (link$step l1-inputs l1 data-size)
     ;; Joint INTERL0
     (interl$step interl0-inputs interl0 data-size)
     ;; Joint INTERL1
     (interl$step interl1-inputs interl1 data-size)
     ;; Joint INTERL2
     (interl$step interl2-inputs interl2 data-size))))

;; The state lemma for COMP-INTERL

(defthm comp-interl$state
  (b* ((inputs (list* full-in0 full-in1 full-in2 full-in3 empty-out-
                      (append data0-in data1-in data2-in data3-in
                              selects go-signals))))
    (implies (and (comp-interl& netlist data-size)
                  (true-listp data0-in)
                  (equal (len data0-in) data-size)
                  (true-listp data1-in)
                  (equal (len data1-in) data-size)
                  (true-listp data2-in)
                  (equal (len data2-in) data-size)
                  (true-listp data3-in)
                  (equal (len data3-in) data-size)
                  (true-listp selects)
                  (equal (len selects) *comp-interl$select-num*)
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-interl$go-num*)
                  (comp-interl$st-format st data-size))
             (equal (de (si 'comp-interl data-size) inputs st netlist)
                    (comp-interl$step inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'comp-interl data-size)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            comp-interl&
                            comp-interl*$destructure
                            comp-interl$st-format
                            comp-interl$data0-in
                            comp-interl$data1-in
                            comp-interl$data2-in
                            comp-interl$data3-in
                            comp-interl$interl0-inputs
                            comp-interl$interl1-inputs
                            comp-interl$interl2-inputs)
                           (de-module-disabled-rules)))))

(in-theory (disable comp-interl$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund comp-interl$input-format (inputs data-size)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-size))))
  (b* ((full-in0   (nth 0 inputs))
       (full-in1   (nth 1 inputs))
       (full-in2   (nth 2 inputs))
       (full-in3   (nth 3 inputs))
       (empty-out- (nth 4 inputs))
       (data0-in   (comp-interl$data0-in inputs data-size))
       (data1-in   (comp-interl$data1-in inputs data-size))
       (data2-in   (comp-interl$data2-in inputs data-size))
       (data3-in   (comp-interl$data3-in inputs data-size))
       (selects    (take *comp-interl$select-num*
                         (nthcdr (comp-interl$data-ins-len data-size)
                                 inputs)))
       (go-signals (nthcdr (+ (comp-interl$data-ins-len data-size)
                              *comp-interl$select-num*)
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
     (= (len selects) *comp-interl$select-num*)
     (true-listp go-signals)
     (= (len go-signals) *comp-interl$go-num*)
     (equal inputs
            (list* full-in0 full-in1 full-in2 full-in3 empty-out-
                   (append data0-in data1-in data2-in data3-in
                           selects go-signals))))))

(local
 (defthm comp-interl$input-format=>interl0$input-format
   (implies (and (comp-interl$input-format inputs data-size)
                 (comp-interl$valid-st st data-size))
            (interl$input-format
             (comp-interl$interl0-inputs inputs st data-size)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (open-nth
                             interl$input-format
                             interl$data0-in
                             interl$data1-in
                             comp-interl$input-format
                             comp-interl$valid-st
                             comp-interl$interl0-inputs)
                            ())))))

(local
 (defthm comp-interl$input-format=>interl1$input-format
   (implies (and (comp-interl$input-format inputs data-size)
                 (comp-interl$valid-st st data-size))
            (interl$input-format
             (comp-interl$interl1-inputs inputs st data-size)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (open-nth
                             interl$input-format
                             interl$data0-in
                             interl$data1-in
                             comp-interl$input-format
                             comp-interl$valid-st
                             comp-interl$interl1-inputs)
                            ())))))

(local
 (defthm comp-interl$input-format=>interl2$input-format
   (implies (and (comp-interl$input-format inputs data-size)
                 (comp-interl$valid-st st data-size))
            (interl$input-format
             (comp-interl$interl2-inputs inputs st data-size)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (open-nth
                             interl$input-format
                             interl$data0-in
                             interl$data1-in
                             comp-interl$input-format
                             comp-interl$valid-st
                             comp-interl$interl2-inputs)
                            ())))))

(defthm booleanp-comp-interl$in0-act
  (implies (and (comp-interl$input-format inputs data-size)
                (comp-interl$valid-st st data-size))
           (booleanp (comp-interl$in0-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (enable comp-interl$valid-st
                              comp-interl$in0-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-interl$in1-act
  (implies (and (comp-interl$input-format inputs data-size)
                (comp-interl$valid-st st data-size))
           (booleanp (comp-interl$in1-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (enable comp-interl$valid-st
                              comp-interl$in1-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-interl$in2-act
  (implies (and (comp-interl$input-format inputs data-size)
                (comp-interl$valid-st st data-size))
           (booleanp (comp-interl$in2-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (enable comp-interl$valid-st
                              comp-interl$in2-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-interl$in3-act
  (implies (and (comp-interl$input-format inputs data-size)
                (comp-interl$valid-st st data-size))
           (booleanp (comp-interl$in3-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (enable comp-interl$valid-st
                              comp-interl$in3-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-interl$out-act0
  (implies (and (comp-interl$input-format inputs data-size)
                (comp-interl$valid-st st data-size))
           (booleanp (comp-interl$out-act0 inputs st data-size)))
  :hints (("Goal"
           :in-theory (enable comp-interl$valid-st
                              comp-interl$out-act0)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-interl$out-act1
  (implies (and (comp-interl$input-format inputs data-size)
                (comp-interl$valid-st st data-size))
           (booleanp (comp-interl$out-act1 inputs st data-size)))
  :hints (("Goal"
           :in-theory (enable comp-interl$valid-st
                              comp-interl$out-act1)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-interl$out-act
  (implies (and (comp-interl$input-format inputs data-size)
                (comp-interl$valid-st st data-size))
           (booleanp (comp-interl$out-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (e/d (comp-interl$out-act)
                           ())))
  :rule-classes (:rewrite :type-prescription))

(encapsulate
  ()

  (local
   (defthm comp-interl$out-act-rewrite
     (equal (comp-interl$out-act inputs st data-size)
            (b* ((interl2-inputs
                  (comp-interl$interl2-inputs inputs st data-size))
                 (interl2 (nth *comp-interl$interl2* st)))
              (interl$out-act interl2-inputs interl2 data-size)))
     :hints (("Goal" :in-theory (enable interl$out-act
                                        comp-interl$out-act0
                                        comp-interl$out-act1
                                        comp-interl$out-act)))))

  (defthm bvp-comp-interl$data-out
    (implies (and (comp-interl$input-format inputs data-size)
                  (comp-interl$valid-st st data-size)
                  (comp-interl$out-act inputs st data-size))
             (bvp (comp-interl$data-out inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-interl$valid-st
                                       comp-interl$data-out))))
  )

(simulate-lemma comp-interl)

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

;; The extraction functions for COMP-INTERL

(defund comp-interl$extract0 (st)
  (b* ((interl0 (nth *comp-interl$interl0* st)))
    (interl$extract0 interl0)))

(defund comp-interl$extract1 (st)
  (b* ((interl0 (nth *comp-interl$interl0* st)))
    (interl$extract1 interl0)))

(defund comp-interl$extract2 (st)
  (b* ((interl1 (nth *comp-interl$interl1* st)))
    (interl$extract0 interl1)))

(defund comp-interl$extract3 (st)
  (b* ((interl1 (nth *comp-interl$interl1* st)))
    (interl$extract1 interl1)))

(defund comp-interl$extract4 (st)
  (b* ((l0 (nth *comp-interl$l0* st))
       (interl2 (nth *comp-interl$interl2* st)))
    (append (extract-valid-data (list l0))
            (interl$extract0 interl2))))

(defund comp-interl$extract5 (st)
  (b* ((l1 (nth *comp-interl$l1* st))
       (interl2 (nth *comp-interl$interl2* st)))
    (append (extract-valid-data (list l1))
            (interl$extract1 interl2))))

(defthm comp-interl$extract0-not-empty
  (implies (and (comp-interl$interl0-out-act0 inputs st data-size)
                (comp-interl$valid-st st data-size))
           (< 0 (len (comp-interl$extract0 st))))
  :hints (("Goal"
           :in-theory (e/d (comp-interl$interl0-out-act0
                            comp-interl$valid-st
                            comp-interl$extract0)
                           ())))
  :rule-classes :linear)

(defthm comp-interl$extract1-not-empty
  (implies (and (comp-interl$interl0-out-act1 inputs st data-size)
                (comp-interl$valid-st st data-size))
           (< 0 (len (comp-interl$extract1 st))))
  :hints (("Goal"
           :in-theory (e/d (comp-interl$interl0-out-act1
                            comp-interl$valid-st
                            comp-interl$extract1)
                           ())))
  :rule-classes :linear)

(defthm comp-interl$extract2-not-empty
  (implies (and (comp-interl$interl1-out-act0 inputs st data-size)
                (comp-interl$valid-st st data-size))
           (< 0 (len (comp-interl$extract2 st))))
  :hints (("Goal"
           :in-theory (e/d (comp-interl$interl1-out-act0
                            comp-interl$valid-st
                            comp-interl$extract2)
                           ())))
  :rule-classes :linear)

(defthm comp-interl$extract3-not-empty
  (implies (and (comp-interl$interl1-out-act1 inputs st data-size)
                (comp-interl$valid-st st data-size))
           (< 0 (len (comp-interl$extract3 st))))
  :hints (("Goal"
           :in-theory (e/d (comp-interl$interl1-out-act1
                            comp-interl$valid-st
                            comp-interl$extract3)
                           ())))
  :rule-classes :linear)

(defthm comp-interl$extract4-not-empty
  (implies (and (comp-interl$out-act0 inputs st data-size)
                (comp-interl$valid-st st data-size))
           (< 0 (len (comp-interl$extract4 st))))
  :hints (("Goal"
           :in-theory (e/d (comp-interl$out-act0
                            comp-interl$valid-st
                            comp-interl$extract4)
                           ())))
  :rule-classes :linear)

(defthm comp-interl$extract5-not-empty
  (implies (and (comp-interl$out-act1 inputs st data-size)
                (comp-interl$valid-st st data-size))
           (< 0 (len (comp-interl$extract5 st))))
  :hints (("Goal"
           :in-theory (e/d (comp-interl$out-act1
                            comp-interl$valid-st
                            comp-interl$extract5)
                           ())))
  :rule-classes :linear)

;; The extracted next-state functions for COMP-INTERL.  Note that these
;; functions avoid exploring the internal computation of COMP-INTERL.

(defund comp-interl$extracted0-step (inputs st data-size)
  (b* ((data (comp-interl$data0-in inputs data-size))
       (extracted-st (comp-interl$extract0 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-interl$interl0-out-act0 inputs st data-size) t)
      (cond
       ((equal (comp-interl$in0-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (comp-interl$in0-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

(defund comp-interl$extracted1-step (inputs st data-size)
  (b* ((data (comp-interl$data1-in inputs data-size))
       (extracted-st (comp-interl$extract1 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-interl$interl0-out-act1 inputs st data-size) t)
      (cond
       ((equal (comp-interl$in1-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (comp-interl$in1-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

(defund comp-interl$extracted2-step (inputs st data-size)
  (b* ((data (comp-interl$data2-in inputs data-size))
       (extracted-st (comp-interl$extract2 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-interl$interl1-out-act0 inputs st data-size) t)
      (cond
       ((equal (comp-interl$in2-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (comp-interl$in2-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

(defund comp-interl$extracted3-step (inputs st data-size)
  (b* ((data (comp-interl$data3-in inputs data-size))
       (extracted-st (comp-interl$extract3 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-interl$interl1-out-act1 inputs st data-size) t)
      (cond
       ((equal (comp-interl$in3-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (comp-interl$in3-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

(defund comp-interl$extracted4-step (inputs st data-size)
  (b* ((data (comp-interl$interl0-data-out inputs st data-size))
       (extracted-st (comp-interl$extract4 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-interl$out-act0 inputs st data-size) t)
      (cond
       ((equal (comp-interl$interl0-out-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (comp-interl$interl0-out-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

(defund comp-interl$extracted5-step (inputs st data-size)
  (b* ((data (comp-interl$interl1-data-out inputs st data-size))
       (extracted-st (comp-interl$extract5 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-interl$out-act1 inputs st data-size) t)
      (cond
       ((equal (comp-interl$interl1-out-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (comp-interl$interl1-out-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm comp-interl$extracted0+1-step-correct-aux-1
     (equal (interl$data0-in (comp-interl$interl0-inputs inputs st data-size)
                             data-size)
            (comp-interl$data0-in inputs data-size))
     :hints (("Goal" :in-theory (enable comp-interl$interl0-inputs
                                        interl$data0-in)))))

  (local
   (defthm comp-interl$extracted0+1-step-correct-aux-2
     (equal (interl$data1-in (comp-interl$interl0-inputs inputs st data-size)
                             data-size)
            (comp-interl$data1-in inputs data-size))
     :hints (("Goal" :in-theory (enable comp-interl$interl0-inputs
                                        comp-interl$data1-in
                                        interl$data1-in)))))

  (defthm comp-interl$extracted0+1-step-correct
    (b* ((next-st (comp-interl$step inputs st data-size)))
      (implies
       (and (comp-interl$input-format inputs data-size)
            (comp-interl$valid-st st data-size))
       (and (equal (comp-interl$extract0 next-st)
                   (comp-interl$extracted0-step inputs st data-size))
            (equal (comp-interl$extract1 next-st)
                   (comp-interl$extracted1-step inputs st data-size)))))
    :hints (("Goal"
             :in-theory (e/d (interl$extracted0-step
                              interl$extracted1-step
                              comp-interl$extracted0-step
                              comp-interl$extracted1-step
                              comp-interl$valid-st
                              comp-interl$step
                              comp-interl$interl0-out-act0
                              comp-interl$interl0-out-act1
                              comp-interl$in0-act
                              comp-interl$in1-act
                              comp-interl$extract0
                              comp-interl$extract1)
                             (link$valid-st
                              link$step)))))

  (local
   (defthm comp-interl$extracted2+3-step-correct-aux-1
     (equal (interl$data0-in (comp-interl$interl1-inputs inputs st data-size)
                             data-size)
            (comp-interl$data2-in inputs data-size))
     :hints (("Goal" :in-theory (enable comp-interl$interl1-inputs
                                        interl$data0-in)))))

  (local
   (defthm comp-interl$extracted2+3-step-correct-aux-2
     (equal (interl$data1-in (comp-interl$interl1-inputs inputs st data-size)
                             data-size)
            (comp-interl$data3-in inputs data-size))
     :hints (("Goal" :in-theory (enable comp-interl$interl1-inputs
                                        comp-interl$data3-in
                                        interl$data1-in)))))

  (defthm comp-interl$extracted2+3-step-correct
    (b* ((next-st (comp-interl$step inputs st data-size)))
      (implies
       (and (comp-interl$input-format inputs data-size)
            (comp-interl$valid-st st data-size))
       (and (equal (comp-interl$extract2 next-st)
                   (comp-interl$extracted2-step inputs st data-size))
            (equal (comp-interl$extract3 next-st)
                   (comp-interl$extracted3-step inputs st data-size)))))
    :hints (("Goal"
             :in-theory (e/d (interl$extracted0-step
                              interl$extracted1-step
                              comp-interl$extracted2-step
                              comp-interl$extracted3-step
                              comp-interl$valid-st
                              comp-interl$step
                              comp-interl$interl1-out-act0
                              comp-interl$interl1-out-act1
                              comp-interl$in2-act
                              comp-interl$in3-act
                              comp-interl$extract2
                              comp-interl$extract3)
                             (link$valid-st
                              link$step)))))

  (local
   (defthm comp-interl$extracted4+5-step-correct-aux-1
     (b* ((l0 (nth *comp-interl$l0* st))
          (l0.d (nth *link$d* l0))
          (interl2-inputs (comp-interl$interl2-inputs inputs st data-size)))
       (implies (and (natp data-size)
                     (equal data-size (len l0.d)))
                (equal (interl$data0-in interl2-inputs data-size)
                       (v-threefix (strip-cars l0.d)))))
     :hints (("Goal" :in-theory (enable comp-interl$interl2-inputs
                                        interl$data0-in)))))

  (local
   (defthm comp-interl$extracted4+5-step-correct-aux-2
     (b* ((l0 (nth *comp-interl$l0* st))
          (l0.d (nth *link$d* l0))
          (l1 (nth *comp-interl$l1* st))
          (l1.d (nth *link$d* l1))
          (interl2-inputs (comp-interl$interl2-inputs inputs st data-size)))
       (implies (and (natp data-size)
                     (equal data-size (len l0.d))
                     (equal data-size (len l1.d)))
                (equal (interl$data1-in interl2-inputs data-size)
                       (v-threefix (strip-cars l1.d)))))
     :hints (("Goal" :in-theory (enable comp-interl$interl2-inputs
                                        interl$data1-in)))))

  (local
   (defthm comp-interl$interl0-out-act-inactive
     (implies (equal (nth *link$s*
                          (nth *comp-interl$l0* st))
                     '(t))
              (and (not (interl$out-act0
                         (comp-interl$interl0-inputs inputs st data-size)
                         (nth *comp-interl$interl0* st)
                         data-size))
                   (not (interl$out-act1
                         (comp-interl$interl0-inputs inputs st data-size)
                         (nth *comp-interl$interl0* st)
                         data-size))))
     :hints (("Goal"
              :in-theory (e/d (comp-interl$interl0-inputs)
                              ())))))

  (local
   (defthm comp-interl$interl1-out-act-inactive
     (implies (equal (nth *link$s*
                          (nth *comp-interl$l1* st))
                     '(t))
              (and (not (interl$out-act0
                         (comp-interl$interl1-inputs inputs st data-size)
                         (nth *comp-interl$interl1* st)
                         data-size))
                   (not (interl$out-act1
                         (comp-interl$interl1-inputs inputs st data-size)
                         (nth *comp-interl$interl1* st)
                         data-size))))
     :hints (("Goal"
              :in-theory (e/d (comp-interl$interl1-inputs)
                              ())))))

  (local
   (defthm comp-interl$interl2-in0-act-inactive
     (implies (equal (nth *link$s*
                          (nth *comp-interl$l0* st))
                     '(nil))
              (not (interl$in0-act
                    (comp-interl$interl2-inputs inputs st data-size)
                    (nth *comp-interl$interl2* st)
                    data-size)))
     :hints (("Goal"
              :in-theory (e/d (comp-interl$interl2-inputs)
                              ())))))

  (local
   (defthm comp-interl$interl2-in1-act-inactive
     (implies (equal (nth *link$s*
                          (nth *comp-interl$l1* st))
                     '(nil))
              (not (interl$in1-act
                    (comp-interl$interl2-inputs inputs st data-size)
                    (nth *comp-interl$interl2* st)
                    data-size)))
     :hints (("Goal"
              :in-theory (e/d (comp-interl$interl2-inputs)
                              ())))))

  (defthm comp-interl$extracted4+5-step-correct
    (b* ((next-st (comp-interl$step inputs st data-size)))
      (implies
       (and (comp-interl$input-format inputs data-size)
            (comp-interl$valid-st st data-size))
       (and (equal (comp-interl$extract4 next-st)
                   (comp-interl$extracted4-step inputs st data-size))
            (equal (comp-interl$extract5 next-st)
                   (comp-interl$extracted5-step inputs st data-size)))))
    :hints (("Goal"
             :use (comp-interl$input-format=>interl0$input-format
                   comp-interl$input-format=>interl1$input-format
                   comp-interl$input-format=>interl2$input-format)
             :in-theory (e/d (f-sr
                              interl$out-act
                              interl$extracted0-step
                              interl$extracted1-step
                              comp-interl$extracted4-step
                              comp-interl$extracted5-step
                              comp-interl$valid-st
                              comp-interl$step
                              comp-interl$interl0-out-act0
                              comp-interl$interl0-out-act1
                              comp-interl$interl0-out-act
                              comp-interl$interl0-data-out
                              comp-interl$interl1-out-act0
                              comp-interl$interl1-out-act1
                              comp-interl$interl1-out-act
                              comp-interl$interl1-data-out
                              comp-interl$out-act0
                              comp-interl$out-act1
                              comp-interl$extract4
                              comp-interl$extract5)
                             (comp-interl$input-format=>interl0$input-format
                              comp-interl$input-format=>interl1$input-format
                              comp-interl$input-format=>interl2$input-format
                              b-or)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that comp-interl$valid-st is an invariant.

(encapsulate
  ()

  (local
   (defthm comp-interl$valid-st-preserved-aux-1
     (implies (and (equal (nth 2 inputs2) (nth 0 inputs1))
                   (booleanp (nth 2 inputs2)))
              (not (and (interl$out-act inputs2 st2 data-size2)
                        (interl$in0-act inputs1 st1 data-size1))))
     :hints (("Goal" :cases ((nth 2 inputs2))))))

  (local
   (defthm comp-interl$valid-st-preserved-aux-2
     (implies (and (equal (nth 2 inputs2) (nth 1 inputs1))
                   (booleanp (nth 2 inputs2)))
              (not (and (interl$out-act inputs2 st2 data-size2)
                        (interl$in1-act inputs1 st1 data-size1))))
     :hints (("Goal" :cases ((nth 2 inputs2))))))

  (local
   (defthm comp-interl$valid-st-preserved-aux-3
     (implies (link$valid-st st data-size)
              (booleanp (car (nth *link$s* st))))
     :rule-classes (:rewrite :type-prescription)))

  (defthm comp-interl$valid-st-preserved
    (implies (and (comp-interl$input-format inputs data-size)
                  (comp-interl$valid-st st data-size))
             (comp-interl$valid-st (comp-interl$step inputs st data-size)
                                   data-size))
    :hints (("Goal"
             :use (comp-interl$input-format=>interl0$input-format
                   comp-interl$input-format=>interl1$input-format
                   comp-interl$input-format=>interl2$input-format)
             :in-theory (e/d (comp-interl$valid-st
                              comp-interl$step
                              comp-interl$interl0-inputs
                              comp-interl$interl1-inputs
                              comp-interl$interl2-inputs)
                             (comp-interl$input-format=>interl0$input-format
                              comp-interl$input-format=>interl1$input-format
                              comp-interl$input-format=>interl2$input-format
                              link$valid-st
                              link$step
                              nfix)))))
  )

(defthm comp-interl$extract0-lemma
  (implies
   (and (comp-interl$input-format inputs data-size)
        (comp-interl$valid-st st data-size)
        (comp-interl$interl0-out-act0 inputs st data-size))
   (equal (list (comp-interl$interl0-data-out inputs st data-size))
          (nthcdr (1- (len (comp-interl$extract0 st)))
                  (comp-interl$extract0 st))))
  :hints (("Goal"
           :in-theory (enable comp-interl$valid-st
                              comp-interl$extract0
                              comp-interl$interl0-out-act0
                              comp-interl$interl0-data-out))))

(defthm comp-interl$extract1-lemma
  (implies
   (and (comp-interl$input-format inputs data-size)
        (comp-interl$valid-st st data-size)
        (comp-interl$interl0-out-act1 inputs st data-size))
   (equal (list (comp-interl$interl0-data-out inputs st data-size))
          (nthcdr (1- (len (comp-interl$extract1 st)))
                  (comp-interl$extract1 st))))
  :hints (("Goal"
           :in-theory (enable comp-interl$valid-st
                              comp-interl$extract1
                              comp-interl$interl0-out-act1
                              comp-interl$interl0-data-out))))

(defthm comp-interl$extract2-lemma
  (implies
   (and (comp-interl$input-format inputs data-size)
        (comp-interl$valid-st st data-size)
        (comp-interl$interl1-out-act0 inputs st data-size))
   (equal (list (comp-interl$interl1-data-out inputs st data-size))
          (nthcdr (1- (len (comp-interl$extract2 st)))
                  (comp-interl$extract2 st))))
  :hints (("Goal"
           :in-theory (enable comp-interl$valid-st
                              comp-interl$extract2
                              comp-interl$interl1-out-act0
                              comp-interl$interl1-data-out))))

(defthm comp-interl$extract3-lemma
  (implies
   (and (comp-interl$input-format inputs data-size)
        (comp-interl$valid-st st data-size)
        (comp-interl$interl1-out-act1 inputs st data-size))
   (equal (list (comp-interl$interl1-data-out inputs st data-size))
          (nthcdr (1- (len (comp-interl$extract3 st)))
                  (comp-interl$extract3 st))))
  :hints (("Goal"
           :in-theory (enable comp-interl$valid-st
                              comp-interl$extract3
                              comp-interl$interl1-out-act1
                              comp-interl$interl1-data-out))))

(defthm comp-interl$extract4-lemma
  (implies (and (comp-interl$input-format inputs data-size)
                (comp-interl$valid-st st data-size)
                (comp-interl$out-act0 inputs st data-size))
           (equal (list (comp-interl$data-out inputs st data-size))
                  (nthcdr (1- (len (comp-interl$extract4 st)))
                          (comp-interl$extract4 st))))
  :hints (("Goal"
           :in-theory (enable comp-interl$valid-st
                              comp-interl$extract4
                              comp-interl$out-act0
                              comp-interl$data-out))))

(defthm comp-interl$extract5-lemma
  (implies (and (comp-interl$input-format inputs data-size)
                (comp-interl$valid-st st data-size)
                (comp-interl$out-act1 inputs st data-size))
           (equal (list (comp-interl$data-out inputs st data-size))
                  (nthcdr (1- (len (comp-interl$extract5 st)))
                          (comp-interl$extract5 st))))
  :hints (("Goal"
           :in-theory (enable comp-interl$valid-st
                              comp-interl$extract5
                              comp-interl$out-act1
                              comp-interl$data-out))))

;; Extract the accepted input sequences

(seq-gen comp-interl in0 in0-act 0
         (comp-interl$data0-in inputs data-size))

(seq-gen comp-interl in1 in1-act 1
         (comp-interl$data1-in inputs data-size))

(seq-gen comp-interl in2 in2-act 2
         (comp-interl$data2-in inputs data-size))

(seq-gen comp-interl in3 in3-act 3
         (comp-interl$data3-in inputs data-size))

;; Extract the valid output sequence

(seq-gen comp-interl out out-act 4
         (comp-interl$data-out inputs st data-size)
         :netlist-data (nthcdr 5 outputs))

;; The multi-step input-output relationship

(defthmd comp-interl$dataflow-correct
  (b* ((extracted0-st (comp-interl$extract0 st))
       (extracted1-st (comp-interl$extract1 st))
       (extracted2-st (comp-interl$extract2 st))
       (extracted3-st (comp-interl$extract3 st))
       (extracted4-st (comp-interl$extract4 st))
       (extracted5-st (comp-interl$extract5 st))
       (final-st (comp-interl$run inputs-seq st data-size n))
       (final-extracted0-st (comp-interl$extract0 final-st))
       (final-extracted1-st (comp-interl$extract1 final-st))
       (final-extracted2-st (comp-interl$extract2 final-st))
       (final-extracted3-st (comp-interl$extract3 final-st))
       (final-extracted4-st (comp-interl$extract4 final-st))
       (final-extracted5-st (comp-interl$extract5 final-st)))
    (implies
     (and (comp-interl$input-format-n inputs-seq data-size n)
          (comp-interl$valid-st st data-size)
          (member x
                  (interleave2
                   (prepend-rec (interleave final-extracted0-st
                                            final-extracted1-st)
                                final-extracted4-st)
                   (prepend-rec (interleave final-extracted2-st
                                            final-extracted3-st)
                                final-extracted5-st))))
     (member
      (append x (comp-interl$out-seq inputs-seq st data-size n))
      (interleave2
       (prepend-rec
        (interleave
         (append (comp-interl$in0-seq inputs-seq st data-size n)
                 extracted0-st)
         (append (comp-interl$in1-seq inputs-seq st data-size n)
                 extracted1-st))
        extracted4-st)
       (prepend-rec
        (interleave
         (append (comp-interl$in2-seq inputs-seq st data-size n)
                 extracted2-st)
         (append (comp-interl$in3-seq inputs-seq st data-size n)
                 extracted3-st))
        extracted5-st)))))
  :hints (("Goal" :in-theory (e/d (f-or
                                   member-of-true-list-list-is-true-list
                                   comp-interl$out-act
                                   comp-interl$interl0-out-act
                                   comp-interl$interl1-out-act
                                   comp-interl$extracted0-step
                                   comp-interl$extracted1-step
                                   comp-interl$extracted2-step
                                   comp-interl$extracted3-step
                                   comp-interl$extracted4-step
                                   comp-interl$extracted5-step)
                                  (f-gates=b-gates
                                   zp-open
                                   member
                                   append
                                   prepend-rec
                                   take-of-too-many)))))

(defthmd comp-interl$functionally-correct
  (b* ((extracted0-st (comp-interl$extract0 st))
       (extracted1-st (comp-interl$extract1 st))
       (extracted2-st (comp-interl$extract2 st))
       (extracted3-st (comp-interl$extract3 st))
       (extracted4-st (comp-interl$extract4 st))
       (extracted5-st (comp-interl$extract5 st))
       (final-st (de-n (si 'comp-interl data-size) inputs-seq st netlist n))
       (final-extracted0-st (comp-interl$extract0 final-st))
       (final-extracted1-st (comp-interl$extract1 final-st))
       (final-extracted2-st (comp-interl$extract2 final-st))
       (final-extracted3-st (comp-interl$extract3 final-st))
       (final-extracted4-st (comp-interl$extract4 final-st))
       (final-extracted5-st (comp-interl$extract5 final-st)))
    (implies
     (and (comp-interl& netlist data-size)
          (comp-interl$input-format-n inputs-seq data-size n)
          (comp-interl$valid-st st data-size)
          (member x
                  (interleave2
                   (prepend-rec (interleave final-extracted0-st
                                            final-extracted1-st)
                                final-extracted4-st)
                   (prepend-rec (interleave final-extracted2-st
                                            final-extracted3-st)
                                final-extracted5-st))))
     (member
      (append x (comp-interl$out-seq-netlist
                 inputs-seq st netlist data-size n))
      (interleave2
       (prepend-rec
        (interleave
         (append (comp-interl$in0-seq-netlist
                  inputs-seq st netlist data-size n)
                 extracted0-st)
         (append (comp-interl$in1-seq-netlist
                  inputs-seq st netlist data-size n)
                 extracted1-st))
        extracted4-st)
       (prepend-rec
        (interleave
         (append (comp-interl$in2-seq-netlist
                  inputs-seq st netlist data-size n)
                 extracted2-st)
         (append (comp-interl$in3-seq-netlist
                  inputs-seq st netlist data-size n)
                 extracted3-st))
        extracted5-st)))))
  :hints (("Goal"
           :use comp-interl$dataflow-correct
           :in-theory (enable comp-interl$valid-st=>st-format
                              comp-interl$de-n))))
