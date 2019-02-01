;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; November 2018

(in-package "ADE")

(include-book "../link-joint")
(include-book "../vector-module")

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of Q2
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of Q2
;;
;; Construct a DE module generator for a queue of two links, Q2, using the
;; link-joint model.  Prove the value and state lemmas for this module
;; generator.

(defconst *queue2$go-num* 3)
(defconst *queue2$st-len* 2)

(defun queue2$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun queue2$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (queue2$data-ins-len data-width)
     *queue2$go-num*))

;; DE module generator of Q2

(module-generator
 queue2* (data-width)
 ;; MODULE'S NAME
 (si 'queue2 data-width)
 ;; INPUTS
 ;; There are 3 types of inputs for a complex joint:
 ;; * full-in and empty-out- signals,
 ;; * input data,
 ;; * GO signals.
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 data-width)
                                     (sis 'go 0 *queue2$go-num*)))
 ;; OUTPUTS
 ;; For a complex joint, in addition to outputing the data, we also report the
 ;; "act" signals from the joints at the module's input and output ports.
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-width))
 ;; INTERNAL STATE
 '(l0 l1)
 ;; OCCURRENCES
 ;; Our DE description of a self-timed module allows links and joints to appear
 ;; in any order in the module's occurrence list, except that LINKS MUST BE
 ;; DECLARED BEFORE JOINTS so that when the module is being evaluated, the "se"
 ;; function called in the first pass will extract the links' full/empty states
 ;; and data and provide these values as inputs for the corresponding joints;
 ;; the "de" function wil make the second pass to update the link's full/empty
 ;; states and data using the joints' output values calculated from the first
 ;; pass.
 (list
  ;; LINKS
  ;; L0
  (list 'l0
        (list* 'l0-status (sis 'd0-out 0 data-width))
        (si 'link data-width)
        (list* 'in-act 'trans-act (sis 'd0-in 0 data-width)))

  ;; L1
  (list 'l1
        (list* 'l1-status (sis 'd1-out 0 data-width))
        (si 'link data-width)
        (list* 'trans-act 'out-act (sis 'd1-in 0 data-width)))

  ;; JOINTS
  ;; In
  (list 'in-cntl
        '(in-act)
        'joint-cntl
        (list 'full-in 'l0-status (si 'go 0)))
  (list 'in-op
        (sis 'd0-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'data-in 0 data-width))

  ;; Transfer data
  (list 'trans-cntl
        '(trans-act)
        'joint-cntl
        (list 'l0-status 'l1-status (si 'go 1)))
  (list 'trans-op
        (sis 'd1-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'd0-out 0 data-width))

  ;; Out
  (list 'out-cntl
        '(out-act)
        'joint-cntl
        (list 'l1-status 'empty-out- (si 'go 2)))
  (list 'out-op
        (sis 'data-out 0 data-width)
        (si 'v-buf data-width)
        (sis 'd1-out 0 data-width)))

 (declare (xargs :guard (natp data-width))))

(make-event
 `(progn
    ,@(state-accessors-gen 'queue2 '(l0 l1) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of Q2.

(defund queue2$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (queue2* data-width)
        (union$ (link$netlist data-width)
                *joint-cntl*
                (v-buf$netlist data-width)
                :test 'equal)))

;; Recognizer for Q2

(defund queue2& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (b* ((subnetlist (delete-to-eq (si 'queue2 data-width) netlist)))
    (and (equal (assoc (si 'queue2 data-width) netlist)
                (queue2* data-width))
         (link& subnetlist data-width)
         (joint-cntl& subnetlist)
         (v-buf& subnetlist data-width))))

;; Sanity check

(local
 (defthmd check-queue2$netlist-64
   (and (net-syntax-okp (queue2$netlist 64))
        (net-arity-okp (queue2$netlist 64))
        (queue2& (queue2$netlist 64) 64))))

;; Constraints on the state of Q2

(defund queue2$st-format (st data-width)
  (b* ((l0 (get-field *queue2$l0* st))
       (l1 (get-field *queue2$l1* st)))
    (and (link$st-format l0 data-width)
         (link$st-format l1 data-width))))

(defthm queue2$st-format=>constraint
  (implies (queue2$st-format st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue2$st-format)))
  :rule-classes :forward-chaining)

(defund queue2$valid-st (st data-width)
  (b* ((l0 (get-field *queue2$l0* st))
       (l1 (get-field *queue2$l1* st)))
    (and (link$valid-st l0 data-width)
         (link$valid-st l1 data-width))))

(defthmd queue2$valid-st=>constraint
  (implies (queue2$valid-st st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue2$valid-st)))
  :rule-classes :forward-chaining)

(defthmd queue2$valid-st=>st-format
  (implies (queue2$valid-st st data-width)
           (queue2$st-format st data-width))
  :hints (("Goal" :in-theory (e/d (queue2$st-format
                                   queue2$valid-st)
                                  (link$st-format)))))

;; Extract the input and output signals for Q2

(progn
  ;; Extract the input data

  (defun queue2$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 2 inputs)))

  (defthm len-queue2$data-in
    (equal (len (queue2$data-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable queue2$data-in))

  ;; Extract the "in-act" signal

  (defund queue2$in-act (inputs st data-width)
    (b* ((full-in (nth 0 inputs))
         (go-signals (nthcdr (queue2$data-ins-len data-width) inputs))
         (go-in (nth 0 go-signals))

         (l0 (get-field *queue2$l0* st))
         (l0.s (get-field *link$s* l0)))
      (joint-act full-in (car l0.s) go-in)))

  (defthm queue2$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (queue2$in-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable queue2$in-act))))

  ;; Extract the "out-act" signal

  (defund queue2$out-act (inputs st data-width)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (queue2$data-ins-len data-width) inputs))
         (go-out (nth 2 go-signals))

         (l1 (get-field *queue2$l1* st))
         (l1.s (get-field *link$s* l1)))
      (joint-act (car l1.s) empty-out- go-out)))

  (defthm queue2$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (queue2$out-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable queue2$out-act))))

  ;; Extract the output data

  (defund queue2$data-out (st)
    (v-threefix (strip-cars (get-field *link$d*
                                       (get-field *queue2$l1* st)))))

  (defthm len-queue2$data-out-1
    (implies (queue2$st-format st data-width)
             (equal (len (queue2$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable queue2$st-format
                                       queue2$data-out))))

  (defthm len-queue2$data-out-2
    (implies (queue2$valid-st st data-width)
             (equal (len (queue2$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable queue2$valid-st
                                       queue2$data-out))))

  (defthm bvp-queue2$data-out
    (implies (and (queue2$valid-st st data-width)
                  (queue2$out-act inputs st data-width))
             (bvp (queue2$data-out st)))
    :hints (("Goal" :in-theory (enable queue2$valid-st
                                       queue2$out-act
                                       queue2$data-out))))

  (defun queue2$outputs (inputs st data-width)
    (list* (queue2$in-act inputs st data-width)
           (queue2$out-act inputs st data-width)
           (queue2$data-out st)))
  )

;; The value lemma for Q2

(defthm queue2$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (queue2& netlist data-width)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue2$go-num*)
                  (queue2$st-format st data-width))
             (equal (se (si 'queue2 data-width) inputs st netlist)
                    (queue2$outputs inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'queue2 data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue2&
                            queue2*$destructure
                            queue2$st-format
                            queue2$in-act
                            queue2$out-act
                            queue2$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of Q2, namely, the next states of two
;; links L0 and L1.

(defun queue2$step (inputs st data-width)
  (b* ((data-in    (queue2$data-in inputs data-width))
       (go-signals (nthcdr (queue2$data-ins-len data-width) inputs))

       (go-trans (nth 1 go-signals))

       (l0 (get-field *queue2$l0* st))
       (l0.s (get-field *link$s* l0))
       (l0.d (get-field *link$d* l0))
       (l1 (get-field *queue2$l1* st))
       (l1.s (get-field *link$s* l1))

       (in-act (queue2$in-act inputs st data-width))
       (out-act (queue2$out-act inputs st data-width))
       (trans-act (joint-act (car l0.s) (car l1.s) go-trans))

       (l0-inputs (list* in-act trans-act data-in))
       (l1-inputs (list* trans-act out-act (strip-cars l0.d))))
    (list
     ;; L0
     (link$step l0-inputs l0 data-width)
     ;; L1
     (link$step l1-inputs l1 data-width))))

(defthm len-of-queue2$step
  (equal (len (queue2$step inputs st data-width))
         *queue2$st-len*))

;; The state lemma for Q2

(defthm queue2$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (queue2& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue2$go-num*)
                  (queue2$st-format st data-width))
             (equal (de (si 'queue2 data-width) inputs st netlist)
                    (queue2$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'queue2 data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue2&
                            queue2*$destructure
                            queue2$st-format
                            queue2$data-in
                            queue2$in-act
                            queue2$out-act)
                           (de-module-disabled-rules)))))

(in-theory (disable queue2$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund queue2$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (queue2$data-in inputs data-width))
       (go-signals (nthcdr (queue2$data-ins-len data-width) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *queue2$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(defthm booleanp-queue2$in-act
  (implies (and (queue2$input-format inputs data-width)
                (queue2$valid-st st data-width))
           (booleanp (queue2$in-act inputs st data-width)))
  :hints (("Goal" :in-theory (enable queue2$input-format
                                     queue2$valid-st
                                     queue2$in-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-queue2$out-act
  (implies (and (queue2$input-format inputs data-width)
                (queue2$valid-st st data-width))
           (booleanp (queue2$out-act inputs st data-width)))
  :hints (("Goal" :in-theory (enable queue2$input-format
                                     queue2$valid-st
                                     queue2$out-act)))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma queue2)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for Q2 that extracts the future output sequence from
;; the current state.

(defund queue2$extract (st)
  (b* ((l0 (get-field *queue2$l0* st))
       (l1 (get-field *queue2$l1* st)))
    (extract-valid-data (list l0 l1))))

(defthm queue2$extract-not-empty
  (implies (and (queue2$out-act inputs st data-width)
                (queue2$valid-st st data-width))
           (< 0 (len (queue2$extract st))))
  :hints (("Goal"
           :in-theory (e/d (queue2$valid-st
                            queue2$extract
                            queue2$out-act)
                           ())))
  :rule-classes :linear)

;; The extracted next-state function for Q2.  Note that this function avoids
;; exploring the internal computation of Q2.

(defund queue2$extracted-step (inputs st data-width)
  (b* ((data (queue2$data-in inputs data-width))
       (extracted-st (queue2$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue2$out-act inputs st data-width) t)
      (cond
       ((equal (queue2$in-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue2$in-act inputs st data-width) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

;; This property characterizes the one-step update on the future output
;; sequence given the current inputs and current state.  The trick here is to
;; apply the extraction function queue2$extract to the step function
;; queue2$step so that the one-step update on the future output sequence can be
;; expressed in terms of the queue2$extracted-step function, which abstracts
;; away the internal computation of Q2.

(defthm queue2$extracted-step-correct
  (b* ((next-st (queue2$step inputs st data-width)))
    (implies (and (queue2$input-format inputs data-width)
                  (queue2$valid-st st data-width))
             (equal (queue2$extract next-st)
                    (queue2$extracted-step inputs st data-width))))
  :hints (("Goal"
           :in-theory (enable get-field
                              f-sr
                              queue2$extracted-step
                              queue2$input-format
                              queue2$valid-st
                              queue2$st-format
                              queue2$step
                              queue2$in-act
                              queue2$out-act
                              queue2$extract))))

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that queue2$valid-st is an invariant.

(defthm queue2$valid-st-preserved
  (implies (and (queue2$input-format inputs data-width)
                (queue2$valid-st st data-width))
           (queue2$valid-st (queue2$step inputs st data-width)
                            data-width))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            f-sr
                            queue2$input-format
                            queue2$valid-st
                            queue2$st-format
                            queue2$step
                            queue2$in-act
                            queue2$out-act)
                           (nfix)))))

(defthm queue2$extract-lemma
  (implies (and (queue2$valid-st st data-width)
                (queue2$out-act inputs st data-width))
           (equal (list (queue2$data-out st))
                  (nthcdr (1- (len (queue2$extract st)))
                          (queue2$extract st))))
  :hints (("Goal"
           :in-theory (enable queue2$valid-st
                              queue2$st-format
                              queue2$extract
                              queue2$out-act
                              queue2$data-out))))

;; Extract the accepted input sequence

(seq-gen queue2 in in-act 0
         (queue2$data-in inputs data-width))

;; Extract the valid output sequence

(seq-gen queue2 out out-act 1
         (queue2$data-out st)
         :netlist-data (nthcdr 2 outputs))

;; The multi-step input-output relationship

(in-out-stream-lemma queue2)

