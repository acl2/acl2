;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "../link-joint")
(include-book "../store-n")
(include-book "../vector-module")

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of QUEUE5-L
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of QUEUE5-L
;;
;; Construct a DE module generator for a queue of 5 links, QUEUE5-L, using the
;; link-joint model.  Prove the value and state lemmas for this module
;; generator.  Note that QUEUE5-L is a complex link.

(defconst *queue5-l$go-num* 4)

(defun queue5-l$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (mbe :logic (nfix data-size)
            :exec  data-size)))

(defun queue5-l$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (queue5-l$data-ins-len data-size)
     *queue5-l$go-num*))

;; DE module generator of QUEUE5-L

(module-generator
 queue5-l* (data-size)
 (si 'queue5-l data-size)
 ;; INPUTS
 ;; There are 3 types of inputs for a complex link:
 ;; * in-act and out-act signals,
 ;; * input data,
 ;; * GO signals.
 (list* 'in-act 'out-act (append (sis 'data-in 0 data-size)
                                 (sis 'go 0 *queue5-l$go-num*)))
 ;; OUTPUTS
 ;; For a complex link, in addition to outputing the data, we also report the
 ;; "ready-in-" signals from the links at the module's input ports and the
 ;; "ready-out" signals from the links at the module's output ports.
 (list* 'ready-in- 'ready-out
        (sis 'data-out 0 data-size))
 '(l0 l1 l2 l3 l4)
 (list
  ;; LINKS
  ;; L0
  (list 'l0
        (list* 'l0-status (sis 'd0-out 0 data-size))
        (si 'link data-size)
        (list* 'in-act 'trans1-act (sis 'data-in 0 data-size)))

  ;; L1
  (list 'l1
        (list* 'l1-status (sis 'd1-out 0 data-size))
        (si 'link data-size)
        (list* 'trans1-act 'trans2-act (sis 'd1-in 0 data-size)))

  ;; L2
  (list 'l2
        (list* 'l2-status (sis 'd2-out 0 data-size))
        (si 'link data-size)
        (list* 'trans2-act 'trans3-act (sis 'd2-in 0 data-size)))

  ;; L3
  (list 'l3
        (list* 'l3-status (sis 'd3-out 0 data-size))
        (si 'link data-size)
        (list* 'trans3-act 'trans4-act (sis 'd3-in 0 data-size)))

  ;; L4
  (list 'l4
        (list* 'l4-status (sis 'data-out 0 data-size))
        (si 'link data-size)
        (list* 'trans4-act 'out-act (sis 'd4-in 0 data-size)))

  ;; JOINTS
  ;; Transfer data1
  (list 'trans1-cntl
        '(trans1-act)
        'joint-cntl
        (list 'l0-status 'l1-status (si 'go 0)))
  (list 'trans1-op
        (sis 'd1-in 0 data-size)
        (si 'v-buf data-size)
        (sis 'd0-out 0 data-size))

  ;; Transfer data2
  (list 'trans2-cntl
        '(trans2-act)
        'joint-cntl
        (list 'l1-status 'l2-status (si 'go 1)))
  (list 'trans2-op
        (sis 'd2-in 0 data-size)
        (si 'v-buf data-size)
        (sis 'd1-out 0 data-size))

  ;; Transfer data3
  (list 'trans3-cntl
        '(trans3-act)
        'joint-cntl
        (list 'l2-status 'l3-status (si 'go 2)))
  (list 'trans3-op
        (sis 'd3-in 0 data-size)
        (si 'v-buf data-size)
        (sis 'd2-out 0 data-size))

  ;; Transfer data4
  (list 'trans4-cntl
        '(trans4-act)
        'joint-cntl
        (list 'l3-status 'l4-status (si 'go 3)))
  (list 'trans4-op
        (sis 'd4-in 0 data-size)
        (si 'v-buf data-size)
        (sis 'd3-out 0 data-size))

  ;; STATUS
  '(in-status (ready-in-) wire (l0-status))
  '(out-status (ready-out) wire (l4-status)))

 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'queue5-l '(l0 l1 l2 l3 l4) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; QUEUE5-L.

(defund queue5-l$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (queue5-l* data-size)
        (union$ (link$netlist data-size)
                *joint-cntl*
                (v-buf$netlist data-size)
                :test 'equal)))

;; Recognizer for QUEUE5-L

(defund queue5-l& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'queue5-l data-size) netlist)))
    (and (equal (assoc (si 'queue5-l data-size) netlist)
                (queue5-l* data-size))
         (link& subnetlist data-size)
         (joint-cntl& subnetlist)
         (v-buf& subnetlist data-size))))

;; Sanity check

(local
 (defthmd check-queue5-l$netlist-64
   (and (net-syntax-okp (queue5-l$netlist 64))
        (net-arity-okp (queue5-l$netlist 64))
        (queue5-l& (queue5-l$netlist 64) 64))))

;; Constraints on the state of QUEUE5-L

(defund queue5-l$st-format (st data-size)
  (b* ((l0 (nth *queue5-l$l0* st))
       (l1 (nth *queue5-l$l1* st))
       (l2 (nth *queue5-l$l2* st))
       (l3 (nth *queue5-l$l3* st))
       (l4 (nth *queue5-l$l4* st)))
    (and (link$st-format l0 data-size)
         (link$st-format l1 data-size)
         (link$st-format l2 data-size)
         (link$st-format l3 data-size)
         (link$st-format l4 data-size))))

(defthm queue5-l$st-format=>constraint
  (implies (queue5-l$st-format st data-size)
           (natp data-size))
  :hints (("Goal" :in-theory (enable queue5-l$st-format)))
  :rule-classes :forward-chaining)

(defund queue5-l$valid-st (st data-size)
  (b* ((l0 (nth *queue5-l$l0* st))
       (l1 (nth *queue5-l$l1* st))
       (l2 (nth *queue5-l$l2* st))
       (l3 (nth *queue5-l$l3* st))
       (l4 (nth *queue5-l$l4* st)))
    (and (link$valid-st l0 data-size)
         (link$valid-st l1 data-size)
         (link$valid-st l2 data-size)
         (link$valid-st l3 data-size)
         (link$valid-st l4 data-size))))

(defthmd queue5-l$valid-st=>constraint
  (implies (queue5-l$valid-st st data-size)
           (natp data-size))
  :hints (("Goal" :in-theory (enable queue5-l$valid-st)))
  :rule-classes :forward-chaining)

(defthmd queue5-l$valid-st=>st-format
  (implies (queue5-l$valid-st st data-size)
           (queue5-l$st-format st data-size))
  :hints (("Goal" :in-theory (e/d (queue5-l$st-format
                                   queue5-l$valid-st)
                                  (link$st-format)))))

;; Extract the input and output signals for QUEUE5-L

(progn
  ;; Extract the "in-act" signal

  (defund queue5-l$in-act (inputs)
    (nth 0 inputs))

  ;; Extract the "out-act" signal

  (defund queue5-l$out-act (inputs)
    (nth 1 inputs))

  ;; Extract the input data

  (defun queue5-l$data-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (mbe :logic (nfix data-size)
               :exec  data-size)
          (nthcdr 2 inputs)))

  (defthm len-queue5-l$data-in
    (equal (len (queue5-l$data-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable queue5-l$data-in))

  ;; Extract the "ready-in-" signal

  (defund queue5-l$ready-in- (st)
    (b* ((l0 (nth *queue5-l$l0* st))
         (l0.s (nth *link$s* l0)))
      (f-buf (car l0.s))))

  (defthm booleanp-queue5-l$ready-in-
    (implies (queue5-l$valid-st st data-size)
             (booleanp (queue5-l$ready-in- st)))
    :hints (("Goal" :in-theory (enable queue5-l$valid-st
                                       queue5-l$ready-in-)))
    :rule-classes (:rewrite :type-prescription))

  ;; Extract the "ready-out" signal

  (defund queue5-l$ready-out (st)
    (b* ((l4 (nth *queue5-l$l4* st))
         (l4.s (nth *link$s* l4)))
      (f-buf (car l4.s))))

  (defthm booleanp-queue5-l$ready-out
    (implies (queue5-l$valid-st st data-size)
             (booleanp (queue5-l$ready-out st)))
    :hints (("Goal" :in-theory (enable queue5-l$valid-st
                                       queue5-l$ready-out)))
    :rule-classes (:rewrite :type-prescription))

  ;; Extract the output data

  (defund queue5-l$data-out (st)
    (v-threefix (strip-cars (nth *link$d*
                                 (nth *queue5-l$l4* st)))))

  (defthm v-threefix-of-queue5-l$data-out-canceled
    (equal (v-threefix (queue5-l$data-out st))
           (queue5-l$data-out st))
    :hints (("Goal" :in-theory (enable queue5-l$data-out))))

  (defthm len-queue5-l$data-out-1
    (implies (queue5-l$st-format st data-size)
             (equal (len (queue5-l$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable queue5-l$st-format
                                       queue5-l$data-out))))

  (defthm len-queue5-l$data-out-2
    (implies (queue5-l$valid-st st data-size)
             (equal (len (queue5-l$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable queue5-l$valid-st
                                       queue5-l$data-out))))

  (defthm bvp-queue5-l$data-out
    (implies (and (queue5-l$valid-st st data-size)
                  (queue5-l$ready-out st))
             (bvp (queue5-l$data-out st)))
    :hints (("Goal" :in-theory (enable queue5-l$valid-st
                                       queue5-l$ready-out
                                       queue5-l$data-out))))

  (defun queue5-l$outputs (inputs st data-size)
    (declare (ignore inputs data-size))
    (list* (queue5-l$ready-in- st)
           (queue5-l$ready-out st)
           (queue5-l$data-out st)))
  )

;; The value lemma for QUEUE5-L

(defthm queue5-l$value
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue5-l& netlist data-size)
                  (queue5-l$st-format st data-size))
             (equal (se (si 'queue5-l data-size) inputs st netlist)
                    (queue5-l$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'queue5-l data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue5-l&
                            queue5-l*$destructure
                            queue5-l$st-format
                            queue5-l$ready-in-
                            queue5-l$ready-out
                            queue5-l$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of QUEUE5-L.

(defun queue5-l$step (inputs st data-size)
  (b* ((in-act     (queue5-l$in-act inputs))
       (out-act    (queue5-l$out-act inputs))
       (data-in    (queue5-l$data-in inputs data-size))
       (go-signals (nthcdr (queue5-l$data-ins-len data-size) inputs))

       (go-trans1 (nth 0 go-signals))
       (go-trans2 (nth 1 go-signals))
       (go-trans3 (nth 2 go-signals))
       (go-trans4 (nth 3 go-signals))

       (l0 (nth *queue5-l$l0* st))
       (l0.s (nth *link$s* l0))
       (l0.d (nth *link$d* l0))
       (l1 (nth *queue5-l$l1* st))
       (l1.s (nth *link$s* l1))
       (l1.d (nth *link$d* l1))
       (l2 (nth *queue5-l$l2* st))
       (l2.s (nth *link$s* l2))
       (l2.d (nth *link$d* l2))
       (l3 (nth *queue5-l$l3* st))
       (l3.s (nth *link$s* l3))
       (l3.d (nth *link$d* l3))
       (l4 (nth *queue5-l$l4* st))
       (l4.s (nth *link$s* l4))

       (trans1-act (joint-act (car l0.s) (car l1.s) go-trans1))
       (trans2-act (joint-act (car l1.s) (car l2.s) go-trans2))
       (trans3-act (joint-act (car l2.s) (car l3.s) go-trans3))
       (trans4-act (joint-act (car l3.s) (car l4.s) go-trans4))

       (l0-inputs (list* in-act trans1-act data-in))
       (l1-inputs (list* trans1-act trans2-act
                         (fv-if in-act data-in (strip-cars l0.d))))
       (l2-inputs (list* trans2-act trans3-act (strip-cars l1.d)))
       (l3-inputs (list* trans3-act trans4-act (strip-cars l2.d)))
       (l4-inputs (list* trans4-act out-act (strip-cars l3.d))))
    (list
     ;; L0
     (link$step l0-inputs l0 data-size)
     ;; L1
     (link$step l1-inputs l1 data-size)
     ;; L2
     (link$step l2-inputs l2 data-size)
     ;; L3
     (link$step l3-inputs l3 data-size)
     ;; L4
     (link$step l4-inputs l4 data-size))))

(defthm queue5-l$step-v-threefix-of-data-in-canceled
  (implies
   (and (true-listp data-in)
        (equal (len data-in) data-size))
   (equal (queue5-l$step (list* in-act out-act
                                (append (v-threefix data-in) go-signals))
                         st
                         data-size)
          (queue5-l$step (list* in-act out-act
                                (append data-in go-signals))
                         st
                         data-size)))
  :hints (("Goal" :in-theory (enable queue5-l$step
                                     queue5-l$data-in
                                     queue5-l$in-act
                                     queue5-l$out-act))))

;; The state lemma for QUEUE5-L

(defthm queue5-l$state
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue5-l& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue5-l$go-num*)
                  (queue5-l$st-format st data-size))
             (equal (de (si 'queue5-l data-size) inputs st netlist)
                    (queue5-l$step inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'queue5-l data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue5-l&
                            queue5-l*$destructure
                            queue5-l$st-format
                            queue5-l$in-act
                            queue5-l$out-act
                            queue5-l$data-in)
                           (de-module-disabled-rules)))))

(in-theory (disable queue5-l$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund queue5-l$input-format (inputs st data-size)
  (b* ((in-act     (queue5-l$in-act inputs))
       (out-act    (queue5-l$out-act inputs))
       (data-in    (queue5-l$data-in inputs data-size))
       (go-signals (nthcdr (queue5-l$data-ins-len data-size) inputs))

       (ready-in- (queue5-l$ready-in- st))
       (ready-out (queue5-l$ready-out st)))
    (and
     (if ready-in-
         (not in-act)
       (booleanp in-act))
     (if (not ready-out)
         (not out-act)
       (booleanp out-act))
     (or (not in-act) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *queue5-l$go-num*)
     (equal inputs
            (list* in-act out-act (append data-in go-signals))))))

(defthm booleanp-queue5-l$in-act
  (implies (queue5-l$input-format inputs st data-size)
           (booleanp (queue5-l$in-act inputs)))
  :hints (("Goal" :in-theory (enable queue5-l$input-format
                                     queue5-l$in-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-queue5-l$out-act
  (implies (queue5-l$input-format inputs st data-size)
           (booleanp (queue5-l$out-act inputs)))
  :hints (("Goal" :in-theory (enable queue5-l$input-format
                                     queue5-l$out-act)))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma queue5-l :clink t)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for QUEUE5-L that extracts the future output
;; sequence from the current state.

(defund queue5-l$extract (st)
  (b* ((l0 (nth *queue5-l$l0* st))
       (l1 (nth *queue5-l$l1* st))
       (l2 (nth *queue5-l$l2* st))
       (l3 (nth *queue5-l$l3* st))
       (l4 (nth *queue5-l$l4* st)))
    (extract-valid-data (list l0 l1 l2 l3 l4))))

(defthm queue5-l$extract-not-empty
  (implies (and (queue5-l$ready-out st)
                (queue5-l$valid-st st data-size))
           (< 0 (len (queue5-l$extract st))))
  :hints (("Goal" :in-theory (e/d (queue5-l$valid-st
                                   queue5-l$extract
                                   queue5-l$ready-out)
                                  ())))
  :rule-classes :linear)

;; The extracted next-state function for QUEUE5-L.  Note that this function
;; avoids exploring the internal computation of QUEUE5-L.

(defund queue5-l$extracted-step (inputs st data-size)
  (b* ((data (queue5-l$data-in inputs data-size))
       (extracted-st (queue5-l$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue5-l$out-act inputs) t)
      (cond
       ((equal (queue5-l$in-act inputs) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue5-l$in-act inputs) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(defthm queue5-l$extracted-step-correct
  (b* ((next-st (queue5-l$step inputs st data-size)))
    (implies (and (queue5-l$input-format inputs st data-size)
                  (queue5-l$valid-st st data-size))
             (equal (queue5-l$extract next-st)
                    (queue5-l$extracted-step inputs st data-size))))
  :hints (("Goal"
           :in-theory (enable f-sr
                              queue5-l$extracted-step
                              queue5-l$input-format
                              queue5-l$valid-st
                              queue5-l$step
                              queue5-l$ready-in-
                              queue5-l$ready-out
                              queue5-l$extract))))

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that queue5-l$valid-st is an invariant.

(defthm queue5-l$valid-st-preserved
  (implies (and (queue5-l$input-format inputs st data-size)
                (queue5-l$valid-st st data-size))
           (queue5-l$valid-st (queue5-l$step inputs st data-size)
                            data-size))
  :hints (("Goal"
           :in-theory (e/d (f-sr
                            queue5-l$input-format
                            queue5-l$valid-st
                            queue5-l$step
                            queue5-l$ready-in-
                            queue5-l$ready-out)
                           ()))))

(defthm queue5-l$extract-lemma-1
  (implies (and (queue5-l$input-format inputs st data-size)
                (queue5-l$valid-st st data-size)
                (queue5-l$out-act inputs))
           (equal (list (queue5-l$data-out st))
                  (nthcdr (1- (len (queue5-l$extract st)))
                          (queue5-l$extract st))))
  :hints (("Goal"
           :in-theory (enable queue5-l$input-format
                              queue5-l$valid-st
                              queue5-l$extract
                              queue5-l$out-act
                              queue5-l$ready-out
                              queue5-l$data-out))))

(defthmd queue5-l$extract-lemma-2
  (implies (and (queue5-l$valid-st st data-size)
                (queue5-l$ready-out st))
           (equal (list (queue5-l$data-out st))
                  (nthcdr (1- (len (queue5-l$extract st)))
                          (queue5-l$extract st))))
  :hints (("Goal"
           :in-theory (enable queue5-l$valid-st
                              queue5-l$extract
                              queue5-l$ready-out
                              queue5-l$data-out))))

;; Extract the accepted input sequence

(seq-gen queue5-l in in-act -1
         (queue5-l$data-in inputs data-size)
         :clink t)

;; Extract the valid output sequence

(seq-gen queue5-l out out-act -1
         (queue5-l$data-out st)
         :netlist-data (nthcdr 2 outputs)
         :clink t)

;; The multi-step input-output relationship

(in-out-stream-lemma queue5-l :clink t)

