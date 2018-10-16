;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2018

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
(defconst *queue5-l$st-len* 5)

(defun queue5-l$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun queue5-l$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (queue5-l$data-ins-len data-width)
     *queue5-l$go-num*))

;; DE module generator of QUEUE5-L

(module-generator
 queue5-l* (data-width)
 (si 'queue5-l data-width)
 ;; INPUTS
 ;; There are 3 types of inputs for a complex link:
 ;; * in-act and out-act signals,
 ;; * input data,
 ;; * GO signals.
 (list* 'in-act 'out-act (append (sis 'data-in 0 data-width)
                                 (sis 'go 0 *queue5-l$go-num*)))
 ;; OUTPUTS
 ;; For a complex link, in addition to outputing the data, we also report the
 ;; "ready-in-" signals from the links at the module's input ports and the
 ;; "ready-out" signals from the links at the module's output ports.
 (list* 'ready-in- 'ready-out
        (sis 'data-out 0 data-width))
 '(l0 l1 l2 l3 l4)
 (list
  ;; LINKS
  ;; L0
  (list 'l0
        (list* 'l0-status (sis 'd0-out 0 data-width))
        (si 'link data-width)
        (list* 'in-act 'trans1-act (sis 'data-in 0 data-width)))

  ;; L1
  (list 'l1
        (list* 'l1-status (sis 'd1-out 0 data-width))
        (si 'link data-width)
        (list* 'trans1-act 'trans2-act (sis 'd1-in 0 data-width)))

  ;; L2
  (list 'l2
        (list* 'l2-status (sis 'd2-out 0 data-width))
        (si 'link data-width)
        (list* 'trans2-act 'trans3-act (sis 'd2-in 0 data-width)))

  ;; L3
  (list 'l3
        (list* 'l3-status (sis 'd3-out 0 data-width))
        (si 'link data-width)
        (list* 'trans3-act 'trans4-act (sis 'd3-in 0 data-width)))

  ;; L4
  (list 'l4
        (list* 'l4-status (sis 'data-out 0 data-width))
        (si 'link data-width)
        (list* 'trans4-act 'out-act (sis 'd4-in 0 data-width)))

  ;; JOINTS
  ;; Transfer data1
  (list 'trans1-cntl
        '(trans1-act)
        'joint-cntl
        (list 'l0-status 'l1-status (si 'go 0)))
  (list 'trans1-op
        (sis 'd1-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'd0-out 0 data-width))

  ;; Transfer data2
  (list 'trans2-cntl
        '(trans2-act)
        'joint-cntl
        (list 'l1-status 'l2-status (si 'go 1)))
  (list 'trans2-op
        (sis 'd2-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'd1-out 0 data-width))

  ;; Transfer data3
  (list 'trans3-cntl
        '(trans3-act)
        'joint-cntl
        (list 'l2-status 'l3-status (si 'go 2)))
  (list 'trans3-op
        (sis 'd3-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'd2-out 0 data-width))

  ;; Transfer data4
  (list 'trans4-cntl
        '(trans4-act)
        'joint-cntl
        (list 'l3-status 'l4-status (si 'go 3)))
  (list 'trans4-op
        (sis 'd4-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'd3-out 0 data-width))

  ;; STATUS
  '(in-status (ready-in-) b-buf (l0-status))
  '(out-status (ready-out) b-buf (l4-status)))

 :guard (natp data-width))

(make-event
 `(progn
    ,@(state-accessors-gen 'queue5-l '(l0 l1 l2 l3 l4) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; QUEUE5-L.

(defun queue5-l$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (queue5-l* data-width)
        (union$ (link$netlist data-width)
                *joint-cntl*
                (v-buf$netlist data-width)
                :test 'equal)))

;; Recognizer for QUEUE5-L

(defund queue5-l& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (and (equal (assoc (si 'queue5-l data-width) netlist)
              (queue5-l* data-width))
       (b* ((netlist (delete-to-eq (si 'queue5-l data-width) netlist)))
         (and (link& netlist data-width)
              (joint-cntl& netlist)
              (v-buf& netlist data-width)))))

;; Sanity check

(local
 (defthmd check-queue5-l$netlist-64
   (and (net-syntax-okp (queue5-l$netlist 64))
        (net-arity-okp (queue5-l$netlist 64))
        (queue5-l& (queue5-l$netlist 64) 64))))

;; Constraints on the state of QUEUE5-L

(defund queue5-l$st-format (st data-width)
  (b* ((l0 (get-field *queue5-l$l0* st))
       (l1 (get-field *queue5-l$l1* st))
       (l2 (get-field *queue5-l$l2* st))
       (l3 (get-field *queue5-l$l3* st))
       (l4 (get-field *queue5-l$l4* st)))
    (and (link$st-format l0 data-width)
         (link$st-format l1 data-width)
         (link$st-format l2 data-width)
         (link$st-format l3 data-width)
         (link$st-format l4 data-width))))

(defthm queue5-l$st-format=>data-width-constraint
  (implies (queue5-l$st-format st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue5-l$st-format)))
  :rule-classes :forward-chaining)

(defund queue5-l$valid-st (st data-width)
  (b* ((l0 (get-field *queue5-l$l0* st))
       (l1 (get-field *queue5-l$l1* st))
       (l2 (get-field *queue5-l$l2* st))
       (l3 (get-field *queue5-l$l3* st))
       (l4 (get-field *queue5-l$l4* st)))
    (and (link$valid-st l0 data-width)
         (link$valid-st l1 data-width)
         (link$valid-st l2 data-width)
         (link$valid-st l3 data-width)
         (link$valid-st l4 data-width))))

(defthmd queue5-l$valid-st=>data-width-constraint
  (implies (queue5-l$valid-st st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue5-l$valid-st)))
  :rule-classes :forward-chaining)

(defthmd queue5-l$valid-st=>st-format
  (implies (queue5-l$valid-st st data-width)
           (queue5-l$st-format st data-width))
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

  (defun queue5-l$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 2 inputs)))

  (defthm len-queue5-l$data-in
    (equal (len (queue5-l$data-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable queue5-l$data-in))

  ;; Extract the "ready-in-" signal

  (defund queue5-l$ready-in- (st)
    (b* ((l0 (get-field *queue5-l$l0* st))
         (l0.s (get-field *link$s* l0)))
      (f-buf (car l0.s))))

  (defthm booleanp-queue5-l$ready-in-
    (implies (queue5-l$valid-st st data-width)
             (booleanp (queue5-l$ready-in- st)))
    :hints (("Goal" :in-theory (enable queue5-l$valid-st
                                       queue5-l$ready-in-)))
    :rule-classes :type-prescription)

  ;; Extract the "ready-out" signal

  (defund queue5-l$ready-out (st)
    (b* ((l4 (get-field *queue5-l$l4* st))
         (l4.s (get-field *link$s* l4)))
      (f-buf (car l4.s))))

  (defthm booleanp-queue5-l$ready-out
    (implies (queue5-l$valid-st st data-width)
             (booleanp (queue5-l$ready-out st)))
    :hints (("Goal" :in-theory (enable queue5-l$valid-st
                                       queue5-l$ready-out)))
    :rule-classes :type-prescription)

  ;; Extract the output data

  (defund queue5-l$data-out (st)
    (v-threefix (strip-cars (get-field *link$d*
                                       (get-field *queue5-l$l4* st)))))

  (defthm v-threefix-of-queue5-l$data-out-canceled
    (equal (v-threefix (queue5-l$data-out st))
           (queue5-l$data-out st))
    :hints (("Goal" :in-theory (enable queue5-l$data-out))))

  (defthm len-queue5-l$data-out-1
    (implies (queue5-l$st-format st data-width)
             (equal (len (queue5-l$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable queue5-l$st-format
                                       queue5-l$data-out))))

  (defthm len-queue5-l$data-out-2
    (implies (queue5-l$valid-st st data-width)
             (equal (len (queue5-l$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable queue5-l$valid-st
                                       queue5-l$data-out))))

  (defthm bvp-queue5-l$data-out
    (implies (and (queue5-l$valid-st st data-width)
                  (queue5-l$ready-out st))
             (bvp (queue5-l$data-out st)))
    :hints (("Goal" :in-theory (enable queue5-l$valid-st
                                       queue5-l$ready-out
                                       queue5-l$data-out))))

  (defun queue5-l$outputs (inputs st data-width)
    (declare (ignore inputs data-width))
    (list* (queue5-l$ready-in- st)
           (queue5-l$ready-out st)
           (queue5-l$data-out st)))
  )

;; Prove that QUEUE5-L is not a DE primitive.

(not-primp-lemma queue5-l)

;; The value lemma for QUEUE5-L

(defthm queue5-l$value
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue5-l& netlist data-width)
                  (queue5-l$st-format st data-width))
             (equal (se (si 'queue5-l data-width) inputs st netlist)
                    (queue5-l$outputs inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'queue5-l data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue5-l&
                            queue5-l*$destructure
                            queue5-l$st-format
                            queue5-l$ready-in-
                            queue5-l$ready-out
                            queue5-l$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of QUEUE5-L.

(defun queue5-l$step (inputs st data-width)
  (b* ((in-act     (queue5-l$in-act inputs))
       (out-act    (queue5-l$out-act inputs))
       (data-in    (queue5-l$data-in inputs data-width))
       (go-signals (nthcdr (queue5-l$data-ins-len data-width) inputs))

       (go-trans1 (nth 0 go-signals))
       (go-trans2 (nth 1 go-signals))
       (go-trans3 (nth 2 go-signals))
       (go-trans4 (nth 3 go-signals))

       (l0 (get-field *queue5-l$l0* st))
       (l0.s (get-field *link$s* l0))
       (l0.d (get-field *link$d* l0))
       (l1 (get-field *queue5-l$l1* st))
       (l1.s (get-field *link$s* l1))
       (l1.d (get-field *link$d* l1))
       (l2 (get-field *queue5-l$l2* st))
       (l2.s (get-field *link$s* l2))
       (l2.d (get-field *link$d* l2))
       (l3 (get-field *queue5-l$l3* st))
       (l3.s (get-field *link$s* l3))
       (l3.d (get-field *link$d* l3))
       (l4 (get-field *queue5-l$l4* st))
       (l4.s (get-field *link$s* l4))

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
     (link$step l0-inputs l0 data-width)
     ;; L1
     (link$step l1-inputs l1 data-width)
     ;; L2
     (link$step l2-inputs l2 data-width)
     ;; L3
     (link$step l3-inputs l3 data-width)
     ;; L4
     (link$step l4-inputs l4 data-width))))

(defthm len-of-queue5-l$step
  (equal (len (queue5-l$step inputs st data-width))
         *queue5-l$st-len*))

(defthm queue5-l$step-v-threefix-of-data-in-canceled
  (implies
   (and (true-listp data-in)
        (equal (len data-in) data-width))
   (equal (queue5-l$step (list* in-act out-act
                                (append (v-threefix data-in) go-signals))
                         st
                         data-width)
          (queue5-l$step (list* in-act out-act
                                (append data-in go-signals))
                         st
                         data-width)))
  :hints (("Goal" :in-theory (enable queue5-l$step
                                     queue5-l$data-in
                                     queue5-l$in-act
                                     queue5-l$out-act))))

;; The state lemma for QUEUE5-L

(defthm queue5-l$state
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue5-l& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue5-l$go-num*)
                  (queue5-l$st-format st data-width))
             (equal (de (si 'queue5-l data-width) inputs st netlist)
                    (queue5-l$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'queue5-l data-width) inputs st netlist))
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

(defund queue5-l$input-format (inputs st data-width)
  (b* ((in-act     (queue5-l$in-act inputs))
       (out-act    (queue5-l$out-act inputs))
       (data-in    (queue5-l$data-in inputs data-width))
       (go-signals (nthcdr (queue5-l$data-ins-len data-width) inputs))

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
  (implies (queue5-l$input-format inputs st data-wisth)
           (booleanp (queue5-l$in-act inputs)))
  :hints (("Goal" :in-theory (enable queue5-l$input-format
                                     queue5-l$in-act)))
  :rule-classes :type-prescription)

(defthm booleanp-queue5-l$out-act
  (implies (queue5-l$input-format inputs st data-wisth)
           (booleanp (queue5-l$out-act inputs)))
  :hints (("Goal" :in-theory (enable queue5-l$input-format
                                     queue5-l$out-act)))
  :rule-classes :type-prescription)

(simulate-lemma queue5-l :clink t)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for QUEUE5-L that extracts the future output
;; sequence from the current state.

(defund queue5-l$extract (st)
  (b* ((l0 (get-field *queue5-l$l0* st))
       (l1 (get-field *queue5-l$l1* st))
       (l2 (get-field *queue5-l$l2* st))
       (l3 (get-field *queue5-l$l3* st))
       (l4 (get-field *queue5-l$l4* st)))
    (extract-valid-data (list l0 l1 l2 l3 l4))))

(defthm queue5-l$extract-not-empty
  (implies (and (queue5-l$ready-out st)
                (queue5-l$valid-st st data-width))
           (< 0 (len (queue5-l$extract st))))
  :hints (("Goal" :in-theory (e/d (queue5-l$valid-st
                                   queue5-l$extract
                                   queue5-l$ready-out)
                                  ())))
  :rule-classes :linear)

;; The extracted next-state function for QUEUE5-L.  Note that this function
;; avoids exploring the internal computation of QUEUE5-L.

(defund queue5-l$extracted-step (inputs st data-width)
  (b* ((data (queue5-l$data-in inputs data-width))
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
  (b* ((next-st (queue5-l$step inputs st data-width)))
    (implies (and (queue5-l$input-format inputs st data-width)
                  (queue5-l$valid-st st data-width))
             (equal (queue5-l$extract next-st)
                    (queue5-l$extracted-step inputs st data-width))))
  :hints (("Goal"
           :in-theory (enable get-field
                              f-sr
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
  (implies (and (queue5-l$input-format inputs st data-width)
                (queue5-l$valid-st st data-width))
           (queue5-l$valid-st (queue5-l$step inputs st data-width)
                            data-width))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            f-sr
                            queue5-l$input-format
                            queue5-l$valid-st
                            queue5-l$step
                            queue5-l$ready-in-
                            queue5-l$ready-out)
                           ()))))

(defthm queue5-l$extract-lemma-1
  (implies (and (queue5-l$input-format inputs st data-width)
                (queue5-l$valid-st st data-width)
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
  (implies (and (queue5-l$valid-st st data-width)
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
         (queue5-l$data-in inputs data-width)
         :clink t)

;; Extract the valid output sequence

(seq-gen queue5-l out out-act -1
         (queue5-l$data-out st)
         :netlist-data (nthcdr 2 outputs)
         :clink t)

;; The multi-step input-output relationship

(in-out-stream-lemma queue5-l :clink t)

