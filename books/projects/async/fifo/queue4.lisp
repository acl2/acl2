;; Copyright (C) 2018, Regents of the University of Texas
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
;;; 1. DE Module Generator of Q4
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of Q4
;;
;; Construct a DE module generator for a queue of four links, Q4, using the
;; link-joint model.  Prove the value and state lemmas for this module
;; generator.

(defconst *queue4$go-num* 5)
(defconst *queue4$st-len* 4)

(defun queue4$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun queue4$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (queue4$data-ins-len data-width)
     *queue4$go-num*))

;; DE module generator of Q4

(module-generator
 queue4* (data-width)
 (si 'queue4 data-width)
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 data-width)
                                     (sis 'go 0 *queue4$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-width))
 '(l0 l1 l2 l3)
 (list
  ;; LINKS
  ;; L0
  (list 'l0
        (list* 'l0-status (sis 'd0-out 0 data-width))
        (si 'link data-width)
        (list* 'in-act 'trans1-act (sis 'd0-in 0 data-width)))

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
        (list* 'trans3-act 'out-act (sis 'd3-in 0 data-width)))

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

  ;; Transfer data1
  (list 'trans1-cntl
        '(trans1-act)
        'joint-cntl
        (list 'l0-status 'l1-status (si 'go 1)))
  (list 'trans1-op
        (sis 'd1-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'd0-out 0 data-width))

  ;; Transfer data2
  (list 'trans2-cntl
        '(trans2-act)
        'joint-cntl
        (list 'l1-status 'l2-status (si 'go 2)))
  (list 'trans2-op
        (sis 'd2-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'd1-out 0 data-width))

  ;; Transfer data3
  (list 'trans3-cntl
        '(trans3-act)
        'joint-cntl
        (list 'l2-status 'l3-status (si 'go 3)))
  (list 'trans3-op
        (sis 'd3-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'd2-out 0 data-width))

  ;; Out
  (list 'out-cntl
        '(out-act)
        'joint-cntl
        (list 'l3-status 'empty-out- (si 'go 4)))
  (list 'out-op
        (sis 'data-out 0 data-width)
        (si 'v-buf data-width)
        (sis 'd3-out 0 data-width)))

 (declare (xargs :guard (natp data-width))))

(make-event
 `(progn
    ,@(state-accessors-gen 'queue4 '(l0 l1 l2 l3) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of Q4.

(defund queue4$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (queue4* data-width)
        (union$ (link$netlist data-width)
                *joint-cntl*
                (v-buf$netlist data-width)
                :test 'equal)))

;; Recognizer for Q4

(defund queue4& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (b* ((subnetlist (delete-to-eq (si 'queue4 data-width) netlist)))
    (and (equal (assoc (si 'queue4 data-width) netlist)
                (queue4* data-width))
         (link& subnetlist data-width)
         (joint-cntl& subnetlist)
         (v-buf& subnetlist data-width))))

;; Sanity check

(local
 (defthmd check-queue4$netlist-64
   (and (net-syntax-okp (queue4$netlist 64))
        (net-arity-okp (queue4$netlist 64))
        (queue4& (queue4$netlist 64) 64))))

;; Constraints on the state of Q4

(defund queue4$st-format (st data-width)
  (b* ((l0 (get-field *queue4$l0* st))
       (l1 (get-field *queue4$l1* st))
       (l2 (get-field *queue4$l2* st))
       (l3 (get-field *queue4$l3* st)))
    (and (link$st-format l0 data-width)
         (link$st-format l1 data-width)
         (link$st-format l2 data-width)
         (link$st-format l3 data-width))))

(defthm queue4$st-format=>constraint
  (implies (queue4$st-format st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue4$st-format)))
  :rule-classes :forward-chaining)

(defund queue4$valid-st (st data-width)
  (b* ((l0 (get-field *queue4$l0* st))
       (l1 (get-field *queue4$l1* st))
       (l2 (get-field *queue4$l2* st))
       (l3 (get-field *queue4$l3* st)))
    (and (link$valid-st l0 data-width)
         (link$valid-st l1 data-width)
         (link$valid-st l2 data-width)
         (link$valid-st l3 data-width))))

(defthmd queue4$valid-st=>constraint
  (implies (queue4$valid-st st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue4$valid-st)))
  :rule-classes :forward-chaining)

(defthmd queue4$valid-st=>st-format
  (implies (queue4$valid-st st data-width)
           (queue4$st-format st data-width))
  :hints (("Goal" :in-theory (e/d (queue4$st-format
                                   queue4$valid-st)
                                  (link$st-format)))))

;; Extract the input and output signals for Q4

(progn
  ;; Extract the input data

  (defun queue4$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 2 inputs)))

  (defthm len-queue4$data-in
    (equal (len (queue4$data-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable queue4$data-in))

  ;; Extract the "in-act" signal

  (defund queue4$in-act (inputs st data-width)
    (b* ((full-in (nth 0 inputs))
         (go-signals (nthcdr (queue4$data-ins-len data-width) inputs))
         (go-in (nth 0 go-signals))

         (l0 (get-field *queue4$l0* st))
         (l0.s (get-field *link$s* l0)))
      (joint-act full-in (car l0.s) go-in)))

  (defthm queue4$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (queue4$in-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable queue4$in-act))))

  ;; Extract the "out-act" signal

  (defund queue4$out-act (inputs st data-width)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (queue4$data-ins-len data-width) inputs))
         (go-out (nth 4 go-signals))

         (l3 (get-field *queue4$l3* st))
         (l3.s (get-field *link$s* l3)))
      (joint-act (car l3.s) empty-out- go-out)))

  (defthm queue4$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (queue4$out-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable queue4$out-act))))

  ;; Extract the output data

  (defund queue4$data-out (st)
    (v-threefix (strip-cars (get-field *link$d*
                                       (get-field *queue4$l3* st)))))

  (defthm len-queue4$data-out-1
    (implies (queue4$st-format st data-width)
             (equal (len (queue4$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable queue4$st-format
                                       queue4$data-out))))

  (defthm len-queue4$data-out-2
    (implies (queue4$valid-st st data-width)
             (equal (len (queue4$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable queue4$valid-st
                                       queue4$data-out))))

  (defthm bvp-queue4$data-out
    (implies (and (queue4$valid-st st data-width)
                  (queue4$out-act inputs st data-width))
             (bvp (queue4$data-out st)))
    :hints (("Goal" :in-theory (enable queue4$valid-st
                                       queue4$out-act
                                       queue4$data-out))))

  (defun queue4$outputs (inputs st data-width)
    (list* (queue4$in-act inputs st data-width)
           (queue4$out-act inputs st data-width)
           (queue4$data-out st)))
  )

;; The value lemma for Q4

(defthm queue4$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (queue4& netlist data-width)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue4$go-num*)
                  (queue4$st-format st data-width))
             (equal (se (si 'queue4 data-width) inputs st netlist)
                    (queue4$outputs inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'queue4 data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue4&
                            queue4*$destructure
                            queue4$st-format
                            queue4$in-act
                            queue4$out-act
                            queue4$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of Q4.

(defun queue4$step (inputs st data-width)
  (b* ((data-in    (queue4$data-in inputs data-width))
       (go-signals (nthcdr (queue4$data-ins-len data-width) inputs))

       (go-trans1 (nth 1 go-signals))
       (go-trans2 (nth 2 go-signals))
       (go-trans3 (nth 3 go-signals))

       (l0 (get-field *queue4$l0* st))
       (l0.s (get-field *link$s* l0))
       (l0.d (get-field *link$d* l0))
       (l1 (get-field *queue4$l1* st))
       (l1.s (get-field *link$s* l1))
       (l1.d (get-field *link$d* l1))
       (l2 (get-field *queue4$l2* st))
       (l2.s (get-field *link$s* l2))
       (l2.d (get-field *link$d* l2))
       (l3 (get-field *queue4$l3* st))
       (l3.s (get-field *link$s* l3))

       (in-act (queue4$in-act inputs st data-width))
       (out-act (queue4$out-act inputs st data-width))
       (trans1-act (joint-act (car l0.s) (car l1.s) go-trans1))
       (trans2-act (joint-act (car l1.s) (car l2.s) go-trans2))
       (trans3-act (joint-act (car l2.s) (car l3.s) go-trans3))

       (l0-inputs (list* in-act trans1-act data-in))
       (l1-inputs (list* trans1-act trans2-act (strip-cars l0.d)))
       (l2-inputs (list* trans2-act trans3-act (strip-cars l1.d)))
       (l3-inputs (list* trans3-act out-act (strip-cars l2.d))))
    (list
     ;; L0
     (link$step l0-inputs l0 data-width)
     ;; L1
     (link$step l1-inputs l1 data-width)
     ;; L2
     (link$step l2-inputs l2 data-width)
     ;; L3
     (link$step l3-inputs l3 data-width))))

(defthm len-of-queue4$step
  (equal (len (queue4$step inputs st data-width))
         *queue4$st-len*))

;; The state lemma for Q4

(defthm queue4$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (queue4& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue4$go-num*)
                  (queue4$st-format st data-width))
             (equal (de (si 'queue4 data-width) inputs st netlist)
                    (queue4$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'queue4 data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue4&
                            queue4*$destructure
                            queue4$st-format
                            queue4$data-in
                            queue4$in-act
                            queue4$out-act)
                           (de-module-disabled-rules)))))

(in-theory (disable queue4$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund queue4$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (queue4$data-in inputs data-width))
       (go-signals (nthcdr (queue4$data-ins-len data-width) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *queue4$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(defthm booleanp-queue4$in-act
  (implies (and (queue4$input-format inputs data-width)
                (queue4$valid-st st data-width))
           (booleanp (queue4$in-act inputs st data-width)))
  :hints (("Goal" :in-theory (enable queue4$input-format
                                     queue4$valid-st
                                     queue4$in-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-queue4$out-act
  (implies (and (queue4$input-format inputs data-width)
                (queue4$valid-st st data-width))
           (booleanp (queue4$out-act inputs st data-width)))
  :hints (("Goal" :in-theory (enable queue4$input-format
                                     queue4$valid-st
                                     queue4$out-act)))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma queue4)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for Q4 that extracts the future output sequence from
;; the current state.

(defund queue4$extract (st)
  (b* ((l0 (get-field *queue4$l0* st))
       (l1 (get-field *queue4$l1* st))
       (l2 (get-field *queue4$l2* st))
       (l3 (get-field *queue4$l3* st)))
    (extract-valid-data (list l0 l1 l2 l3))))

(defthm queue4$extract-not-empty
  (implies (and (queue4$out-act inputs st data-width)
                (queue4$valid-st st data-width))
           (< 0 (len (queue4$extract st))))
  :hints (("Goal"
           :in-theory (e/d (queue4$valid-st
                            queue4$extract
                            queue4$out-act)
                           ())))
  :rule-classes :linear)

;; The extracted next-state function for Q4.  Note that this function avoids
;; exploring the internal computation of Q4.

(defund queue4$extracted-step (inputs st data-width)
  (b* ((data (queue4$data-in inputs data-width))
       (extracted-st (queue4$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue4$out-act inputs st data-width) t)
      (cond
       ((equal (queue4$in-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue4$in-act inputs st data-width) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(defthm queue4$extracted-step-correct
  (b* ((next-st (queue4$step inputs st data-width)))
    (implies (and (queue4$input-format inputs data-width)
                  (queue4$valid-st st data-width))
             (equal (queue4$extract next-st)
                    (queue4$extracted-step inputs st data-width))))
  :hints (("Goal"
           :in-theory (enable get-field
                              f-sr
                              queue4$extracted-step
                              queue4$input-format
                              queue4$valid-st
                              queue4$st-format
                              queue4$step
                              queue4$in-act
                              queue4$out-act
                              queue4$extract))))

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that queue4$valid-st is an invariant.

(defthm queue4$valid-st-preserved
  (implies (and (queue4$input-format inputs data-width)
                (queue4$valid-st st data-width))
           (queue4$valid-st (queue4$step inputs st data-width)
                            data-width))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue4$input-format
                            queue4$valid-st
                            queue4$st-format
                            queue4$step
                            queue4$in-act
                            queue4$out-act
                            f-sr)
                           (nfix)))))

(defthm queue4$extract-lemma
  (implies (and (queue4$valid-st st data-width)
                (queue4$out-act inputs st data-width))
           (equal (list (queue4$data-out st))
                  (nthcdr (1- (len (queue4$extract st)))
                          (queue4$extract st))))
  :hints (("Goal"
           :in-theory (enable queue4$valid-st
                              queue4$st-format
                              queue4$extract
                              queue4$out-act
                              queue4$data-out))))

;; Extract the accepted input sequence

(seq-gen queue4 in in-act 0
         (queue4$data-in inputs data-width))

;; Extract the valid output sequence

(seq-gen queue4 out out-act 1
         (queue4$data-out st)
         :netlist-data (nthcdr 2 outputs))

;; The multi-step input-output relationship

(in-out-stream-lemma queue4)

