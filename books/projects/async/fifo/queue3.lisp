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
;;; 1. DE Module Generator of Q3
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of Q3
;;
;; Construct a DE module generator for a queue of three links, Q3, using the
;; link-joint model.  Prove the value and state lemmas for this module
;; generator.

(defconst *queue3$go-num* 4)
(defconst *queue3$st-len* 3)

(defun queue3$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun queue3$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (queue3$data-ins-len data-width)
     *queue3$go-num*))

;; DE module generator of Q3

(module-generator
 queue3* (data-width)
 (si 'queue3 data-width)
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 data-width)
                                     (sis 'go 0 *queue3$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-width))
 '(l0 l1 l2)
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
        (list* 'trans2-act 'out-act (sis 'd2-in 0 data-width)))

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

  ;; Out
  (list 'out-cntl
        '(out-act)
        'joint-cntl
        (list 'l2-status 'empty-out- (si 'go 3)))
  (list 'out-op
        (sis 'data-out 0 data-width)
        (si 'v-buf data-width)
        (sis 'd2-out 0 data-width)))

 (declare (xargs :guard (natp data-width))))

(make-event
 `(progn
    ,@(state-accessors-gen 'queue3 '(l0 l1 l2) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of Q3.

(defund queue3$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (queue3* data-width)
        (union$ (link$netlist data-width)
                *joint-cntl*
                (v-buf$netlist data-width)
                :test 'equal)))

;; Recognizer for Q3

(defund queue3& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (b* ((subnetlist (delete-to-eq (si 'queue3 data-width) netlist)))
    (and (equal (assoc (si 'queue3 data-width) netlist)
                (queue3* data-width))
         (link& subnetlist data-width)
         (joint-cntl& subnetlist)
         (v-buf& subnetlist data-width))))

;; Sanity check

(local
 (defthmd check-queue3$netlist-64
   (and (net-syntax-okp (queue3$netlist 64))
        (net-arity-okp (queue3$netlist 64))
        (queue3& (queue3$netlist 64) 64))))

;; Constraints on the state of Q3

(defund queue3$st-format (st data-width)
  (b* ((l0 (get-field *queue3$l0* st))
       (l1 (get-field *queue3$l1* st))
       (l2 (get-field *queue3$l2* st)))
    (and (link$st-format l0 data-width)
         (link$st-format l1 data-width)
         (link$st-format l2 data-width))))

(defthm queue3$st-format=>constraint
  (implies (queue3$st-format st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue3$st-format)))
  :rule-classes :forward-chaining)

(defund queue3$valid-st (st data-width)
  (b* ((l0 (get-field *queue3$l0* st))
       (l1 (get-field *queue3$l1* st))
       (l2 (get-field *queue3$l2* st)))
    (and (link$valid-st l0 data-width)
         (link$valid-st l1 data-width)
         (link$valid-st l2 data-width))))

(defthmd queue3$valid-st=>constraint
  (implies (queue3$valid-st st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue3$valid-st)))
  :rule-classes :forward-chaining)

(defthmd queue3$valid-st=>st-format
  (implies (queue3$valid-st st data-width)
           (queue3$st-format st data-width))
  :hints (("Goal" :in-theory (e/d (queue3$st-format
                                   queue3$valid-st)
                                  (link$st-format)))))

;; Extract the input and output signals for Q3

(progn
  ;; Extract the input data

  (defun queue3$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 2 inputs)))

  (defthm len-queue3$data-in
    (equal (len (queue3$data-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable queue3$data-in))

  ;; Extract the "in-act" signal

  (defund queue3$in-act (inputs st data-width)
    (b* ((full-in (nth 0 inputs))
         (go-signals (nthcdr (queue3$data-ins-len data-width) inputs))
         (go-in (nth 0 go-signals))

         (l0 (get-field *queue3$l0* st))
         (l0.s (get-field *link$s* l0)))
      (joint-act full-in (car l0.s) go-in)))

  (defthm queue3$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (queue3$in-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable queue3$in-act))))

  ;; Extract the "out-act" signal

  (defund queue3$out-act (inputs st data-width)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (queue3$data-ins-len data-width) inputs))
         (go-out (nth 3 go-signals))

         (l2 (get-field *queue3$l2* st))
         (l2.s (get-field *link$s* l2)))
      (joint-act (car l2.s) empty-out- go-out)))

  (defthm queue3$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (queue3$out-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable queue3$out-act))))

  ;; Extract the output data

  (defund queue3$data-out (st)
    (v-threefix (strip-cars (get-field *link$d*
                                       (get-field *queue3$l2* st)))))

  (defthm len-queue3$data-out-1
    (implies (queue3$st-format st data-width)
             (equal (len (queue3$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable queue3$st-format
                                       queue3$data-out))))

  (defthm len-queue3$data-out-2
    (implies (queue3$valid-st st data-width)
             (equal (len (queue3$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable queue3$valid-st
                                       queue3$data-out))))

  (defthm bvp-queue3$data-out
    (implies (and (queue3$valid-st st data-width)
                  (queue3$out-act inputs st data-width))
             (bvp (queue3$data-out st)))
    :hints (("Goal" :in-theory (enable queue3$valid-st
                                       queue3$out-act
                                       queue3$data-out))))

  (defun queue3$outputs (inputs st data-width)
    (list* (queue3$in-act inputs st data-width)
           (queue3$out-act inputs st data-width)
           (queue3$data-out st)))
  )

;; The value lemma for Q3

(defthm queue3$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (queue3& netlist data-width)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue3$go-num*)
                  (queue3$st-format st data-width))
             (equal (se (si 'queue3 data-width) inputs st netlist)
                    (queue3$outputs inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'queue3 data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue3&
                            queue3*$destructure
                            queue3$st-format
                            queue3$in-act
                            queue3$out-act
                            queue3$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of Q3, namely, the next states of
;; three links L0, L1, and L2.

(defun queue3$step (inputs st data-width)
  (b* ((data-in    (queue3$data-in inputs data-width))
       (go-signals (nthcdr (queue3$data-ins-len data-width) inputs))

       (go-trans1 (nth 1 go-signals))
       (go-trans2 (nth 2 go-signals))

       (l0 (get-field *queue3$l0* st))
       (l0.s (get-field *link$s* l0))
       (l0.d (get-field *link$d* l0))
       (l1 (get-field *queue3$l1* st))
       (l1.s (get-field *link$s* l1))
       (l1.d (get-field *link$d* l1))
       (l2 (get-field *queue3$l2* st))
       (l2.s (get-field *link$s* l2))

       (in-act (queue3$in-act inputs st data-width))
       (out-act (queue3$out-act inputs st data-width))
       (trans1-act (joint-act (car l0.s) (car l1.s) go-trans1))
       (trans2-act (joint-act (car l1.s) (car l2.s) go-trans2))

       (l0-inputs (list* in-act trans1-act data-in))
       (l1-inputs (list* trans1-act trans2-act (strip-cars l0.d)))
       (l2-inputs (list* trans2-act out-act (strip-cars l1.d))))
    (list
     ;; L0
     (link$step l0-inputs l0 data-width)
     ;; L1
     (link$step l1-inputs l1 data-width)
     ;; L2
     (link$step l2-inputs l2 data-width))))

(defthm len-of-queue3$step
  (equal (len (queue3$step inputs st data-width))
         *queue3$st-len*))

;; The state lemma for Q3

(defthm queue3$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (queue3& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue3$go-num*)
                  (queue3$st-format st data-width))
             (equal (de (si 'queue3 data-width) inputs st netlist)
                    (queue3$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'queue3 data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue3&
                            queue3*$destructure
                            queue3$st-format
                            queue3$data-in
                            queue3$in-act
                            queue3$out-act)
                           (de-module-disabled-rules)))))

(in-theory (disable queue3$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund queue3$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (queue3$data-in inputs data-width))
       (go-signals (nthcdr (queue3$data-ins-len data-width) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *queue3$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(defthm booleanp-queue3$in-act
  (implies (and (queue3$input-format inputs data-width)
                (queue3$valid-st st data-width))
           (booleanp (queue3$in-act inputs st data-width)))
  :hints (("Goal" :in-theory (enable queue3$input-format
                                     queue3$valid-st
                                     queue3$in-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-queue3$out-act
  (implies (and (queue3$input-format inputs data-width)
                (queue3$valid-st st data-width))
           (booleanp (queue3$out-act inputs st data-width)))
  :hints (("Goal" :in-theory (enable queue3$input-format
                                     queue3$valid-st
                                     queue3$out-act)))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma queue3)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for Q3 that extracts the future output sequence from
;; the current state.

(defund queue3$extract (st)
  (b* ((l0 (get-field *queue3$l0* st))
       (l1 (get-field *queue3$l1* st))
       (l2 (get-field *queue3$l2* st)))
    (extract-valid-data (list l0 l1 l2))))

(defthm queue3$extract-not-empty
  (implies (and (queue3$out-act inputs st data-width)
                (queue3$valid-st st data-width))
           (< 0 (len (queue3$extract st))))
  :hints (("Goal"
           :in-theory (e/d (queue3$valid-st
                            queue3$extract
                            queue3$out-act)
                           ())))
  :rule-classes :linear)

;; The extracted next-state function for Q3.  Note that this function avoids
;; exploring the internal computation of Q3.

(defund queue3$extracted-step (inputs st data-width)
  (b* ((data (queue3$data-in inputs data-width))
       (extracted-st (queue3$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue3$out-act inputs st data-width) t)
      (cond
       ((equal (queue3$in-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue3$in-act inputs st data-width) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(defthm queue3$extracted-step-correct
  (b* ((next-st (queue3$step inputs st data-width)))
    (implies (and (queue3$input-format inputs data-width)
                  (queue3$valid-st st data-width))
             (equal (queue3$extract next-st)
                    (queue3$extracted-step inputs st data-width))))
  :hints (("Goal"
           :in-theory (enable get-field
                              f-sr
                              queue3$extracted-step
                              queue3$input-format
                              queue3$valid-st
                              queue3$st-format
                              queue3$step
                              queue3$in-act
                              queue3$out-act
                              queue3$extract))))

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that queue3$valid-st is an invariant.

(defthm queue3$valid-st-preserved
  (implies (and (queue3$input-format inputs data-width)
                (queue3$valid-st st data-width))
           (queue3$valid-st (queue3$step inputs st data-width)
                            data-width))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue3$input-format
                            queue3$valid-st
                            queue3$st-format
                            queue3$step
                            queue3$in-act
                            queue3$out-act
                            f-sr)
                           (nfix)))))

(defthm queue3$extract-lemma
  (implies (and (queue3$valid-st st data-width)
                (queue3$out-act inputs st data-width))
           (equal (list (queue3$data-out st))
                  (nthcdr (1- (len (queue3$extract st)))
                          (queue3$extract st))))
  :hints (("Goal"
           :in-theory (enable queue3$valid-st
                              queue3$st-format
                              queue3$extract
                              queue3$out-act
                              queue3$data-out))))

;; Extract the accepted input sequence

(seq-gen queue3 in in-act 0
         (queue3$data-in inputs data-width))

;; Extract the valid output sequence

(seq-gen queue3 out out-act 1
         (queue3$data-out st)
         :netlist-data (nthcdr 2 outputs))

;; The multi-step input-output relationship

(in-out-stream-lemma queue3)

