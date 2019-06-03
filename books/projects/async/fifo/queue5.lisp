;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "../link-joint")
(include-book "../vector-module")

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of Q5
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of Q5
;;
;; Construct a DE module generator for a queue of five links, Q5, using the
;; link-joint model.  Prove the value and state lemmas for this module
;; generator.

(defconst *queue5$go-num* 6)

(defun queue5$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (mbe :logic (nfix data-size)
            :exec  data-size)))

(defun queue5$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (queue5$data-ins-len data-size)
     *queue5$go-num*))

;; DE module generator of Q5

(module-generator
 queue5* (data-size)
 (si 'queue5 data-size)
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 data-size)
                                     (sis 'go 0 *queue5$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-size))
 '(l0 l1 l2 l3 l4)
 (list
  ;; LINKS
  ;; L0
  (list 'l0
        (list* 'l0-status (sis 'd0-out 0 data-size))
        (si 'link data-size)
        (list* 'in-act 'trans1-act (sis 'd0-in 0 data-size)))

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
        (list* 'l4-status (sis 'd4-out 0 data-size))
        (si 'link data-size)
        (list* 'trans4-act 'out-act (sis 'd4-in 0 data-size)))

  ;; JOINTS
  ;; In
  (list 'in-cntl
        '(in-act)
        'joint-cntl
        (list 'full-in 'l0-status (si 'go 0)))
  (list 'in-op
        (sis 'd0-in 0 data-size)
        (si 'v-buf data-size)
        (sis 'data-in 0 data-size))

  ;; Transfer data1
  (list 'trans1-cntl
        '(trans1-act)
        'joint-cntl
        (list 'l0-status 'l1-status (si 'go 1)))
  (list 'trans1-op
        (sis 'd1-in 0 data-size)
        (si 'v-buf data-size)
        (sis 'd0-out 0 data-size))

  ;; Transfer data2
  (list 'trans2-cntl
        '(trans2-act)
        'joint-cntl
        (list 'l1-status 'l2-status (si 'go 2)))
  (list 'trans2-op
        (sis 'd2-in 0 data-size)
        (si 'v-buf data-size)
        (sis 'd1-out 0 data-size))

  ;; Transfer data3
  (list 'trans3-cntl
        '(trans3-act)
        'joint-cntl
        (list 'l2-status 'l3-status (si 'go 3)))
  (list 'trans3-op
        (sis 'd3-in 0 data-size)
        (si 'v-buf data-size)
        (sis 'd2-out 0 data-size))

  ;; Transfer data4
  (list 'trans4-cntl
        '(trans4-act)
        'joint-cntl
        (list 'l3-status 'l4-status (si 'go 4)))
  (list 'trans4-op
        (sis 'd4-in 0 data-size)
        (si 'v-buf data-size)
        (sis 'd3-out 0 data-size))

  ;; Out
  (list 'out-cntl
        '(out-act)
        'joint-cntl
        (list 'l4-status 'empty-out- (si 'go 5)))
  (list 'out-op
        (sis 'data-out 0 data-size)
        (si 'v-buf data-size)
        (sis 'd4-out 0 data-size)))

 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'queue5 '(l0 l1 l2 l3 l4) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of Q5.

(defund queue5$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (queue5* data-size)
        (union$ (link$netlist data-size)
                *joint-cntl*
                (v-buf$netlist data-size)
                :test 'equal)))

;; Recognizer for Q5

(defund queue5& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'queue5 data-size) netlist)))
    (and (equal (assoc (si 'queue5 data-size) netlist)
                (queue5* data-size))
         (link& subnetlist data-size)
         (joint-cntl& subnetlist)
         (v-buf& subnetlist data-size))))

;; Sanity check

(local
 (defthmd check-queue5$netlist-64
   (and (net-syntax-okp (queue5$netlist 64))
        (net-arity-okp (queue5$netlist 64))
        (queue5& (queue5$netlist 64) 64))))

;; Constraints on the state of Q5

(defund queue5$st-format (st data-size)
  (b* ((l0 (nth *queue5$l0* st))
       (l1 (nth *queue5$l1* st))
       (l2 (nth *queue5$l2* st))
       (l3 (nth *queue5$l3* st))
       (l4 (nth *queue5$l4* st)))
    (and (link$st-format l0 data-size)
         (link$st-format l1 data-size)
         (link$st-format l2 data-size)
         (link$st-format l3 data-size)
         (link$st-format l4 data-size))))

(defthm queue5$st-format=>constraint
  (implies (queue5$st-format st data-size)
           (natp data-size))
  :hints (("Goal" :in-theory (enable queue5$st-format)))
  :rule-classes :forward-chaining)

(defund queue5$valid-st (st data-size)
  (b* ((l0 (nth *queue5$l0* st))
       (l1 (nth *queue5$l1* st))
       (l2 (nth *queue5$l2* st))
       (l3 (nth *queue5$l3* st))
       (l4 (nth *queue5$l4* st)))
    (and (link$valid-st l0 data-size)
         (link$valid-st l1 data-size)
         (link$valid-st l2 data-size)
         (link$valid-st l3 data-size)
         (link$valid-st l4 data-size))))

(defthmd queue5$valid-st=>constraint
  (implies (queue5$valid-st st data-size)
           (natp data-size))
  :hints (("Goal" :in-theory (enable queue5$valid-st)))
  :rule-classes :forward-chaining)

(defthmd queue5$valid-st=>st-format
  (implies (queue5$valid-st st data-size)
           (queue5$st-format st data-size))
  :hints (("Goal" :in-theory (e/d (queue5$st-format
                                   queue5$valid-st)
                                  (link$st-format)))))

;; Extract the input and output signals for Q5

(progn
  ;; Extract the input data

  (defun queue5$data-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (mbe :logic (nfix data-size)
               :exec  data-size)
          (nthcdr 2 inputs)))

  (defthm len-queue5$data-in
    (equal (len (queue5$data-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable queue5$data-in))

  ;; Extract the "in-act" signal

  (defund queue5$in-act (inputs st data-size)
    (b* ((full-in (nth 0 inputs))
         (go-signals (nthcdr (queue5$data-ins-len data-size) inputs))
         (go-in (nth 0 go-signals))

         (l0 (nth *queue5$l0* st))
         (l0.s (nth *link$s* l0)))
      (joint-act full-in (car l0.s) go-in)))

  (defthm queue5$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (queue5$in-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable queue5$in-act))))

  ;; Extract the "out-act" signal

  (defund queue5$out-act (inputs st data-size)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (queue5$data-ins-len data-size) inputs))
         (go-out (nth 5 go-signals))

         (l4 (nth *queue5$l4* st))
         (l4.s (nth *link$s* l4)))
      (joint-act (car l4.s) empty-out- go-out)))

  (defthm queue5$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (queue5$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable queue5$out-act))))

  ;; Extract the output data

  (defund queue5$data-out (st)
    (v-threefix (strip-cars (nth *link$d*
                                 (nth *queue5$l4* st)))))

  (defthm len-queue5$data-out-1
    (implies (queue5$st-format st data-size)
             (equal (len (queue5$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable queue5$st-format
                                       queue5$data-out))))

  (defthm len-queue5$data-out-2
    (implies (queue5$valid-st st data-size)
             (equal (len (queue5$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable queue5$valid-st
                                       queue5$data-out))))

  (defthm bvp-queue5$data-out
    (implies (and (queue5$valid-st st data-size)
                  (queue5$out-act inputs st data-size))
             (bvp (queue5$data-out st)))
    :hints (("Goal" :in-theory (enable queue5$valid-st
                                       queue5$out-act
                                       queue5$data-out))))

  (defun queue5$outputs (inputs st data-size)
    (list* (queue5$in-act inputs st data-size)
           (queue5$out-act inputs st data-size)
           (queue5$data-out st)))
  )

;; The value lemma for Q5

(defthm queue5$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (queue5& netlist data-size)
                  (equal (len data-in) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue5$go-num*)
                  (queue5$st-format st data-size))
             (equal (se (si 'queue5 data-size) inputs st netlist)
                    (queue5$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'queue5 data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue5&
                            queue5*$destructure
                            queue5$st-format
                            queue5$in-act
                            queue5$out-act
                            queue5$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of Q5.

(defun queue5$step (inputs st data-size)
  (b* ((data-in    (queue5$data-in inputs data-size))
       (go-signals (nthcdr (queue5$data-ins-len data-size) inputs))

       (go-trans1 (nth 1 go-signals))
       (go-trans2 (nth 2 go-signals))
       (go-trans3 (nth 3 go-signals))
       (go-trans4 (nth 4 go-signals))

       (l0 (nth *queue5$l0* st))
       (l0.s (nth *link$s* l0))
       (l0.d (nth *link$d* l0))
       (l1 (nth *queue5$l1* st))
       (l1.s (nth *link$s* l1))
       (l1.d (nth *link$d* l1))
       (l2 (nth *queue5$l2* st))
       (l2.s (nth *link$s* l2))
       (l2.d (nth *link$d* l2))
       (l3 (nth *queue5$l3* st))
       (l3.s (nth *link$s* l3))
       (l3.d (nth *link$d* l3))
       (l4 (nth *queue5$l4* st))
       (l4.s (nth *link$s* l4))

       (in-act (queue5$in-act inputs st data-size))
       (out-act (queue5$out-act inputs st data-size))
       (trans1-act (joint-act (car l0.s) (car l1.s) go-trans1))
       (trans2-act (joint-act (car l1.s) (car l2.s) go-trans2))
       (trans3-act (joint-act (car l2.s) (car l3.s) go-trans3))
       (trans4-act (joint-act (car l3.s) (car l4.s) go-trans4))

       (l0-inputs (list* in-act trans1-act data-in))
       (l1-inputs (list* trans1-act trans2-act (strip-cars l0.d)))
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

;; The state lemma for Q5

(defthm queue5$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (queue5& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue5$go-num*)
                  (queue5$st-format st data-size))
             (equal (de (si 'queue5 data-size) inputs st netlist)
                    (queue5$step inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'queue5 data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue5&
                            queue5*$destructure
                            queue5$st-format
                            queue5$data-in
                            queue5$in-act
                            queue5$out-act)
                           (de-module-disabled-rules)))))

(in-theory (disable queue5$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund queue5$input-format (inputs data-size)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-size))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (queue5$data-in inputs data-size))
       (go-signals (nthcdr (queue5$data-ins-len data-size) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *queue5$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(defthm booleanp-queue5$in-act
  (implies (and (queue5$input-format inputs data-size)
                (queue5$valid-st st data-size))
           (booleanp (queue5$in-act inputs st data-size)))
  :hints (("Goal" :in-theory (enable queue5$input-format
                                     queue5$valid-st
                                     queue5$in-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-queue5$out-act
  (implies (and (queue5$input-format inputs data-size)
                (queue5$valid-st st data-size))
           (booleanp (queue5$out-act inputs st data-size)))
  :hints (("Goal" :in-theory (enable queue5$input-format
                                     queue5$valid-st
                                     queue5$out-act)))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma queue5)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for Q5 that extracts the future output sequence from
;; the current state.

(defund queue5$extract (st)
  (b* ((l0 (nth *queue5$l0* st))
       (l1 (nth *queue5$l1* st))
       (l2 (nth *queue5$l2* st))
       (l3 (nth *queue5$l3* st))
       (l4 (nth *queue5$l4* st)))
    (extract-valid-data (list l0 l1 l2 l3 l4))))

(defthm queue5$extract-not-empty
  (implies (and (queue5$out-act inputs st data-size)
                (queue5$valid-st st data-size))
           (< 0 (len (queue5$extract st))))
  :hints (("Goal"
           :in-theory (e/d (queue5$valid-st
                            queue5$extract
                            queue5$out-act)
                           ())))
  :rule-classes :linear)

;; The extracted next-state function for Q5.  Note that this function avoids
;; exploring the internal computation of Q5.

(defund queue5$extracted-step (inputs st data-size)
  (b* ((data (queue5$data-in inputs data-size))
       (extracted-st (queue5$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue5$out-act inputs st data-size) t)
      (cond
       ((equal (queue5$in-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue5$in-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(defthm queue5$extracted-step-correct
  (b* ((next-st (queue5$step inputs st data-size)))
    (implies (and (queue5$input-format inputs data-size)
                  (queue5$valid-st st data-size))
             (equal (queue5$extract next-st)
                    (queue5$extracted-step inputs st data-size))))
  :hints (("Goal"
           :in-theory (enable f-sr
                              queue5$extracted-step
                              queue5$input-format
                              queue5$valid-st
                              queue5$st-format
                              queue5$step
                              queue5$in-act
                              queue5$out-act
                              queue5$extract))))

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that queue5$valid-st is an invariant.

(defthm queue5$valid-st-preserved
  (implies (and (queue5$input-format inputs data-size)
                (queue5$valid-st st data-size))
           (queue5$valid-st (queue5$step inputs st data-size)
                            data-size))
  :hints (("Goal"
           :in-theory (e/d (queue5$input-format
                            queue5$valid-st
                            queue5$st-format
                            queue5$step
                            queue5$in-act
                            queue5$out-act
                            f-sr)
                           (nfix)))))

(defthm queue5$extract-lemma
  (implies (and (queue5$valid-st st data-size)
                (queue5$out-act inputs st data-size))
           (equal (list (queue5$data-out st))
                  (nthcdr (1- (len (queue5$extract st)))
                          (queue5$extract st))))
  :hints (("Goal"
           :in-theory (enable queue5$valid-st
                              queue5$st-format
                              queue5$extract
                              queue5$out-act
                              queue5$data-out))))

;; Extract the accepted input sequence

(seq-gen queue5 in in-act 0
         (queue5$data-in inputs data-size))

;; Extract the valid output sequence

(seq-gen queue5 out out-act 1
         (queue5$data-out st)
         :netlist-data (nthcdr 2 outputs))

;; The multi-step input-output relationship

(in-out-stream-lemma queue5)

