;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; November 2018

(in-package "ADE")

(include-book "queue10-l")

(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of QUEUE20-L
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of QUEUE20-L
;;
;; Construct a DE module generator for a queue of 20 links, QUEUE20-L, using
;; the link-joint model.  Prove the value and state lemmas for this module
;; generator.  Note that QUEUE20-L is a complex link.  It is constructed by
;; concatenating two instances of QUEUE10-L via a buffer joint.

(defconst *queue20-l$prim-go-num* 1)
(defconst *queue20-l$go-num* (+ *queue20-l$prim-go-num*
                                (* 2 *queue10-l$go-num*)))
(defconst *queue20-l$st-len* 2)

(defun queue20-l$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun queue20-l$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (queue20-l$data-ins-len data-width)
     *queue20-l$go-num*))

;; DE module generator of QUEUE20-L

(module-generator
 queue20-l* (data-width)
 (si 'queue20-l data-width)
 (list* 'in-act 'out-act (append (sis 'data-in 0 data-width)
                                 (sis 'go 0 *queue20-l$go-num*)))
 (list* 'ready-in- 'ready-out
        (sis 'data-out 0 data-width))
 '(q10-l0 q10-l1)
 (list
  ;; LINKS
  ;; 10-link queue Q10-L0
  (list 'q10-l0
        (list* 'ready-in- 'q10-l0-ready-out
               (sis 'q10-l0-data-out 0 data-width))
        (si 'queue10-l data-width)
        (list* 'in-act 'trans-act
               (append (sis 'data-in 0 data-width)
                       (sis 'go
                            *queue20-l$prim-go-num*
                            *queue10-l$go-num*))))

  ;; 10-link queue Q10-L1
  (list 'q10-l1
        (list* 'q10-l1-ready-in- 'ready-out
               (sis 'data-out 0 data-width))
        (si 'queue10-l data-width)
        (list* 'trans-act 'out-act
               (append (sis 'q10-l1-data-in 0 data-width)
                       (sis 'go
                            (+ *queue20-l$prim-go-num*
                               *queue10-l$go-num*)
                            *queue10-l$go-num*))))

  ;; JOINT
  ;; Transfer data from Q10-L0 to Q10-L1
  (list 'trans-cntl
        '(trans-act)
        'joint-cntl
        (list 'q10-l0-ready-out 'q10-l1-ready-in- (si 'go 0)))
  (list 'trans-op
        (sis 'q10-l1-data-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'q10-l0-data-out 0 data-width)))

 (declare (xargs :guard (natp data-width))))

(make-event
 `(progn
    ,@(state-accessors-gen 'queue20-l '(q10-l0 q10-l1) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; QUEUE20-L.

(defund queue20-l$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (queue20-l* data-width)
        (union$ (queue10-l$netlist data-width)
                :test 'equal)))

;; Recognizer for QUEUE20-L

(defund queue20-l& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (b* ((subnetlist (delete-to-eq (si 'queue20-l data-width) netlist)))
    (and (equal (assoc (si 'queue20-l data-width) netlist)
                (queue20-l* data-width))
         (joint-cntl& subnetlist)
         (v-buf& subnetlist data-width)
         (queue10-l& subnetlist data-width))))

;; Sanity check

(local
 (defthmd check-queue20-l$netlist-64
   (and (net-syntax-okp (queue20-l$netlist 64))
        (net-arity-okp (queue20-l$netlist 64))
        (queue20-l& (queue20-l$netlist 64) 64))))

;; Constraints on the state of QUEUE20-L

(defund queue20-l$st-format (st data-width)
  (b* ((q10-l0 (get-field *queue20-l$q10-l0* st))
       (q10-l1 (get-field *queue20-l$q10-l1* st)))
    (and (queue10-l$st-format q10-l0 data-width)
         (queue10-l$st-format q10-l1 data-width))))

(defthm queue20-l$st-format=>constraint
  (implies (queue20-l$st-format st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue20-l$st-format)))
  :rule-classes :forward-chaining)

(defund queue20-l$valid-st (st data-width)
  (b* ((q10-l0 (get-field *queue20-l$q10-l0* st))
       (q10-l1 (get-field *queue20-l$q10-l1* st)))
    (and (queue10-l$valid-st q10-l0 data-width)
         (queue10-l$valid-st q10-l1 data-width))))

(defthmd queue20-l$valid-st=>constraint
  (implies (queue20-l$valid-st st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue10-l$valid-st=>constraint
                                     queue20-l$valid-st)))
  :rule-classes :forward-chaining)

(defthmd queue20-l$valid-st=>st-format
  (implies (queue20-l$valid-st st data-width)
           (queue20-l$st-format st data-width))
  :hints (("Goal" :in-theory (e/d (queue10-l$valid-st=>st-format
                                   queue20-l$st-format
                                   queue20-l$valid-st)
                                  ()))))

;; Extract the input and output signals for QUEUE20-L

(progn
  ;; Extract the "in-act" signal

  (defund queue20-l$in-act (inputs)
    (nth 0 inputs))

  ;; Extract the "out-act" signal

  (defund queue20-l$out-act (inputs)
    (nth 1 inputs))

  ;; Extract the input data

  (defun queue20-l$data-in (inputs data-width)
    (declare (xargs :guard (true-listp inputs)))
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 2 inputs)))

  (defthm len-queue20-l$data-in
    (equal (len (queue20-l$data-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable queue20-l$data-in))

  ;; Extract the inputs for the Q10-L0 link

  (defund queue20-l$q10-l0-inputs (inputs st data-width)
    (b* ((in-act (queue20-l$in-act inputs))
         (data-in (queue20-l$data-in inputs data-width))
         (go-signals (nthcdr (queue20-l$data-ins-len data-width) inputs))

         (go-trans (nth 0 go-signals))
         (q10-l0-go-signals (take *queue10-l$go-num*
                                  (nthcdr *queue20-l$prim-go-num* go-signals)))

         (q10-l0 (get-field *queue20-l$q10-l0* st))
         (q10-l1 (get-field *queue20-l$q10-l1* st))

         (trans-act (joint-act (queue10-l$ready-out q10-l0)
                               (queue10-l$ready-in- q10-l1)
                               go-trans)))

      (list* in-act trans-act
             (append data-in q10-l0-go-signals))))

  ;; Extract the inputs for the Q10-L1 link

  (defund queue20-l$q10-l1-inputs (inputs st data-width)
    (b* ((out-act (queue20-l$out-act inputs))
         (go-signals (nthcdr (queue20-l$data-ins-len data-width) inputs))

         (go-trans (nth 0 go-signals))
         (q10-l1-go-signals (take *queue10-l$go-num*
                                  (nthcdr (+ *queue20-l$prim-go-num*
                                             *queue10-l$go-num*)
                                          go-signals)))

         (q10-l0 (get-field *queue20-l$q10-l0* st))
         (q10-l1 (get-field *queue20-l$q10-l1* st))

         (trans-act (joint-act (queue10-l$ready-out q10-l0)
                               (queue10-l$ready-in- q10-l1)
                               go-trans)))

      (list* trans-act out-act
             (append (queue10-l$data-out q10-l0)
                     q10-l1-go-signals))))

  ;; Extract the "ready-in-" signal

  (defund queue20-l$ready-in- (st)
    (b* ((q10-l0 (get-field *queue20-l$q10-l0* st)))
      (queue10-l$ready-in- q10-l0)))

  (defthm booleanp-queue20-l$ready-in-
    (implies (queue20-l$valid-st st data-width)
             (booleanp (queue20-l$ready-in- st)))
    :hints (("Goal" :in-theory (enable queue20-l$valid-st
                                       queue20-l$ready-in-)))
    :rule-classes (:rewrite :type-prescription))

  ;; Extract the "ready-out" signal

  (defund queue20-l$ready-out (st)
    (b* ((q10-l1 (get-field *queue20-l$q10-l1* st)))
      (queue10-l$ready-out q10-l1)))

  (defthm booleanp-queue20-l$ready-out
    (implies (queue20-l$valid-st st data-width)
             (booleanp (queue20-l$ready-out st)))
    :hints (("Goal" :in-theory (enable queue20-l$valid-st
                                       queue20-l$ready-out)))
    :rule-classes (:rewrite :type-prescription))

  ;; Extract the output data

  (defund queue20-l$data-out (st)
    (b* ((q10-l1 (get-field *queue20-l$q10-l1* st)))
      (queue10-l$data-out q10-l1)))

  (defthm len-queue20-l$data-out-1
    (implies (queue20-l$st-format st data-width)
             (equal (len (queue20-l$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable queue20-l$st-format
                                       queue20-l$data-out))))

  (defthm len-queue20-l$data-out-2
    (implies (queue20-l$valid-st st data-width)
             (equal (len (queue20-l$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable queue20-l$valid-st
                                       queue20-l$data-out))))

  (defthm bvp-queue20-l$data-out
    (implies (and (queue20-l$valid-st st data-width)
                  (queue20-l$ready-out st))
             (bvp (queue20-l$data-out st)))
    :hints (("Goal" :in-theory (enable queue20-l$valid-st
                                       queue20-l$ready-out
                                       queue20-l$data-out))))

  (defun queue20-l$outputs (inputs st data-width)
    (declare (ignore inputs data-width))
    (list* (queue20-l$ready-in- st)
           (queue20-l$ready-out st)
           (queue20-l$data-out st)))
  )

;; The value lemma for QUEUE20-L

(defthm queue20-l$value
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue20-l& netlist data-width)
                  (queue20-l$st-format st data-width))
             (equal (se (si 'queue20-l data-width) inputs st netlist)
                    (queue20-l$outputs inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'queue20-l data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue20-l&
                            queue20-l*$destructure
                            queue20-l$st-format
                            queue20-l$ready-in-
                            queue20-l$ready-out
                            queue20-l$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of QUEUE20-L.

(defun queue20-l$step (inputs st data-width)
  (b* ((q10-l0 (get-field *queue20-l$q10-l0* st))
       (q10-l1 (get-field *queue20-l$q10-l1* st))

       (q10-l0-inputs (queue20-l$q10-l0-inputs inputs st data-width))
       (q10-l1-inputs (queue20-l$q10-l1-inputs inputs st data-width)))
    (list
     ;; Q10-L0
     (queue10-l$step q10-l0-inputs q10-l0 data-width)
     ;; Q10-L1
     (queue10-l$step q10-l1-inputs q10-l1 data-width))))

(defthm len-of-queue20-l$step
  (equal (len (queue20-l$step inputs st data-width))
         *queue20-l$st-len*))

(defthm queue20-l$step-v-threefix-of-data-in-canceled
  (implies
   (and (true-listp data-in)
        (equal (len data-in) data-width))
   (equal (queue20-l$step (list* in-act out-act
                                 (append (v-threefix data-in) go-signals))
                          st
                          data-width)
          (queue20-l$step (list* in-act out-act
                                 (append data-in go-signals))
                          st
                          data-width)))
  :hints (("Goal" :in-theory (enable queue20-l$step
                                     queue20-l$data-in
                                     queue20-l$q10-l0-inputs
                                     queue20-l$q10-l1-inputs
                                     queue20-l$in-act
                                     queue20-l$out-act))))

;; The state lemma for QUEUE20-L

(defthm queue20-l$state
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue20-l& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue20-l$go-num*)
                  (queue20-l$st-format st data-width))
             (equal (de (si 'queue20-l data-width) inputs st netlist)
                    (queue20-l$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'queue20-l data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue20-l&
                            queue20-l*$destructure
                            queue20-l$st-format
                            queue20-l$in-act
                            queue20-l$out-act
                            queue20-l$data-in
                            queue20-l$q10-l0-inputs
                            queue20-l$q10-l1-inputs)
                           (de-module-disabled-rules)))))

(in-theory (disable queue20-l$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund queue20-l$input-format (inputs st data-width)
  (b* ((in-act     (queue20-l$in-act inputs))
       (out-act    (queue20-l$out-act inputs))
       (data-in    (queue20-l$data-in inputs data-width))
       (go-signals (nthcdr (queue20-l$data-ins-len data-width) inputs))

       (ready-in- (queue20-l$ready-in- st))
       (ready-out (queue20-l$ready-out st)))
    (and
     (if ready-in-
         (not in-act)
       (booleanp in-act))
     (if (not ready-out)
         (not out-act)
       (booleanp out-act))
     (or (not in-act) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *queue20-l$go-num*)
     (equal inputs
            (list* in-act out-act (append data-in go-signals))))))

(local
 (defthm queue20-l$input-format=>q10-l0$input-format
   (implies (and (queue20-l$input-format inputs st data-width)
                 (queue20-l$valid-st st data-width))
            (queue10-l$input-format
             (queue20-l$q10-l0-inputs inputs st data-width)
             (nth *queue20-l$q10-l0* st)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             queue10-l$valid-st=>constraint
                             queue10-l$input-format
                             queue10-l$in-act
                             queue10-l$out-act
                             queue10-l$data-in
                             queue20-l$input-format
                             queue20-l$valid-st
                             queue20-l$ready-in-
                             queue20-l$q10-l0-inputs)
                            ())))))

(local
 (defthm queue20-l$input-format=>q10-l1$input-format
   (implies (and (queue20-l$input-format inputs st data-width)
                 (queue20-l$valid-st st data-width))
            (queue10-l$input-format
             (queue20-l$q10-l1-inputs inputs st data-width)
             (nth *queue20-l$q10-l1* st)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             joint-act
                             queue10-l$valid-st=>constraint
                             queue10-l$input-format
                             queue10-l$in-act
                             queue10-l$out-act
                             queue10-l$data-in
                             queue20-l$input-format
                             queue20-l$valid-st
                             queue20-l$ready-out
                             queue20-l$q10-l1-inputs)
                            ())))))

(defthm booleanp-queue20-l$in-act
  (implies (queue20-l$input-format inputs st data-wisth)
           (booleanp (queue20-l$in-act inputs)))
  :hints (("Goal" :in-theory (enable queue20-l$input-format
                                     queue20-l$in-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-queue20-l$out-act
  (implies (queue20-l$input-format inputs st data-wisth)
           (booleanp (queue20-l$out-act inputs)))
  :hints (("Goal" :in-theory (enable queue20-l$input-format
                                     queue20-l$out-act)))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma queue20-l :clink t)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for QUEUE20-L that extracts the future output
;; sequence from the current state.

(defund queue20-l$extract (st)
  (b* ((q10-l0 (get-field *queue20-l$q10-l0* st))
       (q10-l1 (get-field *queue20-l$q10-l1* st)))
    (append (queue10-l$extract q10-l0)
            (queue10-l$extract q10-l1))))

(defthm queue20-l$extract-not-empty
  (implies (and (queue20-l$ready-out st)
                (queue20-l$valid-st st data-width))
           (< 0 (len (queue20-l$extract st))))
  :hints (("Goal" :in-theory (e/d (queue20-l$valid-st
                                   queue20-l$extract
                                   queue20-l$ready-out)
                                  ())))
  :rule-classes :linear)

;; The extracted next-state function for QUEUE20-L.  Note that this function
;; avoids exploring the internal computation of QUEUE20-L.

(defund queue20-l$extracted-step (inputs st data-width)
  (b* ((data (queue20-l$data-in inputs data-width))
       (extracted-st (queue20-l$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue20-l$out-act inputs) t)
      (cond
       ((equal (queue20-l$in-act inputs) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue20-l$in-act inputs) t)
          (cons data extracted-st))
         (t extracted-st))))))

(local
 (defthm queue10-l$ready-out-lemma
   (implies (and (queue10-l$valid-st st data-width)
                 (equal (len (queue10-l$extract st)) 0))
            (not (queue10-l$ready-out st)))
   :hints (("Goal" :in-theory (enable queue10-l$valid-st
                                      queue10-l$extract
                                      queue10-l$ready-out)))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm queue20-l$q10-l0-data-in-rewrite
     (equal (queue10-l$data-in
             (queue20-l$q10-l0-inputs inputs st data-width)
             data-width)
            (queue20-l$data-in inputs data-width))
     :hints (("Goal"
              :in-theory (enable queue10-l$data-in
                                 queue20-l$data-in
                                 queue20-l$q10-l0-inputs)))))

  (local
   (defthm queue20-l$q10-l1-data-in-rewrite
     (b* ((q10-l0 (nth *queue20-l$q10-l0* st)))
       (implies (queue10-l$valid-st q10-l0 data-width)
                (equal (queue10-l$data-in
                        (queue20-l$q10-l1-inputs inputs st data-width)
                        data-width)
                       (queue10-l$data-out q10-l0))))
     :hints (("Goal"
              :use (:instance queue10-l$valid-st=>constraint
                              (st (nth *queue20-l$q10-l0* st)))
              :in-theory (enable get-field
                                 queue10-l$valid-st
                                 queue10-l$data-in
                                 queue10-l$data-out
                                 queue20-l$q10-l1-inputs)))))

  (local
   (defthm queue20-l$q10-l1-in-act-=-q10-l0-out-act
     (equal (queue10-l$in-act (queue20-l$q10-l1-inputs inputs st data-width))
            (queue10-l$out-act (queue20-l$q10-l0-inputs inputs st data-width)))
     :hints (("Goal" :in-theory (enable queue10-l$in-act
                                        queue10-l$out-act
                                        queue20-l$q10-l0-inputs
                                        queue20-l$q10-l1-inputs)))))

  (local
   (defthm queue20-l$q10-l0-in-act-rewrite
     (equal (queue10-l$in-act (queue20-l$q10-l0-inputs inputs st data-width))
            (queue20-l$in-act inputs))
     :hints (("Goal" :in-theory (enable queue10-l$in-act
                                        queue20-l$in-act
                                        queue20-l$q10-l0-inputs)))))

  (local
   (defthm queue20-l$q10-l1-out-act-rewrite
     (equal (queue10-l$out-act (queue20-l$q10-l1-inputs inputs st data-width))
            (queue20-l$out-act inputs))
     :hints (("Goal" :in-theory (enable queue10-l$out-act
                                        queue20-l$out-act
                                        queue20-l$q10-l1-inputs)))))

  (local
   (defthm queue20-l$extracted-step-correct-aux-1
     (equal (append x (cons e (queue10-l$extract st)))
            (append (append x (list e))
                    (queue10-l$extract st)))))

  (local
   (defthm queue20-l$extracted-step-correct-aux-2
     (equal (append x (cons e (take n (queue10-l$extract st))))
            (append (append x (list e))
                    (take n (queue10-l$extract st))))))

  (defthm queue20-l$extracted-step-correct
    (b* ((next-st (queue20-l$step inputs st data-width)))
      (implies (and (queue20-l$input-format inputs st data-width)
                    (queue20-l$valid-st st data-width))
               (equal (queue20-l$extract next-st)
                      (queue20-l$extracted-step inputs st data-width))))
    :hints (("Goal"
             :use queue20-l$input-format=>q10-l0$input-format
             :in-theory (e/d (get-field
                              queue10-l$valid-st=>constraint
                              queue10-l$extracted-step
                              queue20-l$extracted-step
                              queue20-l$input-format
                              queue20-l$valid-st
                              queue20-l$step
                              queue20-l$in-act
                              queue20-l$out-act
                              queue20-l$ready-in-
                              queue20-l$ready-out
                              queue20-l$extract)
                             (queue20-l$input-format=>q10-l0$input-format)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that queue20-l$valid-st is an invariant.

(defthm queue20-l$valid-st-preserved
  (implies (and (queue20-l$input-format inputs st data-width)
                (queue20-l$valid-st st data-width))
           (queue20-l$valid-st (queue20-l$step inputs st data-width)
                             data-width))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue20-l$valid-st
                            queue20-l$step)
                           ()))))

(encapsulate
  ()

  (local
   (defthm queue20-l$q10-l1-out-act-fire
     (implies (nth 1 inputs)
              (queue10-l$out-act (queue20-l$q10-l1-inputs inputs st data-width)))
     :hints (("Goal" :in-theory (enable queue10-l$out-act
                                        queue20-l$out-act
                                        queue20-l$q10-l1-inputs)))))

  (defthm queue20-l$extract-lemma-1
    (implies (and (queue20-l$input-format inputs st data-width)
                  (queue20-l$valid-st st data-width)
                  (queue20-l$out-act inputs))
             (equal (list (queue20-l$data-out st))
                    (nthcdr (1- (len (queue20-l$extract st)))
                            (queue20-l$extract st))))
    :hints (("Goal"
             :do-not-induct t
             :use queue20-l$input-format=>q10-l1$input-format
             :in-theory (e/d (get-field
                              queue10-l$valid-st=>constraint
                              queue20-l$input-format
                              queue20-l$valid-st
                              queue20-l$extract
                              queue20-l$out-act
                              queue20-l$ready-out
                              queue20-l$data-out)
                             (queue20-l$input-format=>q10-l1$input-format)))))

  (defthmd queue20-l$extract-lemma-2
    (implies (and (queue20-l$valid-st st data-width)
                  (queue20-l$ready-out st))
             (equal (list (queue20-l$data-out st))
                    (nthcdr (1- (len (queue20-l$extract st)))
                            (queue20-l$extract st))))
    :hints (("Goal" :in-theory (e/d (queue10-l$extract-lemma-2
                                     queue20-l$valid-st
                                     queue20-l$ready-out
                                     queue20-l$data-out
                                     queue20-l$extract)
                                    ()))))
  )

;; Extract the accepted input sequence

(seq-gen queue20-l in in-act -1
         (queue20-l$data-in inputs data-width)
         :clink t)

;; Extract the valid output sequence

(seq-gen queue20-l out out-act -1
         (queue20-l$data-out st)
         :netlist-data (nthcdr 2 outputs)
         :clink t)

;; The multi-step input-output relationship

(in-out-stream-lemma queue20-l :clink t)

