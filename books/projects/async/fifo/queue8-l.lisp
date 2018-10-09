;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2018

(in-package "ADE")

(include-book "queue4-l")

(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of QUEUE8-L
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of QUEUE8-L
;;
;; Construct a DE module generator for a queue of 8 links, QUEUE8-L, using the
;; link-joint model.  Prove the value and state lemmas for this module
;; generator.  Note that QUEUE8-L is a complex link.  It is constructed by
;; concatenating two instances of QUEUE4-L via a buffer joint.

(defconst *queue8-l$prim-go-num* 1)
(defconst *queue8-l$go-num* (+ *queue8-l$prim-go-num*
                               (* 2 *queue4-l$go-num*)))
(defconst *queue8-l$st-len* 2)

(defun queue8-l$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun queue8-l$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (queue8-l$data-ins-len data-width)
     *queue8-l$go-num*))

;; DE module generator of QUEUE8-L

(module-generator
 queue8-l* (data-width)
 (si 'queue8-l data-width)
 (list* 'in-act 'out-act (append (sis 'data-in 0 data-width)
                                 (sis 'go 0 *queue8-l$go-num*)))
 (list* 'ready-in- 'ready-out
        (sis 'data-out 0 data-width))
 '(q4-l0 q4-l1)
 (list
  ;; LINKS
  ;; 4-link queue Q4-L0
  (list 'q4-l0
        (list* 'ready-in- 'q4-l0-ready-out
               (sis 'q4-l0-data-out 0 data-width))
        (si 'queue4-l data-width)
        (list* 'in-act 'trans-act
               (append (sis 'data-in 0 data-width)
                       (sis 'go
                            *queue8-l$prim-go-num*
                            *queue4-l$go-num*))))

  ;; 4-link queue Q4-L1
  (list 'q4-l1
        (list* 'q4-l1-ready-in- 'ready-out
               (sis 'data-out 0 data-width))
        (si 'queue4-l data-width)
        (list* 'trans-act 'out-act
               (append (sis 'q4-l1-data-in 0 data-width)
                       (sis 'go
                            (+ *queue8-l$prim-go-num*
                               *queue4-l$go-num*)
                            *queue4-l$go-num*))))

  ;; JOINT
  ;; Transfer data from Q4-L0 to Q4-L1
  (list 'trans-cntl
        '(trans-act)
        'joint-cntl
        (list 'q4-l0-ready-out 'q4-l1-ready-in- (si 'go 0)))
  (list 'trans-op
        (sis 'q4-l1-data-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'q4-l0-data-out 0 data-width)))

 :guard (natp data-width))

(make-event
 `(progn
    ,@(state-accessors-gen 'queue8-l '(q4-l0 q4-l1) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; QUEUE8-L.

(defun queue8-l$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (queue8-l* data-width)
        (union$ (queue4-l$netlist data-width)
                :test 'equal)))

;; Recognizer for QUEUE8-L

(defund queue8-l& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (and (equal (assoc (si 'queue8-l data-width) netlist)
              (queue8-l* data-width))
       (b* ((netlist (delete-to-eq (si 'queue8-l data-width) netlist)))
         (and (joint-cntl& netlist)
              (v-buf& netlist data-width)
              (queue4-l& netlist data-width)))))

;; Sanity check

(local
 (defthmd check-queue8-l$netlist-64
   (and (net-syntax-okp (queue8-l$netlist 64))
        (net-arity-okp (queue8-l$netlist 64))
        (queue8-l& (queue8-l$netlist 64) 64))))

;; Constraints on the state of QUEUE8-L

(defund queue8-l$st-format (st data-width)
  (b* ((q4-l0 (get-field *queue8-l$q4-l0* st))
       (q4-l1 (get-field *queue8-l$q4-l1* st)))
    (and (queue4-l$st-format q4-l0 data-width)
         (queue4-l$st-format q4-l1 data-width))))

(defthm queue8-l$st-format=>data-width-constraint
  (implies (queue8-l$st-format st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue8-l$st-format)))
  :rule-classes :forward-chaining)

(defund queue8-l$valid-st (st data-width)
  (b* ((q4-l0 (get-field *queue8-l$q4-l0* st))
       (q4-l1 (get-field *queue8-l$q4-l1* st)))
    (and (queue4-l$valid-st q4-l0 data-width)
         (queue4-l$valid-st q4-l1 data-width))))

(defthmd queue8-l$valid-st=>data-width-constraint
  (implies (queue8-l$valid-st st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue4-l$valid-st=>data-width-constraint
                                     queue8-l$valid-st)))
  :rule-classes :forward-chaining)

(defthmd queue8-l$valid-st=>st-format
  (implies (queue8-l$valid-st st data-width)
           (queue8-l$st-format st data-width))
  :hints (("Goal" :in-theory (e/d (queue4-l$valid-st=>st-format
                                   queue8-l$st-format
                                   queue8-l$valid-st)
                                  ()))))

;; Extract the input and output signals for QUEUE8-L

(progn
  ;; Extract the "in-act" signal

  (defund queue8-l$in-act (inputs)
    (nth 0 inputs))

  ;; Extract the "out-act" signal

  (defund queue8-l$out-act (inputs)
    (nth 1 inputs))

  ;; Extract the input data

  (defun queue8-l$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 2 inputs)))

  (defthm len-queue8-l$data-in
    (equal (len (queue8-l$data-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable queue8-l$data-in))

  ;; Extract the inputs for the Q4-L0 link

  (defund queue8-l$q4-l0-inputs (inputs st data-width)
    (b* ((in-act (queue8-l$in-act inputs))
         (data-in (queue8-l$data-in inputs data-width))
         (go-signals (nthcdr (queue8-l$data-ins-len data-width) inputs))

         (go-trans (nth 0 go-signals))
         (q4-l0-go-signals (take *queue4-l$go-num*
                                 (nthcdr *queue8-l$prim-go-num*
                                         go-signals)))

         (q4-l0 (get-field *queue8-l$q4-l0* st))
         (q4-l1 (get-field *queue8-l$q4-l1* st))

         (trans-act (joint-act (queue4-l$ready-out q4-l0)
                               (queue4-l$ready-in- q4-l1)
                               go-trans)))

      (list* in-act trans-act
             (append data-in q4-l0-go-signals))))

  ;; Extract the inputs for the Q4-L1 link

  (defund queue8-l$q4-l1-inputs (inputs st data-width)
    (b* ((out-act (queue8-l$out-act inputs))
         (go-signals (nthcdr (queue8-l$data-ins-len data-width) inputs))

         (go-trans (nth 0 go-signals))
         (q4-l1-go-signals (take *queue4-l$go-num*
                                 (nthcdr (+ *queue8-l$prim-go-num*
                                            *queue4-l$go-num*)
                                         go-signals)))

         (q4-l0 (get-field *queue8-l$q4-l0* st))
         (q4-l1 (get-field *queue8-l$q4-l1* st))

         (trans-act (joint-act (queue4-l$ready-out q4-l0)
                               (queue4-l$ready-in- q4-l1)
                               go-trans)))

      (list* trans-act out-act
             (append (queue4-l$data-out q4-l0)
                     q4-l1-go-signals))))

  ;; Extract the "ready-in-" signal

  (defund queue8-l$ready-in- (st)
    (b* ((q4-l0 (get-field *queue8-l$q4-l0* st)))
      (queue4-l$ready-in- q4-l0)))

  (defthm booleanp-queue8-l$ready-in-
    (implies (queue8-l$valid-st st data-width)
             (booleanp (queue8-l$ready-in- st)))
    :hints (("Goal" :in-theory (enable queue8-l$valid-st
                                       queue8-l$ready-in-)))
    :rule-classes :type-prescription)

  ;; Extract the "ready-out" signal

  (defund queue8-l$ready-out (st)
    (b* ((q4-l1 (get-field *queue8-l$q4-l1* st)))
      (queue4-l$ready-out q4-l1)))

  (defthm booleanp-queue8-l$ready-out
    (implies (queue8-l$valid-st st data-width)
             (booleanp (queue8-l$ready-out st)))
    :hints (("Goal" :in-theory (enable queue8-l$valid-st
                                       queue8-l$ready-out)))
    :rule-classes :type-prescription)

  ;; Extract the output data

  (defund queue8-l$data-out (st)
    (b* ((q4-l1 (get-field *queue8-l$q4-l1* st)))
      (queue4-l$data-out q4-l1)))

  (defthm len-queue8-l$data-out-1
    (implies (queue8-l$st-format st data-width)
             (equal (len (queue8-l$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable queue8-l$st-format
                                       queue8-l$data-out))))

  (defthm len-queue8-l$data-out-2
    (implies (queue8-l$valid-st st data-width)
             (equal (len (queue8-l$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable queue8-l$valid-st
                                       queue8-l$data-out))))

  (defthm bvp-queue8-l$data-out
    (implies (and (queue8-l$valid-st st data-width)
                  (queue8-l$ready-out st))
             (bvp (queue8-l$data-out st)))
    :hints (("Goal" :in-theory (enable queue8-l$valid-st
                                       queue8-l$ready-out
                                       queue8-l$data-out))))

  (defun queue8-l$outputs (inputs st data-width)
    (declare (ignore inputs data-width))
    (list* (queue8-l$ready-in- st)
           (queue8-l$ready-out st)
           (queue8-l$data-out st)))
  )

;; Prove that QUEUE8-L is not a DE primitive.

(not-primp-lemma queue8-l)

;; The value lemma for QUEUE8-L

(defthmd queue8-l$value
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue8-l& netlist data-width)
                  (queue8-l$st-format st data-width))
             (equal (se (si 'queue8-l data-width) inputs st netlist)
                    (queue8-l$outputs inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'queue8-l data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue8-l&
                            queue8-l*$destructure
                            joint-cntl$value
                            v-buf$value
                            queue4-l$value
                            queue8-l$st-format
                            queue8-l$ready-in-
                            queue8-l$ready-out
                            queue8-l$data-out)
                           ((queue8-l*)
                            de-module-disabled-rules)))))

;; This function specifies the next state of QUEUE8-L.

(defun queue8-l$step (inputs st data-width)
  (b* ((q4-l0 (get-field *queue8-l$q4-l0* st))
       (q4-l1 (get-field *queue8-l$q4-l1* st))

       (q4-l0-inputs (queue8-l$q4-l0-inputs inputs st data-width))
       (q4-l1-inputs (queue8-l$q4-l1-inputs inputs st data-width)))
    (list
     ;; Q4-L0
     (queue4-l$step q4-l0-inputs q4-l0 data-width)
     ;; Q4-L1
     (queue4-l$step q4-l1-inputs q4-l1 data-width))))

(defthm len-of-queue8-l$step
  (equal (len (queue8-l$step inputs st data-width))
         *queue8-l$st-len*))

(defthm queue8-l$step-v-threefix-of-data-in-canceled
  (implies
   (and (true-listp data-in)
        (equal (len data-in) data-width))
   (equal (queue8-l$step (list* in-act out-act
                                (append (v-threefix data-in) go-signals))
                         st
                         data-width)
          (queue8-l$step (list* in-act out-act
                                (append data-in go-signals))
                         st
                         data-width)))
  :hints (("Goal" :in-theory (enable queue8-l$step
                                     queue8-l$data-in
                                     queue8-l$q4-l0-inputs
                                     queue8-l$q4-l1-inputs
                                     queue8-l$in-act
                                     queue8-l$out-act))))

;; The state lemma for QUEUE8-L

(defthmd queue8-l$state
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue8-l& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue8-l$go-num*)
                  (queue8-l$st-format st data-width))
             (equal (de (si 'queue8-l data-width) inputs st netlist)
                    (queue8-l$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'queue8-l data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue8-l&
                            queue8-l*$destructure
                            queue8-l$st-format
                            queue8-l$in-act
                            queue8-l$out-act
                            queue8-l$data-in
                            queue8-l$q4-l0-inputs
                            queue8-l$q4-l1-inputs
                            joint-cntl$value
                            v-buf$value
                            queue4-l$value
                            queue4-l$state)
                           ((queue8-l*)
                            de-module-disabled-rules)))))

(in-theory (disable queue8-l$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund queue8-l$input-format (inputs st data-width)
  (b* ((in-act     (queue8-l$in-act inputs))
       (out-act    (queue8-l$out-act inputs))
       (data-in    (queue8-l$data-in inputs data-width))
       (go-signals (nthcdr (queue8-l$data-ins-len data-width) inputs))

       (ready-in- (queue8-l$ready-in- st))
       (ready-out (queue8-l$ready-out st)))
    (and
     (if ready-in-
         (not in-act)
       (booleanp in-act))
     (if (not ready-out)
         (not out-act)
       (booleanp out-act))
     (or (not in-act) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *queue8-l$go-num*)
     (equal inputs
            (list* in-act out-act (append data-in go-signals))))))

(local
 (defthm queue8-l$input-format=>q4-l0$input-format
   (implies (and (queue8-l$input-format inputs st data-width)
                 (queue8-l$valid-st st data-width))
            (queue4-l$input-format
             (queue8-l$q4-l0-inputs inputs st data-width)
             (nth *queue8-l$q4-l0* st)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             queue4-l$valid-st=>data-width-constraint
                             queue4-l$input-format
                             queue4-l$in-act
                             queue4-l$out-act
                             queue4-l$data-in
                             queue8-l$input-format
                             queue8-l$valid-st
                             queue8-l$ready-in-
                             queue8-l$q4-l0-inputs)
                            ())))))

(local
 (defthm queue8-l$input-format=>q4-l1$input-format
   (implies (and (queue8-l$input-format inputs st data-width)
                 (queue8-l$valid-st st data-width))
            (queue4-l$input-format
             (queue8-l$q4-l1-inputs inputs st data-width)
             (nth *queue8-l$q4-l1* st)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             joint-act
                             queue4-l$valid-st=>data-width-constraint
                             queue4-l$input-format
                             queue4-l$in-act
                             queue4-l$out-act
                             queue4-l$data-in
                             queue8-l$input-format
                             queue8-l$valid-st
                             queue8-l$ready-out
                             queue8-l$q4-l1-inputs)
                            ())))))

(defthm booleanp-queue8-l$in-act
  (implies (queue8-l$input-format inputs st data-wisth)
           (booleanp (queue8-l$in-act inputs)))
  :hints (("Goal" :in-theory (enable queue8-l$input-format
                                     queue8-l$in-act)))
  :rule-classes :type-prescription)

(defthm booleanp-queue8-l$out-act
  (implies (queue8-l$input-format inputs st data-wisth)
           (booleanp (queue8-l$out-act inputs)))
  :hints (("Goal" :in-theory (enable queue8-l$input-format
                                     queue8-l$out-act)))
  :rule-classes :type-prescription)

(simulate-lemma queue8-l :clink t)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for QUEUE8-L that extracts the future output
;; sequence from the current state.

(defund queue8-l$extract (st)
  (b* ((q4-l0 (get-field *queue8-l$q4-l0* st))
       (q4-l1 (get-field *queue8-l$q4-l1* st)))
    (append (queue4-l$extract q4-l0)
            (queue4-l$extract q4-l1))))

(defthm queue8-l$extract-not-empty
  (implies (and (queue8-l$ready-out st)
                (queue8-l$valid-st st data-width))
           (< 0 (len (queue8-l$extract st))))
  :hints (("Goal" :in-theory (e/d (queue8-l$valid-st
                                   queue8-l$extract
                                   queue8-l$ready-out)
                                  ())))
  :rule-classes :linear)

;; The extracted next-state function for QUEUE8-L.  Note that this function
;; avoids exploring the internal computation of QUEUE8-L.

(defund queue8-l$extracted-step (inputs st data-width)
  (b* ((data (queue8-l$data-in inputs data-width))
       (extracted-st (queue8-l$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue8-l$out-act inputs) t)
      (cond
       ((equal (queue8-l$in-act inputs) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue8-l$in-act inputs) t)
          (cons data extracted-st))
         (t extracted-st))))))

(local
 (defthm queue4-l$ready-out-lemma
   (implies (and (queue4-l$valid-st st data-width)
                 (equal (len (queue4-l$extract st)) 0))
            (not (queue4-l$ready-out st)))
   :hints (("Goal" :in-theory (enable queue4-l$valid-st
                                      queue4-l$extract
                                      queue4-l$ready-out)))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm queue8-l$q4-l0-data-in-rewrite
     (equal (queue4-l$data-in
             (queue8-l$q4-l0-inputs inputs st data-width)
             data-width)
            (queue8-l$data-in inputs data-width))
     :hints (("Goal"
              :in-theory (enable queue4-l$data-in
                                 queue8-l$data-in
                                 queue8-l$q4-l0-inputs)))))

  (local
   (defthm queue8-l$q4-l1-data-in-rewrite
     (b* ((q4-l0 (nth *queue8-l$q4-l0* st)))
       (implies (queue4-l$valid-st q4-l0 data-width)
                (equal (queue4-l$data-in
                        (queue8-l$q4-l1-inputs inputs st data-width)
                        data-width)
                       (queue4-l$data-out q4-l0))))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue4-l$valid-st
                                 queue4-l$data-in
                                 queue4-l$data-out
                                 queue8-l$q4-l1-inputs)))))

  (local
   (defthm queue8-l$q4-l1-in-act-=-q4-l0-out-act
     (equal (queue4-l$in-act (queue8-l$q4-l1-inputs inputs st data-width))
            (queue4-l$out-act (queue8-l$q4-l0-inputs inputs st data-width)))
     :hints (("Goal" :in-theory (enable queue4-l$in-act
                                        queue4-l$out-act
                                        queue8-l$q4-l0-inputs
                                        queue8-l$q4-l1-inputs)))))

  (local
   (defthm queue8-l$q4-l0-in-act-rewrite
     (equal (queue4-l$in-act (queue8-l$q4-l0-inputs inputs st data-width))
            (queue8-l$in-act inputs))
     :hints (("Goal" :in-theory (enable queue4-l$in-act
                                        queue8-l$in-act
                                        queue8-l$q4-l0-inputs)))))

  (local
   (defthm queue8-l$q4-l1-out-act-rewrite
     (equal (queue4-l$out-act (queue8-l$q4-l1-inputs inputs st data-width))
            (queue8-l$out-act inputs))
     :hints (("Goal" :in-theory (enable queue4-l$out-act
                                        queue8-l$out-act
                                        queue8-l$q4-l1-inputs)))))

  (local
   (defthm queue8-l$extracted-step-correct-aux-1
     (equal (append x (cons e (queue4-l$extract st)))
            (append (append x (list e))
                    (queue4-l$extract st)))))

  (local
   (defthm queue8-l$extracted-step-correct-aux-2
     (equal (append x (cons e (take n (queue4-l$extract st))))
            (append (append x (list e))
                    (take n (queue4-l$extract st))))))

  (defthm queue8-l$extracted-step-correct
    (b* ((next-st (queue8-l$step inputs st data-width)))
      (implies (and (queue8-l$input-format inputs st data-width)
                    (queue8-l$valid-st st data-width))
               (equal (queue8-l$extract next-st)
                      (queue8-l$extracted-step inputs st data-width))))
    :hints (("Goal"
             :use queue8-l$input-format=>q4-l0$input-format
             :in-theory (e/d (get-field
                              queue4-l$valid-st=>data-width-constraint
                              queue4-l$extracted-step
                              queue8-l$extracted-step
                              queue8-l$input-format
                              queue8-l$valid-st
                              queue8-l$step
                              queue8-l$in-act
                              queue8-l$out-act
                              queue8-l$ready-in-
                              queue8-l$ready-out
                              queue8-l$extract)
                             (queue8-l$input-format=>q4-l0$input-format)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that queue8-l$valid-st is an invariant.

(defthm queue8-l$valid-st-preserved
  (implies (and (queue8-l$input-format inputs st data-width)
                (queue8-l$valid-st st data-width))
           (queue8-l$valid-st (queue8-l$step inputs st data-width)
                            data-width))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue8-l$valid-st
                            queue8-l$step)
                           ()))))

(encapsulate
  ()

  (local
   (defthm queue8-l$q4-l1-out-act-fire
     (implies (nth 1 inputs)
              (queue4-l$out-act (queue8-l$q4-l1-inputs inputs st data-width)))
     :hints (("Goal" :in-theory (enable queue4-l$out-act
                                        queue8-l$out-act
                                        queue8-l$q4-l1-inputs)))))

  (defthm queue8-l$extract-lemma-1
    (implies (and (queue8-l$input-format inputs st data-width)
                  (queue8-l$valid-st st data-width)
                  (queue8-l$out-act inputs))
             (equal (list (queue8-l$data-out st))
                    (nthcdr (1- (len (queue8-l$extract st)))
                            (queue8-l$extract st))))
    :hints (("Goal"
             :do-not-induct t
             :use queue8-l$input-format=>q4-l1$input-format
             :in-theory (e/d (get-field
                              queue4-l$valid-st=>data-width-constraint
                              queue8-l$input-format
                              queue8-l$valid-st
                              queue8-l$extract
                              queue8-l$out-act
                              queue8-l$ready-out
                              queue8-l$data-out)
                             (queue8-l$input-format=>q4-l1$input-format)))))

  (defthmd queue8-l$extract-lemma-2
    (implies (and (queue8-l$valid-st st data-width)
                  (queue8-l$ready-out st))
             (equal (list (queue8-l$data-out st))
                    (nthcdr (1- (len (queue8-l$extract st)))
                            (queue8-l$extract st))))
    :hints (("Goal" :in-theory (e/d (queue4-l$extract-lemma-2
                                     queue8-l$valid-st
                                     queue8-l$ready-out
                                     queue8-l$data-out
                                     queue8-l$extract)
                                    ()))))
  )

;; Extract the accepted input sequence

(seq-gen queue8-l in in-act -1
         (queue8-l$data-in inputs data-width)
         :clink t)

;; Extract the valid output sequence

(seq-gen queue8-l out out-act -1
         (queue8-l$data-out st)
         :netlist-data (nthcdr 2 outputs)
         :clink t)

;; The multi-step input-output relationship

(in-out-stream-lemma queue8-l :clink t)

