;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "queue5-l")

(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of QUEUE10-L
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of QUEUE10-L
;;
;; Construct a DE module generator for a queue of 10 links, QUEUE10-L, using
;; the link-joint model.  Prove the value and state lemmas for this module
;; generator.  Note that QUEUE10-L is a complex link.  It is constructed by
;; concatenating two instances of QUEUE5-L via a buffer joint.

(defconst *queue10-l$prim-go-num* 1)
(defconst *queue10-l$go-num* (+ *queue10-l$prim-go-num*
                                (* 2 *queue5-l$go-num*)))

(defun queue10-l$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (mbe :logic (nfix data-size)
            :exec  data-size)))

(defun queue10-l$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (queue10-l$data-ins-len data-size)
     *queue10-l$go-num*))

;; DE module generator of QUEUE10-L

(module-generator
 queue10-l* (data-size)
 (si 'queue10-l data-size)
 (list* 'in-act 'out-act (append (sis 'data-in 0 data-size)
                                 (sis 'go 0 *queue10-l$go-num*)))
 (list* 'ready-in- 'ready-out
        (sis 'data-out 0 data-size))
 '(q5-l0 q5-l1)
 (list
  ;; LINKS
  ;; 5-link queue Q5-L0
  (list 'q5-l0
        (list* 'ready-in- 'q5-l0-ready-out
               (sis 'q5-l0-data-out 0 data-size))
        (si 'queue5-l data-size)
        (list* 'in-act 'trans-act
               (append (sis 'data-in 0 data-size)
                       (sis 'go
                            *queue10-l$prim-go-num*
                            *queue5-l$go-num*))))

  ;; 5-link queue Q5-L1
  (list 'q5-l1
        (list* 'q5-l1-ready-in- 'ready-out
               (sis 'data-out 0 data-size))
        (si 'queue5-l data-size)
        (list* 'trans-act 'out-act
               (append (sis 'q5-l1-data-in 0 data-size)
                       (sis 'go
                            (+ *queue10-l$prim-go-num*
                               *queue5-l$go-num*)
                            *queue5-l$go-num*))))

  ;; JOINT
  ;; Transfer data from Q5-L0 to Q5-L1
  (list 'trans-cntl
        '(trans-act)
        'joint-cntl
        (list 'q5-l0-ready-out 'q5-l1-ready-in- (si 'go 0)))
  (list 'trans-op
        (sis 'q5-l1-data-in 0 data-size)
        (si 'v-buf data-size)
        (sis 'q5-l0-data-out 0 data-size)))

 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'queue10-l '(q5-l0 q5-l1) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; QUEUE10-L.

(defund queue10-l$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (queue10-l* data-size)
        (union$ (queue5-l$netlist data-size)
                :test 'equal)))

;; Recognizer for QUEUE10-L

(defund queue10-l& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'queue10-l data-size) netlist)))
    (and (equal (assoc (si 'queue10-l data-size) netlist)
                (queue10-l* data-size))
         (joint-cntl& subnetlist)
         (v-buf& subnetlist data-size)
         (queue5-l& subnetlist data-size))))

;; Sanity check

(local
 (defthmd check-queue10-l$netlist-64
   (and (net-syntax-okp (queue10-l$netlist 64))
        (net-arity-okp (queue10-l$netlist 64))
        (queue10-l& (queue10-l$netlist 64) 64))))

;; Constraints on the state of QUEUE10-L

(defund queue10-l$st-format (st data-size)
  (b* ((q5-l0 (nth *queue10-l$q5-l0* st))
       (q5-l1 (nth *queue10-l$q5-l1* st)))
    (and (queue5-l$st-format q5-l0 data-size)
         (queue5-l$st-format q5-l1 data-size))))

(defthm queue10-l$st-format=>constraint
  (implies (queue10-l$st-format st data-size)
           (natp data-size))
  :hints (("Goal" :in-theory (enable queue10-l$st-format)))
  :rule-classes :forward-chaining)

(defund queue10-l$valid-st (st data-size)
  (b* ((q5-l0 (nth *queue10-l$q5-l0* st))
       (q5-l1 (nth *queue10-l$q5-l1* st)))
    (and (queue5-l$valid-st q5-l0 data-size)
         (queue5-l$valid-st q5-l1 data-size))))

(defthmd queue10-l$valid-st=>constraint
  (implies (queue10-l$valid-st st data-size)
           (natp data-size))
  :hints (("Goal" :in-theory (enable queue5-l$valid-st=>constraint
                                     queue10-l$valid-st)))
  :rule-classes :forward-chaining)

(defthmd queue10-l$valid-st=>st-format
  (implies (queue10-l$valid-st st data-size)
           (queue10-l$st-format st data-size))
  :hints (("Goal" :in-theory (e/d (queue5-l$valid-st=>st-format
                                   queue10-l$st-format
                                   queue10-l$valid-st)
                                  ()))))

;; Extract the input and output signals for QUEUE10-L

(progn
  ;; Extract the "in-act" signal

  (defund queue10-l$in-act (inputs)
    (nth 0 inputs))

  ;; Extract the "out-act" signal

  (defund queue10-l$out-act (inputs)
    (nth 1 inputs))

  ;; Extract the input data

  (defun queue10-l$data-in (inputs data-size)
    (declare (xargs :guard (true-listp inputs)))
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (mbe :logic (nfix data-size)
               :exec  data-size)
          (nthcdr 2 inputs)))

  (defthm len-queue10-l$data-in
    (equal (len (queue10-l$data-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable queue10-l$data-in))

  ;; Extract the inputs for the Q5-L0 link

  (defund queue10-l$q5-l0-inputs (inputs st data-size)
    (b* ((in-act (queue10-l$in-act inputs))
         (data-in (queue10-l$data-in inputs data-size))
         (go-signals (nthcdr (queue10-l$data-ins-len data-size) inputs))

         (go-trans (nth 0 go-signals))
         (q5-l0-go-signals (take *queue5-l$go-num*
                                 (nthcdr *queue10-l$prim-go-num* go-signals)))

         (q5-l0 (nth *queue10-l$q5-l0* st))
         (q5-l1 (nth *queue10-l$q5-l1* st))

         (trans-act (joint-act (queue5-l$ready-out q5-l0)
                               (queue5-l$ready-in- q5-l1)
                               go-trans)))

      (list* in-act trans-act
             (append data-in q5-l0-go-signals))))

  ;; Extract the inputs for the Q5-L1 link

  (defund queue10-l$q5-l1-inputs (inputs st data-size)
    (b* ((out-act (queue10-l$out-act inputs))
         (go-signals (nthcdr (queue10-l$data-ins-len data-size) inputs))

         (go-trans (nth 0 go-signals))
         (q5-l1-go-signals (take *queue5-l$go-num*
                                 (nthcdr (+ *queue10-l$prim-go-num*
                                            *queue5-l$go-num*)
                                         go-signals)))

         (q5-l0 (nth *queue10-l$q5-l0* st))
         (q5-l1 (nth *queue10-l$q5-l1* st))

         (trans-act (joint-act (queue5-l$ready-out q5-l0)
                               (queue5-l$ready-in- q5-l1)
                               go-trans)))

      (list* trans-act out-act
             (append (queue5-l$data-out q5-l0)
                     q5-l1-go-signals))))

  ;; Extract the "ready-in-" signal

  (defund queue10-l$ready-in- (st)
    (b* ((q5-l0 (nth *queue10-l$q5-l0* st)))
      (queue5-l$ready-in- q5-l0)))

  (defthm booleanp-queue10-l$ready-in-
    (implies (queue10-l$valid-st st data-size)
             (booleanp (queue10-l$ready-in- st)))
    :hints (("Goal" :in-theory (enable queue10-l$valid-st
                                       queue10-l$ready-in-)))
    :rule-classes (:rewrite :type-prescription))

  ;; Extract the "ready-out" signal

  (defund queue10-l$ready-out (st)
    (b* ((q5-l1 (nth *queue10-l$q5-l1* st)))
      (queue5-l$ready-out q5-l1)))

  (defthm booleanp-queue10-l$ready-out
    (implies (queue10-l$valid-st st data-size)
             (booleanp (queue10-l$ready-out st)))
    :hints (("Goal" :in-theory (enable queue10-l$valid-st
                                       queue10-l$ready-out)))
    :rule-classes (:rewrite :type-prescription))

  ;; Extract the output data

  (defund queue10-l$data-out (st)
    (b* ((q5-l1 (nth *queue10-l$q5-l1* st)))
      (queue5-l$data-out q5-l1)))

  (defthm len-queue10-l$data-out-1
    (implies (queue10-l$st-format st data-size)
             (equal (len (queue10-l$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable queue10-l$st-format
                                       queue10-l$data-out))))

  (defthm len-queue10-l$data-out-2
    (implies (queue10-l$valid-st st data-size)
             (equal (len (queue10-l$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable queue10-l$valid-st
                                       queue10-l$data-out))))

  (defthm bvp-queue10-l$data-out
    (implies (and (queue10-l$valid-st st data-size)
                  (queue10-l$ready-out st))
             (bvp (queue10-l$data-out st)))
    :hints (("Goal" :in-theory (enable queue10-l$valid-st
                                       queue10-l$ready-out
                                       queue10-l$data-out))))

  (defun queue10-l$outputs (inputs st data-size)
    (declare (ignore inputs data-size))
    (list* (queue10-l$ready-in- st)
           (queue10-l$ready-out st)
           (queue10-l$data-out st)))
  )

;; The value lemma for QUEUE10-L

(defthm queue10-l$value
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue10-l& netlist data-size)
                  (queue10-l$st-format st data-size))
             (equal (se (si 'queue10-l data-size) inputs st netlist)
                    (queue10-l$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'queue10-l data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue10-l&
                            queue10-l*$destructure
                            queue10-l$st-format
                            queue10-l$ready-in-
                            queue10-l$ready-out
                            queue10-l$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of QUEUE10-L.

(defun queue10-l$step (inputs st data-size)
  (b* ((q5-l0 (nth *queue10-l$q5-l0* st))
       (q5-l1 (nth *queue10-l$q5-l1* st))

       (q5-l0-inputs (queue10-l$q5-l0-inputs inputs st data-size))
       (q5-l1-inputs (queue10-l$q5-l1-inputs inputs st data-size)))
    (list
     ;; Q5-L0
     (queue5-l$step q5-l0-inputs q5-l0 data-size)
     ;; Q5-L1
     (queue5-l$step q5-l1-inputs q5-l1 data-size))))

(defthm queue10-l$step-v-threefix-of-data-in-canceled
  (implies
   (and (true-listp data-in)
        (equal (len data-in) data-size))
   (equal (queue10-l$step (list* in-act out-act
                                 (append (v-threefix data-in) go-signals))
                          st
                          data-size)
          (queue10-l$step (list* in-act out-act
                                 (append data-in go-signals))
                          st
                          data-size)))
  :hints (("Goal" :in-theory (enable queue10-l$step
                                     queue10-l$data-in
                                     queue10-l$q5-l0-inputs
                                     queue10-l$q5-l1-inputs
                                     queue10-l$in-act
                                     queue10-l$out-act))))

;; The state lemma for QUEUE10-L

(defthm queue10-l$state
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue10-l& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue10-l$go-num*)
                  (queue10-l$st-format st data-size))
             (equal (de (si 'queue10-l data-size) inputs st netlist)
                    (queue10-l$step inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'queue10-l data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue10-l&
                            queue10-l*$destructure
                            queue10-l$st-format
                            queue10-l$in-act
                            queue10-l$out-act
                            queue10-l$data-in
                            queue10-l$q5-l0-inputs
                            queue10-l$q5-l1-inputs)
                           (de-module-disabled-rules)))))

(in-theory (disable queue10-l$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund queue10-l$input-format (inputs st data-size)
  (b* ((in-act     (queue10-l$in-act inputs))
       (out-act    (queue10-l$out-act inputs))
       (data-in    (queue10-l$data-in inputs data-size))
       (go-signals (nthcdr (queue10-l$data-ins-len data-size) inputs))

       (ready-in- (queue10-l$ready-in- st))
       (ready-out (queue10-l$ready-out st)))
    (and
     (if ready-in-
         (not in-act)
       (booleanp in-act))
     (if (not ready-out)
         (not out-act)
       (booleanp out-act))
     (or (not in-act) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *queue10-l$go-num*)
     (equal inputs
            (list* in-act out-act (append data-in go-signals))))))

(local
 (defthm queue10-l$input-format=>q5-l0$input-format
   (implies (and (queue10-l$input-format inputs st data-size)
                 (queue10-l$valid-st st data-size))
            (queue5-l$input-format
             (queue10-l$q5-l0-inputs inputs st data-size)
             (nth *queue10-l$q5-l0* st)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (queue5-l$valid-st=>constraint
                             queue5-l$input-format
                             queue5-l$in-act
                             queue5-l$out-act
                             queue5-l$data-in
                             queue10-l$input-format
                             queue10-l$valid-st
                             queue10-l$ready-in-
                             queue10-l$q5-l0-inputs)
                            ())))))

(local
 (defthm queue10-l$input-format=>q5-l1$input-format
   (implies (and (queue10-l$input-format inputs st data-size)
                 (queue10-l$valid-st st data-size))
            (queue5-l$input-format
             (queue10-l$q5-l1-inputs inputs st data-size)
             (nth *queue10-l$q5-l1* st)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (joint-act
                             queue5-l$valid-st=>constraint
                             queue5-l$input-format
                             queue5-l$in-act
                             queue5-l$out-act
                             queue5-l$data-in
                             queue10-l$input-format
                             queue10-l$valid-st
                             queue10-l$ready-out
                             queue10-l$q5-l1-inputs)
                            ())))))

(defthm booleanp-queue10-l$in-act
  (implies (queue10-l$input-format inputs st data-size)
           (booleanp (queue10-l$in-act inputs)))
  :hints (("Goal" :in-theory (enable queue10-l$input-format
                                     queue10-l$in-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-queue10-l$out-act
  (implies (queue10-l$input-format inputs st data-size)
           (booleanp (queue10-l$out-act inputs)))
  :hints (("Goal" :in-theory (enable queue10-l$input-format
                                     queue10-l$out-act)))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma queue10-l :clink t)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for QUEUE10-L that extracts the future output
;; sequence from the current state.

(defund queue10-l$extract (st)
  (b* ((q5-l0 (nth *queue10-l$q5-l0* st))
       (q5-l1 (nth *queue10-l$q5-l1* st)))
    (append (queue5-l$extract q5-l0)
            (queue5-l$extract q5-l1))))

(defthm queue10-l$extract-not-empty
  (implies (and (queue10-l$ready-out st)
                (queue10-l$valid-st st data-size))
           (< 0 (len (queue10-l$extract st))))
  :hints (("Goal" :in-theory (e/d (queue10-l$valid-st
                                   queue10-l$extract
                                   queue10-l$ready-out)
                                  ())))
  :rule-classes :linear)

;; The extracted next-state function for QUEUE10-L.  Note that this function
;; avoids exploring the internal computation of QUEUE10-L.

(defund queue10-l$extracted-step (inputs st data-size)
  (b* ((data (queue10-l$data-in inputs data-size))
       (extracted-st (queue10-l$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue10-l$out-act inputs) t)
      (cond
       ((equal (queue10-l$in-act inputs) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue10-l$in-act inputs) t)
          (cons data extracted-st))
         (t extracted-st))))))

(local
 (defthm queue5-l$ready-out-lemma
   (implies (and (queue5-l$valid-st st data-size)
                 (equal (len (queue5-l$extract st)) 0))
            (not (queue5-l$ready-out st)))
   :hints (("Goal" :in-theory (enable queue5-l$valid-st
                                      queue5-l$extract
                                      queue5-l$ready-out)))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm queue10-l$q5-l0-data-in-rewrite
     (equal (queue5-l$data-in
             (queue10-l$q5-l0-inputs inputs st data-size)
             data-size)
            (queue10-l$data-in inputs data-size))
     :hints (("Goal"
              :in-theory (enable queue5-l$data-in
                                 queue10-l$data-in
                                 queue10-l$q5-l0-inputs)))))

  (local
   (defthm queue10-l$q5-l1-data-in-rewrite
     (b* ((q5-l0 (nth *queue10-l$q5-l0* st)))
       (implies (queue5-l$valid-st q5-l0 data-size)
                (equal (queue5-l$data-in
                        (queue10-l$q5-l1-inputs inputs st data-size)
                        data-size)
                       (queue5-l$data-out q5-l0))))
     :hints (("Goal"
              :in-theory (enable queue5-l$valid-st
                                 queue5-l$data-in
                                 queue5-l$data-out
                                 queue10-l$q5-l1-inputs)))))

  (local
   (defthm queue10-l$q5-l1-in-act-=-q5-l0-out-act
     (equal (queue5-l$in-act (queue10-l$q5-l1-inputs inputs st data-size))
            (queue5-l$out-act (queue10-l$q5-l0-inputs inputs st data-size)))
     :hints (("Goal" :in-theory (enable queue5-l$in-act
                                        queue5-l$out-act
                                        queue10-l$q5-l0-inputs
                                        queue10-l$q5-l1-inputs)))))

  (local
   (defthm queue10-l$q5-l0-in-act-rewrite
     (equal (queue5-l$in-act (queue10-l$q5-l0-inputs inputs st data-size))
            (queue10-l$in-act inputs))
     :hints (("Goal" :in-theory (enable queue5-l$in-act
                                        queue10-l$in-act
                                        queue10-l$q5-l0-inputs)))))

  (local
   (defthm queue10-l$q5-l1-out-act-rewrite
     (equal (queue5-l$out-act (queue10-l$q5-l1-inputs inputs st data-size))
            (queue10-l$out-act inputs))
     :hints (("Goal" :in-theory (enable queue5-l$out-act
                                        queue10-l$out-act
                                        queue10-l$q5-l1-inputs)))))

  (local
   (defthm queue10-l$extracted-step-correct-aux-1
     (equal (append x (cons e (queue5-l$extract st)))
            (append (append x (list e))
                    (queue5-l$extract st)))))

  (local
   (defthm queue10-l$extracted-step-correct-aux-2
     (equal (append x (cons e (take n (queue5-l$extract st))))
            (append (append x (list e))
                    (take n (queue5-l$extract st))))))

  (defthm queue10-l$extracted-step-correct
    (b* ((next-st (queue10-l$step inputs st data-size)))
      (implies (and (queue10-l$input-format inputs st data-size)
                    (queue10-l$valid-st st data-size))
               (equal (queue10-l$extract next-st)
                      (queue10-l$extracted-step inputs st data-size))))
    :hints (("Goal"
             :use queue10-l$input-format=>q5-l0$input-format
             :in-theory (e/d (queue5-l$valid-st=>constraint
                              queue5-l$extracted-step
                              queue10-l$extracted-step
                              queue10-l$input-format
                              queue10-l$valid-st
                              queue10-l$step
                              queue10-l$in-act
                              queue10-l$out-act
                              queue10-l$ready-in-
                              queue10-l$ready-out
                              queue10-l$extract)
                             (queue10-l$input-format=>q5-l0$input-format)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that queue10-l$valid-st is an invariant.

(defthm queue10-l$valid-st-preserved
  (implies (and (queue10-l$input-format inputs st data-size)
                (queue10-l$valid-st st data-size))
           (queue10-l$valid-st (queue10-l$step inputs st data-size)
                             data-size))
  :hints (("Goal"
           :in-theory (e/d (queue10-l$valid-st
                            queue10-l$step)
                           ()))))

(encapsulate
  ()

  (local
   (defthm queue10-l$q5-l1-out-act-fire
     (implies (nth 1 inputs)
              (queue5-l$out-act (queue10-l$q5-l1-inputs inputs st data-size)))
     :hints (("Goal" :in-theory (enable queue5-l$out-act
                                        queue10-l$out-act
                                        queue10-l$q5-l1-inputs)))))

  (defthm queue10-l$extract-lemma-1
    (implies (and (queue10-l$input-format inputs st data-size)
                  (queue10-l$valid-st st data-size)
                  (queue10-l$out-act inputs))
             (equal (list (queue10-l$data-out st))
                    (nthcdr (1- (len (queue10-l$extract st)))
                            (queue10-l$extract st))))
    :hints (("Goal"
             :do-not-induct t
             :use queue10-l$input-format=>q5-l1$input-format
             :in-theory (e/d (queue5-l$valid-st=>constraint
                              queue10-l$input-format
                              queue10-l$valid-st
                              queue10-l$extract
                              queue10-l$out-act
                              queue10-l$ready-out
                              queue10-l$data-out)
                             (queue10-l$input-format=>q5-l1$input-format)))))

  (defthmd queue10-l$extract-lemma-2
    (implies (and (queue10-l$valid-st st data-size)
                  (queue10-l$ready-out st))
             (equal (list (queue10-l$data-out st))
                    (nthcdr (1- (len (queue10-l$extract st)))
                            (queue10-l$extract st))))
    :hints (("Goal" :in-theory (e/d (queue5-l$extract-lemma-2
                                     queue10-l$valid-st
                                     queue10-l$ready-out
                                     queue10-l$data-out
                                     queue10-l$extract)
                                    ()))))
  )

;; Extract the accepted input sequence

(seq-gen queue10-l in in-act -1
         (queue10-l$data-in inputs data-size)
         :clink t)

;; Extract the valid output sequence

(seq-gen queue10-l out out-act -1
         (queue10-l$data-out st)
         :netlist-data (nthcdr 2 outputs)
         :clink t)

;; The multi-step input-output relationship

(in-out-stream-lemma queue10-l :clink t)

