;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "queue4-l")
(include-book "queue5-l")

(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of QUEUE9-L
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of QUEUE9-L
;;
;; Construct a DE module generator for a queue of 9 links, QUEUE9-L, using the
;; link-joint model.  Prove the value and state lemmas for this module
;; generator.  Note that QUEUE9-L is a complex link.  It is constructed by
;; concatenating QUEUE4-L and QUEUE5-L via a buffer joint.

(defconst *queue9-l$prim-go-num* 1)
(defconst *queue9-l$go-num* (+ *queue9-l$prim-go-num*
                               *queue4-l$go-num*
                               *queue5-l$go-num*))

(defun queue9-l$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (mbe :logic (nfix data-size)
            :exec  data-size)))

(defun queue9-l$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (queue9-l$data-ins-len data-size)
     *queue9-l$go-num*))

;; DE module generator of QUEUE9-L

(module-generator
 queue9-l* (data-size)
 (si 'queue9-l data-size)
 (list* 'in-act 'out-act (append (sis 'data-in 0 data-size)
                                 (sis 'go 0 *queue9-l$go-num*)))
 (list* 'ready-in- 'ready-out
        (sis 'data-out 0 data-size))
 '(q4-l q5-l)
 (list
  ;; LINKS
  ;; 4-link queue Q4-L
  (list 'q4-l
        (list* 'ready-in- 'q4-l-ready-out
               (sis 'q4-l-data-out 0 data-size))
        (si 'queue4-l data-size)
        (list* 'in-act 'trans-act
               (append (sis 'data-in 0 data-size)
                       (sis 'go
                            *queue9-l$prim-go-num*
                            *queue4-l$go-num*))))

  ;; 5-link queue Q5-L
  (list 'q5-l
        (list* 'q5-l-ready-in- 'ready-out
               (sis 'data-out 0 data-size))
        (si 'queue5-l data-size)
        (list* 'trans-act 'out-act
               (append (sis 'q5-l-data-in 0 data-size)
                       (sis 'go
                            (+ *queue9-l$prim-go-num*
                               *queue4-l$go-num*)
                            *queue5-l$go-num*))))

  ;; JOINT
  ;; Transfer data from Q4-L to Q5-L
  (list 'trans-cntl
        '(trans-act)
        'joint-cntl
        (list 'q4-l-ready-out 'q5-l-ready-in- (si 'go 0)))
  (list 'trans-op
        (sis 'q5-l-data-in 0 data-size)
        (si 'v-buf data-size)
        (sis 'q4-l-data-out 0 data-size)))

 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'queue9-l '(q4-l q5-l) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; QUEUE9-L.

(defund queue9-l$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (queue9-l* data-size)
        (union$ (queue4-l$netlist data-size)
                (queue5-l$netlist data-size)
                :test 'equal)))

;; Recognizer for QUEUE9-L

(defund queue9-l& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'queue9-l data-size) netlist)))
    (and (equal (assoc (si 'queue9-l data-size) netlist)
                (queue9-l* data-size))
         (joint-cntl& subnetlist)
         (v-buf& subnetlist data-size)
         (queue4-l& subnetlist data-size)
         (queue5-l& subnetlist data-size))))

;; Sanity check

(local
 (defthmd check-queue9-l$netlist-64
   (and (net-syntax-okp (queue9-l$netlist 64))
        (net-arity-okp (queue9-l$netlist 64))
        (queue9-l& (queue9-l$netlist 64) 64))))

;; Constraints on the state of QUEUE9-L

(defund queue9-l$st-format (st data-size)
  (b* ((q4-l (nth *queue9-l$q4-l* st))
       (q5-l (nth *queue9-l$q5-l* st)))
    (and (queue4-l$st-format q4-l data-size)
         (queue5-l$st-format q5-l data-size))))

(defthm queue9-l$st-format=>constraint
  (implies (queue9-l$st-format st data-size)
           (natp data-size))
  :hints (("Goal" :in-theory (enable queue9-l$st-format)))
  :rule-classes :forward-chaining)

(defund queue9-l$valid-st (st data-size)
  (b* ((q4-l (nth *queue9-l$q4-l* st))
       (q5-l (nth *queue9-l$q5-l* st)))
    (and (queue4-l$valid-st q4-l data-size)
         (queue5-l$valid-st q5-l data-size))))

(defthmd queue9-l$valid-st=>constraint
  (implies (queue9-l$valid-st st data-size)
           (natp data-size))
  :hints (("Goal" :in-theory (enable queue4-l$valid-st=>constraint
                                     queue9-l$valid-st)))
  :rule-classes :forward-chaining)

(defthmd queue9-l$valid-st=>st-format
  (implies (queue9-l$valid-st st data-size)
           (queue9-l$st-format st data-size))
  :hints (("Goal" :in-theory (e/d (queue4-l$valid-st=>st-format
                                   queue5-l$valid-st=>st-format
                                   queue9-l$st-format
                                   queue9-l$valid-st)
                                  ()))))

;; Extract the input and output signals for QUEUE9-L

(progn
  ;; Extract the "in-act" signal

  (defund queue9-l$in-act (inputs)
    (nth 0 inputs))

  ;; Extract the "out-act" signal

  (defund queue9-l$out-act (inputs)
    (nth 1 inputs))

  ;; Extract the input data

  (defun queue9-l$data-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (mbe :logic (nfix data-size)
               :exec  data-size)
          (nthcdr 2 inputs)))

  (defthm len-queue9-l$data-in
    (equal (len (queue9-l$data-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable queue9-l$data-in))

  ;; Extract the inputs for the Q4-L link

  (defund queue9-l$q4-l-inputs (inputs st data-size)
    (b* ((in-act (queue9-l$in-act inputs))
         (data-in (queue9-l$data-in inputs data-size))
         (go-signals (nthcdr (queue9-l$data-ins-len data-size) inputs))

         (go-trans (nth 0 go-signals))
         (q4-l-go-signals (take *queue4-l$go-num*
                                (nthcdr *queue9-l$prim-go-num*
                                        go-signals)))

         (q4-l (nth *queue9-l$q4-l* st))
         (q5-l (nth *queue9-l$q5-l* st))

         (trans-act (joint-act (queue4-l$ready-out q4-l)
                               (queue5-l$ready-in- q5-l)
                               go-trans)))

      (list* in-act trans-act
             (append data-in q4-l-go-signals))))

  ;; Extract the inputs for the Q5-L link

  (defund queue9-l$q5-l-inputs (inputs st data-size)
    (b* ((out-act (queue9-l$out-act inputs))
         (go-signals (nthcdr (queue9-l$data-ins-len data-size) inputs))

         (go-trans (nth 0 go-signals))
         (q5-l-go-signals (take *queue5-l$go-num*
                                (nthcdr (+ *queue9-l$prim-go-num*
                                           *queue4-l$go-num*)
                                        go-signals)))

         (q4-l (nth *queue9-l$q4-l* st))
         (q5-l (nth *queue9-l$q5-l* st))

         (trans-act (joint-act (queue4-l$ready-out q4-l)
                               (queue5-l$ready-in- q5-l)
                               go-trans)))

      (list* trans-act out-act
             (append (queue4-l$data-out q4-l)
                     q5-l-go-signals))))

  ;; Extract the "ready-in-" signal

  (defund queue9-l$ready-in- (st)
    (b* ((q4-l (nth *queue9-l$q4-l* st)))
      (queue4-l$ready-in- q4-l)))

  (defthm booleanp-queue9-l$ready-in-
    (implies (queue9-l$valid-st st data-size)
             (booleanp (queue9-l$ready-in- st)))
    :hints (("Goal" :in-theory (enable queue9-l$valid-st
                                       queue9-l$ready-in-)))
    :rule-classes (:rewrite :type-prescription))

  ;; Extract the "ready-out" signal

  (defund queue9-l$ready-out (st)
    (b* ((q5-l (nth *queue9-l$q5-l* st)))
      (queue5-l$ready-out q5-l)))

  (defthm booleanp-queue9-l$ready-out
    (implies (queue9-l$valid-st st data-size)
             (booleanp (queue9-l$ready-out st)))
    :hints (("Goal" :in-theory (enable queue9-l$valid-st
                                       queue9-l$ready-out)))
    :rule-classes (:rewrite :type-prescription))

  ;; Extract the output data

  (defund queue9-l$data-out (st)
    (b* ((q5-l (nth *queue9-l$q5-l* st)))
      (queue5-l$data-out q5-l)))

  (defthm len-queue9-l$data-out-1
    (implies (queue9-l$st-format st data-size)
             (equal (len (queue9-l$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable queue9-l$st-format
                                       queue9-l$data-out))))

  (defthm len-queue9-l$data-out-2
    (implies (queue9-l$valid-st st data-size)
             (equal (len (queue9-l$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable queue9-l$valid-st
                                       queue9-l$data-out))))

  (defthm bvp-queue9-l$data-out
    (implies (and (queue9-l$valid-st st data-size)
                  (queue9-l$ready-out st))
             (bvp (queue9-l$data-out st)))
    :hints (("Goal" :in-theory (enable queue9-l$valid-st
                                       queue9-l$ready-out
                                       queue9-l$data-out))))

  (defun queue9-l$outputs (inputs st data-size)
    (declare (ignore inputs data-size))
    (list* (queue9-l$ready-in- st)
           (queue9-l$ready-out st)
           (queue9-l$data-out st)))
  )

;; The value lemma for QUEUE9-L

(defthm queue9-l$value
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue9-l& netlist data-size)
                  (queue9-l$st-format st data-size))
             (equal (se (si 'queue9-l data-size) inputs st netlist)
                    (queue9-l$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'queue9-l data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue9-l&
                            queue9-l*$destructure
                            queue9-l$st-format
                            queue9-l$ready-in-
                            queue9-l$ready-out
                            queue9-l$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of QUEUE9-L.

(defun queue9-l$step (inputs st data-size)
  (b* ((q4-l (nth *queue9-l$q4-l* st))
       (q5-l (nth *queue9-l$q5-l* st))

       (q4-l-inputs (queue9-l$q4-l-inputs inputs st data-size))
       (q5-l-inputs (queue9-l$q5-l-inputs inputs st data-size)))
    (list
     ;; Q4-L
     (queue4-l$step q4-l-inputs q4-l data-size)
     ;; Q5-L
     (queue5-l$step q5-l-inputs q5-l data-size))))

(defthm queue9-l$step-v-threefix-of-data-in-canceled
  (implies
   (and (true-listp data-in)
        (equal (len data-in) data-size))
   (equal (queue9-l$step (list* in-act out-act
                                (append (v-threefix data-in) go-signals))
                         st
                         data-size)
          (queue9-l$step (list* in-act out-act
                                (append data-in go-signals))
                         st
                         data-size)))
  :hints (("Goal" :in-theory (enable queue9-l$step
                                     queue9-l$data-in
                                     queue9-l$q4-l-inputs
                                     queue9-l$q5-l-inputs
                                     queue9-l$in-act
                                     queue9-l$out-act))))

;; The state lemma for QUEUE9-L

(defthm queue9-l$state
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue9-l& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue9-l$go-num*)
                  (queue9-l$st-format st data-size))
             (equal (de (si 'queue9-l data-size) inputs st netlist)
                    (queue9-l$step inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'queue9-l data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue9-l&
                            queue9-l*$destructure
                            queue9-l$st-format
                            queue9-l$in-act
                            queue9-l$out-act
                            queue9-l$data-in
                            queue9-l$q4-l-inputs
                            queue9-l$q5-l-inputs)
                           (de-module-disabled-rules)))))

(in-theory (disable queue9-l$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund queue9-l$input-format (inputs st data-size)
  (b* ((in-act     (queue9-l$in-act inputs))
       (out-act    (queue9-l$out-act inputs))
       (data-in    (queue9-l$data-in inputs data-size))
       (go-signals (nthcdr (queue9-l$data-ins-len data-size) inputs))

       (ready-in- (queue9-l$ready-in- st))
       (ready-out (queue9-l$ready-out st)))
    (and
     (if ready-in-
         (not in-act)
       (booleanp in-act))
     (if (not ready-out)
         (not out-act)
       (booleanp out-act))
     (or (not in-act) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *queue9-l$go-num*)
     (equal inputs
            (list* in-act out-act (append data-in go-signals))))))

(local
 (defthm queue9-l$input-format=>q4-l$input-format
   (implies (and (queue9-l$input-format inputs st data-size)
                 (queue9-l$valid-st st data-size))
            (queue4-l$input-format
             (queue9-l$q4-l-inputs inputs st data-size)
             (nth *queue9-l$q4-l* st)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (queue4-l$valid-st=>constraint
                             queue4-l$input-format
                             queue4-l$in-act
                             queue4-l$out-act
                             queue4-l$data-in
                             queue9-l$input-format
                             queue9-l$valid-st
                             queue9-l$ready-in-
                             queue9-l$q4-l-inputs)
                            ())))))

(local
 (defthm queue9-l$input-format=>q5-l$input-format
   (implies (and (queue9-l$input-format inputs st data-size)
                 (queue9-l$valid-st st data-size))
            (queue5-l$input-format
             (queue9-l$q5-l-inputs inputs st data-size)
             (nth *queue9-l$q5-l* st)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (joint-act
                             queue5-l$valid-st=>constraint
                             queue5-l$input-format
                             queue5-l$in-act
                             queue5-l$out-act
                             queue5-l$data-in
                             queue9-l$input-format
                             queue9-l$valid-st
                             queue9-l$ready-out
                             queue9-l$q5-l-inputs)
                            ())))))

(defthm booleanp-queue9-l$in-act
  (implies (queue9-l$input-format inputs st data-size)
           (booleanp (queue9-l$in-act inputs)))
  :hints (("Goal" :in-theory (enable queue9-l$input-format
                                     queue9-l$in-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-queue9-l$out-act
  (implies (queue9-l$input-format inputs st data-size)
           (booleanp (queue9-l$out-act inputs)))
  :hints (("Goal" :in-theory (enable queue9-l$input-format
                                     queue9-l$out-act)))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma queue9-l :clink t)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for QUEUE9-L that extracts the future output
;; sequence from the current state.

(defund queue9-l$extract (st)
  (b* ((q4-l (nth *queue9-l$q4-l* st))
       (q5-l (nth *queue9-l$q5-l* st)))
    (append (queue4-l$extract q4-l)
            (queue5-l$extract q5-l))))

(defthm queue9-l$extract-not-empty
  (implies (and (queue9-l$ready-out st)
                (queue9-l$valid-st st data-size))
           (< 0 (len (queue9-l$extract st))))
  :hints (("Goal" :in-theory (e/d (queue9-l$valid-st
                                   queue9-l$extract
                                   queue9-l$ready-out)
                                  ())))
  :rule-classes :linear)

;; The extracted next-state function for QUEUE9-L.  Note that this function
;; avoids exploring the internal computation of QUEUE9-L.

(defund queue9-l$extracted-step (inputs st data-size)
  (b* ((data (queue9-l$data-in inputs data-size))
       (extracted-st (queue9-l$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue9-l$out-act inputs) t)
      (cond
       ((equal (queue9-l$in-act inputs) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue9-l$in-act inputs) t)
          (cons data extracted-st))
         (t extracted-st))))))

(local
 (defthm queue4-l$ready-out-lemma
   (implies (and (queue4-l$valid-st st data-size)
                 (equal (len (queue4-l$extract st)) 0))
            (not (queue4-l$ready-out st)))
   :hints (("Goal" :in-theory (enable queue4-l$valid-st
                                      queue4-l$extract
                                      queue4-l$ready-out)))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm queue9-l$q4-l-data-in-rewrite
     (equal (queue4-l$data-in
             (queue9-l$q4-l-inputs inputs st data-size)
             data-size)
            (queue9-l$data-in inputs data-size))
     :hints (("Goal"
              :in-theory (enable queue4-l$data-in
                                 queue9-l$data-in
                                 queue9-l$q4-l-inputs)))))

  (local
   (defthm queue9-l$q5-l-data-in-rewrite
     (b* ((q4-l (nth *queue9-l$q4-l* st)))
       (implies (queue4-l$valid-st q4-l data-size)
                (equal (queue5-l$data-in
                        (queue9-l$q5-l-inputs inputs st data-size)
                        data-size)
                       (queue4-l$data-out q4-l))))
     :hints (("Goal"
              :in-theory (enable queue4-l$valid-st
                                 queue4-l$data-out
                                 queue5-l$data-in
                                 queue9-l$q5-l-inputs)))))

  (local
   (defthm queue9-l$q5-l-in-act-=-q4-l-out-act
     (equal (queue5-l$in-act (queue9-l$q5-l-inputs inputs st data-size))
            (queue4-l$out-act (queue9-l$q4-l-inputs inputs st data-size)))
     :hints (("Goal" :in-theory (enable queue4-l$out-act
                                        queue5-l$in-act
                                        queue9-l$q4-l-inputs
                                        queue9-l$q5-l-inputs)))))

  (local
   (defthm queue9-l$q4-l-in-act-rewrite
     (equal (queue4-l$in-act (queue9-l$q4-l-inputs inputs st data-size))
            (queue9-l$in-act inputs))
     :hints (("Goal" :in-theory (enable queue4-l$in-act
                                        queue9-l$in-act
                                        queue9-l$q4-l-inputs)))))

  (local
   (defthm queue9-l$q5-l-out-act-rewrite
     (equal (queue5-l$out-act (queue9-l$q5-l-inputs inputs st data-size))
            (queue9-l$out-act inputs))
     :hints (("Goal" :in-theory (enable queue5-l$out-act
                                        queue9-l$out-act
                                        queue9-l$q5-l-inputs)))))

  (local
   (defthm queue9-l$extracted-step-correct-aux-1
     (equal (append x (cons e (queue5-l$extract st)))
            (append (append x (list e))
                    (queue5-l$extract st)))))

  (local
   (defthm queue9-l$extracted-step-correct-aux-2
     (equal (append x (cons e (take n (queue5-l$extract st))))
            (append (append x (list e))
                    (take n (queue5-l$extract st))))))

  (defthm queue9-l$extracted-step-correct
    (b* ((next-st (queue9-l$step inputs st data-size)))
      (implies (and (queue9-l$input-format inputs st data-size)
                    (queue9-l$valid-st st data-size))
               (equal (queue9-l$extract next-st)
                      (queue9-l$extracted-step inputs st data-size))))
    :hints (("Goal"
             :use queue9-l$input-format=>q4-l$input-format
             :in-theory (e/d (queue4-l$valid-st=>constraint
                              queue4-l$extracted-step
                              queue5-l$extracted-step
                              queue9-l$extracted-step
                              queue9-l$input-format
                              queue9-l$valid-st
                              queue9-l$step
                              queue9-l$in-act
                              queue9-l$out-act
                              queue9-l$ready-in-
                              queue9-l$ready-out
                              queue9-l$extract)
                             (queue9-l$input-format=>q4-l$input-format
                              associativity-of-append)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that queue9-l$valid-st is an invariant.

(defthm queue9-l$valid-st-preserved
  (implies (and (queue9-l$input-format inputs st data-size)
                (queue9-l$valid-st st data-size))
           (queue9-l$valid-st (queue9-l$step inputs st data-size)
                            data-size))
  :hints (("Goal"
           :in-theory (e/d (queue9-l$valid-st
                            queue9-l$step)
                           ()))))

(encapsulate
  ()

  (local
   (defthm queue9-l$q5-l-out-act-fire
     (implies (nth 1 inputs)
              (queue5-l$out-act (queue9-l$q5-l-inputs inputs st data-size)))
     :hints (("Goal" :in-theory (enable queue5-l$out-act
                                        queue9-l$out-act
                                        queue9-l$q5-l-inputs)))))

  (defthm queue9-l$extract-lemma-1
    (implies (and (queue9-l$input-format inputs st data-size)
                  (queue9-l$valid-st st data-size)
                  (queue9-l$out-act inputs))
             (equal (list (queue9-l$data-out st))
                    (nthcdr (1- (len (queue9-l$extract st)))
                            (queue9-l$extract st))))
    :hints (("Goal"
             :do-not-induct t
             :use queue9-l$input-format=>q5-l$input-format
             :in-theory (e/d (queue5-l$valid-st=>constraint
                              queue9-l$input-format
                              queue9-l$valid-st
                              queue9-l$extract
                              queue9-l$out-act
                              queue9-l$ready-out
                              queue9-l$data-out)
                             (queue9-l$input-format=>q5-l$input-format)))))

  (defthmd queue9-l$extract-lemma-2
    (implies (and (queue9-l$valid-st st data-size)
                  (queue9-l$ready-out st))
             (equal (list (queue9-l$data-out st))
                    (nthcdr (1- (len (queue9-l$extract st)))
                            (queue9-l$extract st))))
    :hints (("Goal" :in-theory (e/d (queue5-l$extract-lemma-2
                                     queue9-l$valid-st
                                     queue9-l$ready-out
                                     queue9-l$data-out
                                     queue9-l$extract)
                                    ()))))
  )

;; Extract the accepted input sequence

(seq-gen queue9-l in in-act -1
         (queue9-l$data-in inputs data-size)
         :clink t)

;; Extract the valid output sequence

(seq-gen queue9-l out out-act -1
         (queue9-l$data-out st)
         :netlist-data (nthcdr 2 outputs)
         :clink t)

;; The multi-step input-output relationship

(in-out-stream-lemma queue9-l :clink t)

