;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2018

(in-package "ADE")

(include-book "queue3-l")
(include-book "queue8-l")

(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of QUEUE11-L
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of QUEUE11-L
;;
;; Construct a DE module generator for a queue of 11 links, QUEUE11-L, using
;; the link-joint model.  Prove the value and state lemmas for this module
;; generator.  Note that QUEUE11-L is a complex link.  It is constructed by
;; concatenating QUEUE3-L and QUEUE8-L via a buffer joint.

(defconst *queue11-l$prim-go-num* 1)
(defconst *queue11-l$go-num* (+ *queue11-l$prim-go-num*
                                *queue3-l$go-num*
                                *queue8-l$go-num*))
(defconst *queue11-l$st-len* 2)

(defun queue11-l$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun queue11-l$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (queue11-l$data-ins-len data-width)
     *queue11-l$go-num*))

;; DE module generator of QUEUE11-L

(module-generator
 queue11-l* (data-width)
 (si 'queue11-l data-width)
 (list* 'in-act 'out-act (append (sis 'data-in 0 data-width)
                                 (sis 'go 0 *queue11-l$go-num*)))
 (list* 'ready-in- 'ready-out
        (sis 'data-out 0 data-width))
 '(q3-l q8-l)
 (list
  ;; LINKS
  ;; 3-link queue Q3-L
  (list 'q3-l
        (list* 'ready-in- 'q3-l-ready-out
               (sis 'q3-l-data-out 0 data-width))
        (si 'queue3-l data-width)
        (list* 'in-act 'trans-act
               (append (sis 'data-in 0 data-width)
                       (sis 'go
                            *queue11-l$prim-go-num*
                            *queue3-l$go-num*))))

  ;; 8-link queue Q8-L
  (list 'q8-l
        (list* 'q8-l-ready-in- 'ready-out
               (sis 'data-out 0 data-width))
        (si 'queue8-l data-width)
        (list* 'trans-act 'out-act
               (append (sis 'q8-l-data-in 0 data-width)
                       (sis 'go
                            (+ *queue11-l$prim-go-num*
                               *queue3-l$go-num*)
                            *queue8-l$go-num*))))

  ;; JOINT
  ;; Transfer data from Q3-L to Q8-L
  (list 'trans-cntl
        '(trans-act)
        'joint-cntl
        (list 'q3-l-ready-out 'q8-l-ready-in- (si 'go 0)))
  (list 'trans-op
        (sis 'q8-l-data-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'q3-l-data-out 0 data-width)))

 :guard (natp data-width))

(make-event
 `(progn
    ,@(state-accessors-gen 'queue11-l '(q3-l q8-l) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; QUEUE11-L.

(defund queue11-l$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (queue11-l* data-width)
        (union$ (queue3-l$netlist data-width)
                (queue8-l$netlist data-width)
                :test 'equal)))

;; Recognizer for QUEUE11-L

(defund queue11-l& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (b* ((subnetlist (delete-to-eq (si 'queue11-l data-width) netlist)))
    (and (equal (assoc (si 'queue11-l data-width) netlist)
                (queue11-l* data-width))
         (joint-cntl& subnetlist)
         (v-buf& subnetlist data-width)
         (queue3-l& subnetlist data-width)
         (queue8-l& subnetlist data-width))))

;; Sanity check

(local
 (defthmd check-queue11-l$netlist-64
   (and (net-syntax-okp (queue11-l$netlist 64))
        (net-arity-okp (queue11-l$netlist 64))
        (queue11-l& (queue11-l$netlist 64) 64))))

;; Constraints on the state of QUEUE11-L

(defund queue11-l$st-format (st data-width)
  (b* ((q3-l (get-field *queue11-l$q3-l* st))
       (q8-l (get-field *queue11-l$q8-l* st)))
    (and (queue3-l$st-format q3-l data-width)
         (queue8-l$st-format q8-l data-width))))

(defthm queue11-l$st-format=>data-width-constraint
  (implies (queue11-l$st-format st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue11-l$st-format)))
  :rule-classes :forward-chaining)

(defund queue11-l$valid-st (st data-width)
  (b* ((q3-l (get-field *queue11-l$q3-l* st))
       (q8-l (get-field *queue11-l$q8-l* st)))
    (and (queue3-l$valid-st q3-l data-width)
         (queue8-l$valid-st q8-l data-width))))

(defthmd queue11-l$valid-st=>data-width-constraint
  (implies (queue11-l$valid-st st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue3-l$valid-st=>data-width-constraint
                                     queue11-l$valid-st)))
  :rule-classes :forward-chaining)

(defthmd queue11-l$valid-st=>st-format
  (implies (queue11-l$valid-st st data-width)
           (queue11-l$st-format st data-width))
  :hints (("Goal" :in-theory (e/d (queue3-l$valid-st=>st-format
                                   queue8-l$valid-st=>st-format
                                   queue11-l$st-format
                                   queue11-l$valid-st)
                                  ()))))

;; Extract the input and output signals for QUEUE11-L

(progn
  ;; Extract the "in-act" signal

  (defund queue11-l$in-act (inputs)
    (nth 0 inputs))

  ;; Extract the "out-act" signal

  (defund queue11-l$out-act (inputs)
    (nth 1 inputs))

  ;; Extract the input data

  (defun queue11-l$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 2 inputs)))

  (defthm len-queue11-l$data-in
    (equal (len (queue11-l$data-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable queue11-l$data-in))

  ;; Extract the inputs for the Q3-L link

  (defund queue11-l$q3-l-inputs (inputs st data-width)
    (b* ((in-act (queue11-l$in-act inputs))
         (data-in (queue11-l$data-in inputs data-width))
         (go-signals (nthcdr (queue11-l$data-ins-len data-width) inputs))

         (go-trans (nth 0 go-signals))
         (q3-l-go-signals (take *queue3-l$go-num*
                                (nthcdr *queue11-l$prim-go-num*
                                        go-signals)))

         (q3-l (get-field *queue11-l$q3-l* st))
         (q8-l (get-field *queue11-l$q8-l* st))

         (trans-act (joint-act (queue3-l$ready-out q3-l)
                               (queue8-l$ready-in- q8-l)
                               go-trans)))

      (list* in-act trans-act
             (append data-in q3-l-go-signals))))

  ;; Extract the inputs for the Q8-L link

  (defund queue11-l$q8-l-inputs (inputs st data-width)
    (b* ((out-act (queue11-l$out-act inputs))
         (go-signals (nthcdr (queue11-l$data-ins-len data-width) inputs))

         (go-trans (nth 0 go-signals))
         (q8-l-go-signals (take *queue8-l$go-num*
                                (nthcdr (+ *queue11-l$prim-go-num*
                                           *queue3-l$go-num*)
                                        go-signals)))

         (q3-l (get-field *queue11-l$q3-l* st))
         (q8-l (get-field *queue11-l$q8-l* st))

         (trans-act (joint-act (queue3-l$ready-out q3-l)
                               (queue8-l$ready-in- q8-l)
                               go-trans)))

      (list* trans-act out-act
             (append (queue3-l$data-out q3-l)
                     q8-l-go-signals))))

  ;; Extract the "ready-in-" signal

  (defund queue11-l$ready-in- (st)
    (b* ((q3-l (get-field *queue11-l$q3-l* st)))
      (queue3-l$ready-in- q3-l)))

  (defthm booleanp-queue11-l$ready-in-
    (implies (queue11-l$valid-st st data-width)
             (booleanp (queue11-l$ready-in- st)))
    :hints (("Goal" :in-theory (enable queue11-l$valid-st
                                       queue11-l$ready-in-)))
    :rule-classes (:rewrite :type-prescription))

  ;; Extract the "ready-out" signal

  (defund queue11-l$ready-out (st)
    (b* ((q8-l (get-field *queue11-l$q8-l* st)))
      (queue8-l$ready-out q8-l)))

  (defthm booleanp-queue11-l$ready-out
    (implies (queue11-l$valid-st st data-width)
             (booleanp (queue11-l$ready-out st)))
    :hints (("Goal" :in-theory (enable queue11-l$valid-st
                                       queue11-l$ready-out)))
    :rule-classes (:rewrite :type-prescription))

  ;; Extract the output data

  (defund queue11-l$data-out (st)
    (b* ((q8-l (get-field *queue11-l$q8-l* st)))
      (queue8-l$data-out q8-l)))

  (defthm len-queue11-l$data-out-1
    (implies (queue11-l$st-format st data-width)
             (equal (len (queue11-l$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable queue11-l$st-format
                                       queue11-l$data-out))))

  (defthm len-queue11-l$data-out-2
    (implies (queue11-l$valid-st st data-width)
             (equal (len (queue11-l$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable queue11-l$valid-st
                                       queue11-l$data-out))))

  (defthm bvp-queue11-l$data-out
    (implies (and (queue11-l$valid-st st data-width)
                  (queue11-l$ready-out st))
             (bvp (queue11-l$data-out st)))
    :hints (("Goal" :in-theory (enable queue11-l$valid-st
                                       queue11-l$ready-out
                                       queue11-l$data-out))))

  (defun queue11-l$outputs (inputs st data-width)
    (declare (ignore inputs data-width))
    (list* (queue11-l$ready-in- st)
           (queue11-l$ready-out st)
           (queue11-l$data-out st)))
  )

;; Prove that QUEUE11-L is not a DE primitive.

(not-primp-lemma queue11-l)

;; The value lemma for QUEUE11-L

(defthm queue11-l$value
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue11-l& netlist data-width)
                  (queue11-l$st-format st data-width))
             (equal (se (si 'queue11-l data-width) inputs st netlist)
                    (queue11-l$outputs inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'queue11-l data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue11-l&
                            queue11-l*$destructure
                            queue11-l$st-format
                            queue11-l$ready-in-
                            queue11-l$ready-out
                            queue11-l$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of QUEUE11-L.

(defun queue11-l$step (inputs st data-width)
  (b* ((q3-l (get-field *queue11-l$q3-l* st))
       (q8-l (get-field *queue11-l$q8-l* st))

       (q3-l-inputs (queue11-l$q3-l-inputs inputs st data-width))
       (q8-l-inputs (queue11-l$q8-l-inputs inputs st data-width)))
    (list
     ;; Q3-L
     (queue3-l$step q3-l-inputs q3-l data-width)
     ;; Q8-L
     (queue8-l$step q8-l-inputs q8-l data-width))))

(defthm len-of-queue11-l$step
  (equal (len (queue11-l$step inputs st data-width))
         *queue11-l$st-len*))

(defthm queue11-l$step-v-threefix-of-data-in-canceled
  (implies
   (and (true-listp data-in)
        (equal (len data-in) data-width))
   (equal (queue11-l$step (list* in-act out-act
                                 (append (v-threefix data-in) go-signals))
                          st
                          data-width)
          (queue11-l$step (list* in-act out-act
                                 (append data-in go-signals))
                          st
                          data-width)))
  :hints (("Goal" :in-theory (enable queue11-l$step
                                     queue11-l$data-in
                                     queue11-l$q3-l-inputs
                                     queue11-l$q8-l-inputs
                                     queue11-l$in-act
                                     queue11-l$out-act))))

;; The state lemma for QUEUE11-L

(defthm queue11-l$state
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue11-l& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue11-l$go-num*)
                  (queue11-l$st-format st data-width))
             (equal (de (si 'queue11-l data-width) inputs st netlist)
                    (queue11-l$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'queue11-l data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue11-l&
                            queue11-l*$destructure
                            queue11-l$st-format
                            queue11-l$in-act
                            queue11-l$out-act
                            queue11-l$data-in
                            queue11-l$q3-l-inputs
                            queue11-l$q8-l-inputs)
                           (de-module-disabled-rules)))))

(in-theory (disable queue11-l$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund queue11-l$input-format (inputs st data-width)
  (b* ((in-act     (queue11-l$in-act inputs))
       (out-act    (queue11-l$out-act inputs))
       (data-in    (queue11-l$data-in inputs data-width))
       (go-signals (nthcdr (queue11-l$data-ins-len data-width) inputs))

       (ready-in- (queue11-l$ready-in- st))
       (ready-out (queue11-l$ready-out st)))
    (and
     (if ready-in-
         (not in-act)
       (booleanp in-act))
     (if (not ready-out)
         (not out-act)
       (booleanp out-act))
     (or (not in-act) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *queue11-l$go-num*)
     (equal inputs
            (list* in-act out-act (append data-in go-signals))))))

(local
 (defthm queue11-l$input-format=>q3-l$input-format
   (implies (and (queue11-l$input-format inputs st data-width)
                 (queue11-l$valid-st st data-width))
            (queue3-l$input-format
             (queue11-l$q3-l-inputs inputs st data-width)
             (nth *queue11-l$q3-l* st)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             queue3-l$valid-st=>data-width-constraint
                             queue3-l$input-format
                             queue3-l$in-act
                             queue3-l$out-act
                             queue3-l$data-in
                             queue11-l$input-format
                             queue11-l$valid-st
                             queue11-l$ready-in-
                             queue11-l$q3-l-inputs)
                            ())))))

(local
 (defthm queue11-l$input-format=>q8-l$input-format
   (implies (and (queue11-l$input-format inputs st data-width)
                 (queue11-l$valid-st st data-width))
            (queue8-l$input-format
             (queue11-l$q8-l-inputs inputs st data-width)
             (nth *queue11-l$q8-l* st)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             joint-act
                             queue8-l$valid-st=>data-width-constraint
                             queue8-l$input-format
                             queue8-l$in-act
                             queue8-l$out-act
                             queue8-l$data-in
                             queue11-l$input-format
                             queue11-l$valid-st
                             queue11-l$ready-out
                             queue11-l$q8-l-inputs)
                            ())))))

(defthm booleanp-queue11-l$in-act
  (implies (queue11-l$input-format inputs st data-wisth)
           (booleanp (queue11-l$in-act inputs)))
  :hints (("Goal" :in-theory (enable queue11-l$input-format
                                     queue11-l$in-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-queue11-l$out-act
  (implies (queue11-l$input-format inputs st data-wisth)
           (booleanp (queue11-l$out-act inputs)))
  :hints (("Goal" :in-theory (enable queue11-l$input-format
                                     queue11-l$out-act)))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma queue11-l :clink t)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for QUEUE11-L that extracts the future output
;; sequence from the current state.

(defund queue11-l$extract (st)
  (b* ((q3-l (get-field *queue11-l$q3-l* st))
       (q8-l (get-field *queue11-l$q8-l* st)))
    (append (queue3-l$extract q3-l)
            (queue8-l$extract q8-l))))

(defthm queue11-l$extract-not-empty
  (implies (and (queue11-l$ready-out st)
                (queue11-l$valid-st st data-width))
           (< 0 (len (queue11-l$extract st))))
  :hints (("Goal" :in-theory (e/d (queue11-l$valid-st
                                   queue11-l$extract
                                   queue11-l$ready-out)
                                  ())))
  :rule-classes :linear)

;; The extracted next-state function for QUEUE11-L.  Note that this function
;; avoids exploring the internal computation of QUEUE11-L.

(defund queue11-l$extracted-step (inputs st data-width)
  (b* ((data (queue11-l$data-in inputs data-width))
       (extracted-st (queue11-l$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue11-l$out-act inputs) t)
      (cond
       ((equal (queue11-l$in-act inputs) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue11-l$in-act inputs) t)
          (cons data extracted-st))
         (t extracted-st))))))

(local
 (defthm queue3-l$ready-out-lemma
   (implies (and (queue3-l$valid-st st data-width)
                 (equal (len (queue3-l$extract st)) 0))
            (not (queue3-l$ready-out st)))
   :hints (("Goal" :in-theory (enable queue3-l$valid-st
                                      queue3-l$extract
                                      queue3-l$ready-out)))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm queue11-l$q3-l-data-in-rewrite
     (equal (queue3-l$data-in
             (queue11-l$q3-l-inputs inputs st data-width)
             data-width)
            (queue11-l$data-in inputs data-width))
     :hints (("Goal"
              :in-theory (enable queue3-l$data-in
                                 queue11-l$data-in
                                 queue11-l$q3-l-inputs)))))

  (local
   (defthm queue11-l$q8-l-data-in-rewrite
     (b* ((q3-l (nth *queue11-l$q3-l* st)))
       (implies (queue3-l$valid-st q3-l data-width)
                (equal (queue8-l$data-in
                        (queue11-l$q8-l-inputs inputs st data-width)
                        data-width)
                       (queue3-l$data-out q3-l))))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue3-l$valid-st
                                 queue3-l$data-out
                                 queue8-l$data-in
                                 queue11-l$q8-l-inputs)))))

  (local
   (defthm queue11-l$q8-l-in-act-=-q3-l-out-act
     (equal (queue8-l$in-act (queue11-l$q8-l-inputs inputs st data-width))
            (queue3-l$out-act (queue11-l$q3-l-inputs inputs st data-width)))
     :hints (("Goal" :in-theory (enable queue3-l$out-act
                                        queue8-l$in-act
                                        queue11-l$q3-l-inputs
                                        queue11-l$q8-l-inputs)))))

  (local
   (defthm queue11-l$q3-l-in-act-rewrite
     (equal (queue3-l$in-act (queue11-l$q3-l-inputs inputs st data-width))
            (queue11-l$in-act inputs))
     :hints (("Goal" :in-theory (enable queue3-l$in-act
                                        queue11-l$in-act
                                        queue11-l$q3-l-inputs)))))

  (local
   (defthm queue11-l$q8-l-out-act-rewrite
     (equal (queue8-l$out-act (queue11-l$q8-l-inputs inputs st data-width))
            (queue11-l$out-act inputs))
     :hints (("Goal" :in-theory (enable queue8-l$out-act
                                        queue11-l$out-act
                                        queue11-l$q8-l-inputs)))))

  (local
   (defthm queue11-l$extracted-step-correct-aux-1
     (equal (append x (cons e (queue8-l$extract st)))
            (append (append x (list e))
                    (queue8-l$extract st)))))

  (local
   (defthm queue11-l$extracted-step-correct-aux-2
     (equal (append x (cons e (take n (queue8-l$extract st))))
            (append (append x (list e))
                    (take n (queue8-l$extract st))))))

  (defthm queue11-l$extracted-step-correct
    (b* ((next-st (queue11-l$step inputs st data-width)))
      (implies (and (queue11-l$input-format inputs st data-width)
                    (queue11-l$valid-st st data-width))
               (equal (queue11-l$extract next-st)
                      (queue11-l$extracted-step inputs st data-width))))
    :hints (("Goal"
             :use queue11-l$input-format=>q3-l$input-format
             :in-theory (e/d (get-field
                              queue3-l$valid-st=>data-width-constraint
                              queue3-l$extracted-step
                              queue8-l$extracted-step
                              queue11-l$extracted-step
                              queue11-l$input-format
                              queue11-l$valid-st
                              queue11-l$step
                              queue11-l$in-act
                              queue11-l$out-act
                              queue11-l$ready-in-
                              queue11-l$ready-out
                              queue11-l$extract)
                             (queue11-l$input-format=>q3-l$input-format
                              acl2::associativity-of-append)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that queue11-l$valid-st is an invariant.

(defthm queue11-l$valid-st-preserved
  (implies (and (queue11-l$input-format inputs st data-width)
                (queue11-l$valid-st st data-width))
           (queue11-l$valid-st (queue11-l$step inputs st data-width)
                            data-width))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue11-l$valid-st
                            queue11-l$step)
                           ()))))

(encapsulate
  ()

  (local
   (defthm queue11-l$q8-l-out-act-fire
     (implies (nth 1 inputs)
              (queue8-l$out-act (queue11-l$q8-l-inputs inputs st data-width)))
     :hints (("Goal" :in-theory (enable queue8-l$out-act
                                        queue11-l$out-act
                                        queue11-l$q8-l-inputs)))))

  (defthm queue11-l$extract-lemma-1
    (implies (and (queue11-l$input-format inputs st data-width)
                  (queue11-l$valid-st st data-width)
                  (queue11-l$out-act inputs))
             (equal (list (queue11-l$data-out st))
                    (nthcdr (1- (len (queue11-l$extract st)))
                            (queue11-l$extract st))))
    :hints (("Goal"
             :do-not-induct t
             :use queue11-l$input-format=>q8-l$input-format
             :in-theory (e/d (get-field
                              queue8-l$valid-st=>data-width-constraint
                              queue11-l$input-format
                              queue11-l$valid-st
                              queue11-l$extract
                              queue11-l$out-act
                              queue11-l$ready-out
                              queue11-l$data-out)
                             (queue11-l$input-format=>q8-l$input-format)))))

  (defthmd queue11-l$extract-lemma-2
    (implies (and (queue11-l$valid-st st data-width)
                  (queue11-l$ready-out st))
             (equal (list (queue11-l$data-out st))
                    (nthcdr (1- (len (queue11-l$extract st)))
                            (queue11-l$extract st))))
    :hints (("Goal" :in-theory (e/d (queue8-l$extract-lemma-2
                                     queue11-l$valid-st
                                     queue11-l$ready-out
                                     queue11-l$data-out
                                     queue11-l$extract)
                                    ()))))
  )

;; Extract the accepted input sequence

(seq-gen queue11-l in in-act -1
         (queue11-l$data-in inputs data-width)
         :clink t)

;; Extract the valid output sequence

(seq-gen queue11-l out out-act -1
         (queue11-l$data-out st)
         :netlist-data (nthcdr 2 outputs)
         :clink t)

;; The multi-step input-output relationship

(in-out-stream-lemma queue11-l :clink t)

