;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "queue4")
(include-book "queue5")

(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of Q10
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of Q10
;;
;; Construct a DE module generator for a queue of four links, Q10, using the
;; link-joint model.  Prove the value and state lemmas for this module
;; generator.

(defconst *queue10$go-num* (+ *queue4$go-num*
                              *queue5$go-num*))

(defun queue10$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (mbe :logic (nfix data-size)
            :exec  data-size)))

(defun queue10$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (queue10$data-ins-len data-size)
     *queue10$go-num*))

;; DE module generator of Q10

(module-generator
 queue10* (data-size)
 (si 'queue10 data-size)
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 data-size)
                                     (sis 'go 0 *queue10$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-size))
 '(l q4 q5)
 (list
  ;; LINK
  ;; L
  (list 'l
        (list* 'l-status (sis 'd-out 0 data-size))
        (si 'link data-size)
        (list* 'q4-out-act 'q5-in-act (sis 'd-in 0 data-size)))

  ;; JOINTS
  ;; Q4
  (list 'q4
        (list* 'in-act 'q4-out-act
               (sis 'd-in 0 data-size))
        (si 'queue4 data-size)
        (list* 'full-in 'l-status (append (sis 'data-in 0 data-size)
                                          (sis 'go 0 *queue4$go-num*))))

  ;; Q5
  (list 'q5
        (list* 'q5-in-act 'out-act
               (sis 'data-out 0 data-size))
        (si 'queue5 data-size)
        (list* 'l-status 'empty-out- (append (sis 'd-out 0 data-size)
                                             (sis 'go
                                                  *queue4$go-num*
                                                  *queue5$go-num*)))))
 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'queue10 '(l q4 q5) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of Q10.

(defund queue10$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (queue10* data-size)
        (union$ (queue4$netlist data-size)
                (queue5$netlist data-size)
                :test 'equal)))

;; Recognizer for Q10

(defund queue10& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'queue10 data-size) netlist)))
    (and (equal (assoc (si 'queue10 data-size) netlist)
                (queue10* data-size))
         (link& subnetlist data-size)
         (queue4& subnetlist data-size)
         (queue5& subnetlist data-size))))

;; Sanity check

(local
 (defthmd check-queue10$netlist-64
   (and (net-syntax-okp (queue10$netlist 64))
        (net-arity-okp (queue10$netlist 64))
        (queue10& (queue10$netlist 64) 64))))

;; Constraints on the state of Q10

(defund queue10$st-format (st data-size)
  (b* ((l (nth *queue10$l* st))
       (q4 (nth *queue10$q4* st))
       (q5 (nth *queue10$q5* st)))
    (and (link$st-format l data-size)
         (queue4$st-format q4 data-size)
         (queue5$st-format q5 data-size))))

(defthm queue10$st-format=>constraint
  (implies (queue10$st-format st data-size)
           (natp data-size))
  :hints (("Goal" :in-theory (enable queue10$st-format)))
  :rule-classes :forward-chaining)

(defund queue10$valid-st (st data-size)
  (b* ((l (nth *queue10$l* st))
       (q4 (nth *queue10$q4* st))
       (q5 (nth *queue10$q5* st)))
    (and (link$valid-st l data-size)
         (queue4$valid-st q4 data-size)
         (queue5$valid-st q5 data-size))))

(defthmd queue10$valid-st=>constraint
  (implies (queue10$valid-st st data-size)
           (natp data-size))
  :hints (("Goal" :in-theory (enable queue10$valid-st)))
  :rule-classes :forward-chaining)

(defthmd queue10$valid-st=>st-format
  (implies (queue10$valid-st st data-size)
           (queue10$st-format st data-size))
  :hints (("Goal" :in-theory (e/d (queue4$valid-st=>st-format
                                   queue5$valid-st=>st-format
                                   queue10$st-format
                                   queue10$valid-st)
                                  (link$st-format)))))

;; Extract the input and output signals for Q10

(progn
  ;; Extract the input data

  (defun queue10$data-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (mbe :logic (nfix data-size)
               :exec  data-size)
          (nthcdr 2 inputs)))

  (defthm len-queue10$data-in
    (equal (len (queue10$data-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable queue10$data-in))

  ;; Extract the inputs for joint Q4

  (defund queue10$q4-inputs (inputs st data-size)
    (b* ((full-in (nth 0 inputs))
         (data-in (queue10$data-in inputs data-size))
         (go-signals (nthcdr (queue10$data-ins-len data-size) inputs))

         (q4-go-signals (take *queue4$go-num* go-signals))

         (l (nth *queue10$l* st))
         (l.s (nth *link$s* l)))

      (list* full-in (f-buf (car l.s))
             (append data-in q4-go-signals))))

  ;; Extract the inputs for joint Q5

  (defund queue10$q5-inputs (inputs st data-size)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (queue10$data-ins-len data-size) inputs))

         (q5-go-signals (take *queue5$go-num*
                              (nthcdr *queue4$go-num* go-signals)))

         (l (nth *queue10$l* st))
         (l.s (nth *link$s* l))
         (l.d (nth *link$d* l)))

      (list* (f-buf (car l.s)) empty-out-
             (append (v-threefix (strip-cars l.d)) q5-go-signals))))

  ;; Extract the "in-act" signal

  (defund queue10$in-act (inputs st data-size)
    (b* ((q4-inputs (queue10$q4-inputs inputs st data-size))
         (q4 (nth *queue10$q4* st)))
      (queue4$in-act q4-inputs q4 data-size)))

  (defthm queue10$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (queue10$in-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable queue10$q4-inputs
                                       queue10$in-act))))

  ;; Extract the "out-act" signal

  (defund queue10$out-act (inputs st data-size)
    (b* ((q5-inputs (queue10$q5-inputs inputs st data-size))
         (q5 (nth *queue10$q5* st)))
      (queue5$out-act q5-inputs q5 data-size)))

  (defthm queue10$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (queue10$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable queue10$q5-inputs
                                       queue10$out-act))))

  ;; Extract the output data

  (defund queue10$data-out (st)
    (b* ((q5 (nth *queue10$q5* st)))
      (queue5$data-out q5)))

  (defthm len-queue10$data-out-1
    (implies (queue10$st-format st data-size)
             (equal (len (queue10$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable queue10$st-format
                                       queue10$data-out))))

  (defthm len-queue10$data-out-2
    (implies (queue10$valid-st st data-size)
             (equal (len (queue10$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable queue10$valid-st
                                       queue10$data-out))))

  (defthm bvp-queue10$data-out
    (implies (and (queue10$valid-st st data-size)
                  (queue10$out-act inputs st data-size))
             (bvp (queue10$data-out st)))
    :hints (("Goal" :in-theory (enable queue10$valid-st
                                       queue10$out-act
                                       queue10$data-out))))

  (defun queue10$outputs (inputs st data-size)
    (list* (queue10$in-act inputs st data-size)
           (queue10$out-act inputs st data-size)
           (queue10$data-out st)))
  )

;; The value lemma for Q10

(defthm queue10$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (queue10& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue10$go-num*)
                  (queue10$st-format st data-size))
             (equal (se (si 'queue10 data-size) inputs st netlist)
                    (queue10$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'queue10 data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue10&
                            queue10*$destructure
                            queue10$st-format
                            queue10$data-in
                            queue10$q4-inputs
                            queue10$q5-inputs
                            queue10$in-act
                            queue10$out-act
                            queue10$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of Q10.

(defun queue10$step (inputs st data-size)
  (b* ((l (nth *queue10$l* st))
       (q4 (nth *queue10$q4* st))
       (q5 (nth *queue10$q5* st))

       (q4-inputs (queue10$q4-inputs inputs st data-size))
       (q5-inputs (queue10$q5-inputs inputs st data-size))

       (q4-out-act (queue4$out-act q4-inputs q4 data-size))
       (q5-in-act (queue5$in-act q5-inputs q5 data-size))
       (d-in (queue4$data-out q4))

       (l-inputs (list* q4-out-act q5-in-act d-in)))
    (list
     ;; L
     (link$step l-inputs l data-size)
     ;; Joint Q4
     (queue4$step q4-inputs q4 data-size)
     ;; Joint Q5
     (queue5$step q5-inputs q5 data-size))))

;; The state lemma for Q10

(defthm queue10$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (queue10& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue10$go-num*)
                  (queue10$st-format st data-size))
             (equal (de (si 'queue10 data-size) inputs st netlist)
                    (queue10$step inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'queue10 data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            queue10&
                            queue10*$destructure
                            queue10$st-format
                            queue10$data-in
                            queue10$q4-inputs
                            queue10$q5-inputs
                            queue10$in-act
                            queue10$out-act)
                           (de-module-disabled-rules)))))

(in-theory (disable queue10$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund queue10$input-format (inputs data-size)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-size))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (queue10$data-in inputs data-size))
       (go-signals (nthcdr (queue10$data-ins-len data-size) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *queue10$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(local
 (defthm queue10$input-format=>q4$input-format
   (implies (and (queue10$input-format inputs data-size)
                 (queue10$valid-st st data-size))
            (queue4$input-format
             (queue10$q4-inputs inputs st data-size)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (queue4$input-format
                             queue4$data-in
                             queue10$input-format
                             queue10$valid-st
                             queue10$q4-inputs)
                            ())))))

(local
 (defthm queue10$input-format=>q5$input-format
   (implies (and (queue10$input-format inputs data-size)
                 (queue10$valid-st st data-size))
            (queue5$input-format
             (queue10$q5-inputs inputs st data-size)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (queue5$input-format
                             queue5$data-in
                             queue10$input-format
                             queue10$valid-st
                             queue10$q5-inputs)
                            ())))))

(defthm booleanp-queue10$in-act
  (implies (and (queue10$input-format inputs data-size)
                (queue10$valid-st st data-size))
           (booleanp (queue10$in-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (enable queue10$valid-st
                              queue10$in-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-queue10$out-act
  (implies (and (queue10$input-format inputs data-size)
                (queue10$valid-st st data-size))
           (booleanp (queue10$out-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (enable queue10$valid-st
                              queue10$out-act)))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma queue10)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for Q10 that extracts the future output sequence from
;; the current state.

(defund queue10$extract (st)
  (b* ((l (nth *queue10$l* st))
       (q4 (nth *queue10$q4* st))
       (q5 (nth *queue10$q5* st)))
    (append (queue4$extract q4)
            (extract-valid-data (list l))
            (queue5$extract q5))))

(defthm queue10$extract-not-empty
  (implies (and (queue10$out-act inputs st data-size)
                (queue10$valid-st st data-size))
           (< 0 (len (queue10$extract st))))
  :hints (("Goal"
           :in-theory (e/d (queue10$valid-st
                            queue10$extract
                            queue10$out-act)
                           ())))
  :rule-classes :linear)

;; The extracted next-state function for Q10.  Note that this function avoids
;; exploring the internal computation of Q10.

(defund queue10$extracted-step (inputs st data-size)
  (b* ((data (queue10$data-in inputs data-size))
       (extracted-st (queue10$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue10$out-act inputs st data-size) t)
      (cond
       ((equal (queue10$in-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue10$in-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(progn
  (local
   (defthm queue10$q4-out-act-inactive
     (implies (equal (nth *link$s* (nth *queue10$l* st))
                     '(t))
              (not (queue4$out-act (queue10$q4-inputs inputs st data-size)
                                   (nth *queue10$q4* st)
                                   data-size)))
     :hints (("Goal" :in-theory (enable queue10$q4-inputs)))))

  (local
   (defthm queue10$q5-in-act-inactive
     (implies (equal (nth *link$s* (nth *queue10$l* st))
                     '(nil))
              (not (queue5$in-act (queue10$q5-inputs inputs st data-size)
                                  (nth *queue10$q5* st)
                                  data-size)))
     :hints (("Goal" :in-theory (enable queue10$q5-inputs)))))

  (local
   (defthm queue10$q4-data-in-rewrite
     (equal (queue4$data-in
             (queue10$q4-inputs inputs st data-size)
             data-size)
            (queue10$data-in inputs data-size))
     :hints (("Goal"
              :in-theory (enable queue4$data-in
                                 queue10$q4-inputs)))))

  (local
   (defthm queue10$q5-data-in-rewrite
     (b* ((l (nth *queue10$l* st))
          (l.d (nth *link$d* l)))
       (implies (equal (len l.d) data-size)
                (equal (queue5$data-in
                        (queue10$q5-inputs inputs st data-size)
                        data-size)
                       (v-threefix (strip-cars l.d)))))
     :hints (("Goal"
              :in-theory (enable queue5$data-in
                                 queue10$q5-inputs)))))

  (defthm queue10$extracted-step-correct
    (b* ((next-st (queue10$step inputs st data-size)))
      (implies (and (queue10$input-format inputs data-size)
                    (queue10$valid-st st data-size))
               (equal (queue10$extract next-st)
                      (queue10$extracted-step inputs st data-size))))
    :hints (("Goal"
             :use (queue10$input-format=>q4$input-format
                   queue10$input-format=>q5$input-format)
             :in-theory (e/d (f-sr
                              left-associativity-of-append
                              queue4$extracted-step
                              queue5$extracted-step
                              queue10$extracted-step
                              queue10$valid-st
                              queue10$step
                              queue10$in-act
                              queue10$out-act
                              queue10$extract)
                             (queue10$input-format=>q4$input-format
                              queue10$input-format=>q5$input-format
                              associativity-of-append)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that queue10$valid-st is an invariant.

(defthm queue10$valid-st-preserved
  (implies (and (queue10$input-format inputs data-size)
                (queue10$valid-st st data-size))
           (queue10$valid-st (queue10$step inputs st data-size)
                            data-size))
  :hints (("Goal"
           :use (queue10$input-format=>q4$input-format
                 queue10$input-format=>q5$input-format)
           :in-theory (e/d (f-sr
                            queue10$valid-st
                            queue10$step)
                           (queue10$input-format=>q4$input-format
                            queue10$input-format=>q5$input-format)))))

(defthm queue10$extract-lemma
  (implies (and (queue10$valid-st st data-size)
                (queue10$out-act inputs st data-size))
           (equal (list (queue10$data-out st))
                  (nthcdr (1- (len (queue10$extract st)))
                          (queue10$extract st))))
  :hints (("Goal"
           :in-theory (enable queue10$valid-st
                              queue10$extract
                              queue10$out-act
                              queue10$data-out))))

;; Extract the accepted input sequence

(seq-gen queue10 in in-act 0
         (queue10$data-in inputs data-size))

;; Extract the valid output sequence

(seq-gen queue10 out out-act 1
         (queue10$data-out st)
         :netlist-data (nthcdr 2 outputs))

;; The multi-step input-output relationship

(in-out-stream-lemma queue10)

