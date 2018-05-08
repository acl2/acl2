;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; April 2018

(in-package "ADE")

(include-book "queue4-as-link")

(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of Q8'
;;; 2. Specify the Final State of Q8' After An N-Step Execution
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of Q8'
;;
;; Construct a DE module generator for a queue of eight links, Q8', using the
;; link-joint model.  Prove the value and state lemmas for this module
;; generator.  Note that Q8' is a complex link.  It is constructed by
;; concatenating two instances of Q4' via a buffer joint.

(defconst *queue8$prim-go-num* 1)
(defconst *queue8$go-num* (+ *queue8$prim-go-num*
                             (* 2 *queue4$go-num*)))
(defconst *queue8$st-len* 2)

(defun queue8$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun queue8$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (queue8$data-ins-len data-width)
     *queue8$go-num*))

;; DE module generator of Q8'

(module-generator
 queue8* (data-width)
 (si 'queue8 data-width)
 (list* 'in-act 'out-act (append (sis 'data-in 0 data-width)
                                 (sis 'go 0 *queue8$go-num*)))
 (list* 'ready-in- 'ready-out
        (sis 'data-out 0 data-width))
 '(q4-0 q4-1)
 (list
  ;; LINKS
  ;; 4-link queue Q4-0
  (list 'q4-0
        (list* 'ready-in- 'q4-0-ready-out
               (sis 'q4-0-data-out 0 data-width))
        (si 'queue4 data-width)
        (list* 'in-act 'trans-act
               (append (sis 'data-in 0 data-width)
                       (sis 'go
                            *queue8$prim-go-num*
                            *queue4$go-num*))))

  ;; 4-link queue Q4-1
  (list 'q4-1
        (list* 'q4-1-ready-in- 'ready-out
               (sis 'data-out 0 data-width))
        (si 'queue4 data-width)
        (list* 'trans-act 'out-act
               (append (sis 'q4-1-data-in 0 data-width)
                       (sis 'go
                            (+ *queue8$prim-go-num*
                               *queue4$go-num*)
                            *queue4$go-num*))))

  ;; JOINT
  ;; Transfer data from Q4-0 to Q4-1
  (list 'trans-cntl
        '(trans-act)
        'joint-cntl
        (list 'q4-0-ready-out 'q4-1-ready-in- (si 'go 0)))
  (list 'trans-op
        (sis 'q4-1-data-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'q4-0-data-out 0 data-width)))

 :guard (natp data-width))

(make-event
 `(progn
    ,@(state-accessors-gen 'queue8 '(q4-0 q4-1) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of Q8'.

(defun queue8$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (queue8* data-width)
        (union$ (queue4$netlist data-width)
                :test 'equal)))

;; Recognizer for Q8'

(defund queue8& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (and (equal (assoc (si 'queue8 data-width) netlist)
              (queue8* data-width))
       (b* ((netlist (delete-to-eq (si 'queue8 data-width) netlist)))
         (and (joint-cntl& netlist)
              (v-buf& netlist data-width)
              (queue4& netlist data-width)))))

;; Sanity check

(local
 (defthmd check-queue8$netlist-64
   (and (net-syntax-okp (queue8$netlist 64))
        (net-arity-okp (queue8$netlist 64))
        (queue8& (queue8$netlist 64) 64))))

;; Constraints on the state of Q8'

(defund queue8$st-format (st data-width)
  (b* ((q4-0 (get-field *queue8$q4-0* st))
       (q4-1 (get-field *queue8$q4-1* st)))
    (and (queue4$st-format q4-0 data-width)
         (queue4$st-format q4-1 data-width))))

(defthm queue8$st-format=>natp-data-width
  (implies (queue8$st-format st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue8$st-format)))
  :rule-classes :forward-chaining)

(defund queue8$valid-st (st data-width)
  (b* ((q4-0 (get-field *queue8$q4-0* st))
       (q4-1 (get-field *queue8$q4-1* st)))
    (and (queue4$valid-st q4-0 data-width)
         (queue4$valid-st q4-1 data-width))))

(defthmd queue8$valid-st=>natp-data-width
  (implies (queue8$valid-st st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue8$valid-st
                                     queue4$valid-st=>natp-data-width)))
  :rule-classes :forward-chaining)

;; Extract the input and output signals from Q8'

(progn
  ;; Extract the "in-act" signal

  (defund queue8$in-act (inputs)
    (nth 0 inputs))

  ;; Extract the "out-act" signal

  (defund queue8$out-act (inputs)
    (nth 1 inputs))

  ;; Extract the input data

  (defun queue8$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 2 inputs)))

  (defthm len-queue8$data-in
    (equal (len (queue8$data-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable queue8$data-in))

  ;; Extract the inputs for the Q4-0 link

  (defund queue8$q4-0-inputs (inputs st data-width)
    (b* ((in-act (queue8$in-act inputs))
         (data-in (queue8$data-in inputs data-width))
         (go-signals (nthcdr (queue8$data-ins-len data-width) inputs))

         (go-trans (nth 0 go-signals))
         (q4-0-go-signals (take *queue4$go-num*
                                (nthcdr *queue8$prim-go-num*
                                        go-signals)))

         (q4-0 (get-field *queue8$q4-0* st))
         (q4-1 (get-field *queue8$q4-1* st))

         (trans-act (joint-act (queue4$ready-out q4-0)
                               (queue4$ready-in- q4-1)
                               go-trans)))

      (list* in-act trans-act
             (append data-in q4-0-go-signals))))

  ;; Extract the inputs for the Q4-1 link

  (defund queue8$q4-1-inputs (inputs st data-width)
    (b* ((out-act (queue8$out-act inputs))
         (go-signals (nthcdr (queue8$data-ins-len data-width) inputs))

         (go-trans (nth 0 go-signals))
         (q4-1-go-signals (take *queue4$go-num*
                                (nthcdr (+ *queue8$prim-go-num*
                                           *queue4$go-num*)
                                        go-signals)))

         (q4-0 (get-field *queue8$q4-0* st))
         (q4-1 (get-field *queue8$q4-1* st))

         (trans-act (joint-act (queue4$ready-out q4-0)
                               (queue4$ready-in- q4-1)
                               go-trans)))

      (list* trans-act out-act
             (append (queue4$data-out q4-0)
                     q4-1-go-signals))))

  ;; Extract the "ready-in-" signal

  (defund queue8$ready-in- (st)
    (b* ((q4-0 (get-field *queue8$q4-0* st)))
      (queue4$ready-in- q4-0)))

  (defthm booleanp-queue8$ready-in-
    (implies (queue8$valid-st st data-width)
             (booleanp (queue8$ready-in- st)))
    :hints (("Goal" :in-theory (enable queue8$valid-st
                                       queue8$ready-in-)))
    :rule-classes :type-prescription)

  ;; Extract the "ready-out" signal

  (defund queue8$ready-out (st)
    (b* ((q4-1 (get-field *queue8$q4-1* st)))
      (queue4$ready-out q4-1)))

  (defthm booleanp-queue8$ready-out
    (implies (queue8$valid-st st data-width)
             (booleanp (queue8$ready-out st)))
    :hints (("Goal" :in-theory (enable queue8$valid-st
                                       queue8$ready-out)))
    :rule-classes :type-prescription)

  ;; Extract the output data

  (defund queue8$data-out (st)
    (b* ((q4-1 (get-field *queue8$q4-1* st)))
      (queue4$data-out q4-1)))

  (defthm len-queue8$data-out-1
    (implies (queue8$st-format st data-width)
             (equal (len (queue8$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable queue8$st-format
                                       queue8$data-out))))

  (defthm len-queue8$data-out-2
    (implies (queue8$valid-st st data-width)
             (equal (len (queue8$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable queue8$valid-st
                                       queue8$data-out))))

  (defthm bvp-queue8$data-out
    (implies (and (queue8$valid-st st data-width)
                  (queue8$ready-out st))
             (bvp (queue8$data-out st)))
    :hints (("Goal" :in-theory (enable queue8$valid-st
                                       queue8$ready-out
                                       queue8$data-out))))
  )

(not-primp-lemma queue8) ;; Prove that Q8' is not a DE primitive.

;; The value lemma for Q8'

(defthmd queue8$value
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue8& netlist data-width)
                  (queue8$st-format st data-width))
             (equal (se (si 'queue8 data-width) inputs st netlist)
                    (list* (queue8$ready-in- st)
                           (queue8$ready-out st)
                           (queue8$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'queue8 data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            not-primp-queue8
                            queue4$st-format=>natp-data-width
                            queue8&
                            queue8*$destructure
                            joint-cntl$value
                            v-buf$value
                            queue4$value
                            queue8$st-format
                            queue8$ready-in-
                            queue8$ready-out
                            queue8$data-out)
                           ((queue8*)
                            de-module-disabled-rules)))))

;; This function specifies the next state of Q8'.

(defun queue8$step (inputs st data-width)
  (b* ((q4-0 (get-field *queue8$q4-0* st))
       (q4-1 (get-field *queue8$q4-1* st))

       (q4-0-inputs (queue8$q4-0-inputs inputs st data-width))
       (q4-1-inputs (queue8$q4-1-inputs inputs st data-width)))
    (list
     ;; Q4-0
     (queue4$step q4-0-inputs q4-0 data-width)
     ;; Q4-1
     (queue4$step q4-1-inputs q4-1 data-width))))

(defthm len-of-queue8$step
  (equal (len (queue8$step inputs st data-width))
         *queue8$st-len*))

;; The state lemma for Q8'

(defthmd queue8$state
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue8& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue8$go-num*)
                  (queue8$st-format st data-width))
             (equal (de (si 'queue8 data-width) inputs st netlist)
                    (queue8$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'queue8 data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            not-primp-queue8
                            queue8&
                            queue8*$destructure
                            queue8$st-format
                            queue8$in-act
                            queue8$out-act
                            queue8$data-in
                            queue8$q4-0-inputs
                            queue8$q4-1-inputs
                            joint-cntl$value
                            v-buf$value
                            queue4$value queue4$state)
                           ((queue8*)
                            de-module-disabled-rules)))))

(in-theory (disable queue8$step))

;; ======================================================================

;; 2. Specify the Final State of Q8' After An N-Step Execution

;; Q8' simulator

(progn
  (defun queue8$map-to-links (st)
    (b* ((q4-0 (get-field *queue8$q4-0* st))
         (q4-1 (get-field *queue8$q4-1* st)))
      (append (list (cons 'Q4-0 (queue4$map-to-links q4-0)))
              (list (cons 'Q4-1 (queue4$map-to-links q4-1))))))

  (defun queue8$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (queue8$map-to-links (car x))
            (queue8$map-to-links-list (cdr x)))))

  (defund queue8$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue8$ins-len data-width))
         ((mv inputs-lst state)
          (signal-vals-gen num-signals n state nil))
         ;;(- (cw "~x0~%" inputs-lst))
         (empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (q4-0 (list (list empty invalid-data)
                     (list empty invalid-data)
                     (list empty invalid-data)
                     (list empty invalid-data)))
         (q4-1 (list (list empty invalid-data)
                     (list empty invalid-data)
                     (list empty invalid-data)
                     (list empty invalid-data)))
         (st (list q4-0 q4-1)))
      (mv (pretty-list
           (remove-dup-neighbors
            (queue8$map-to-links-list
             (de-sim-list (si 'queue8 data-width)
                          inputs-lst
                          st
                          (queue8$netlist data-width))))
           0)
          state)))
  )

;; Conditions on the inputs

(defund queue8$input-format (inputs st data-width)
  (b* ((in-act     (queue8$in-act inputs))
       (out-act    (queue8$out-act inputs))
       (data-in    (queue8$data-in inputs data-width))
       (go-signals (nthcdr (queue8$data-ins-len data-width) inputs))

       (ready-in- (queue8$ready-in- st))
       (ready-out (queue8$ready-out st)))
    (and
     (if ready-in-
         (not in-act)
       (booleanp in-act))
     (if (not ready-out)
         (not out-act)
       (booleanp out-act))
     (or (not in-act) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *queue8$go-num*)
     (equal inputs
            (list* in-act out-act (append data-in go-signals))))))

(local
 (defthm queue8$input-format=>q4-0$input-format
   (implies (and (queue8$input-format inputs st data-width)
                 (queue8$valid-st st data-width))
            (queue4$input-format
             (queue8$q4-0-inputs inputs st data-width)
             (nth *queue8$q4-0* st)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             queue4$valid-st=>natp-data-width
                             queue4$input-format
                             queue4$in-act
                             queue4$out-act
                             queue4$data-in
                             queue8$input-format
                             queue8$valid-st
                             queue8$ready-in-
                             queue8$q4-0-inputs)
                            (nthcdr
                             take-of-too-many))))))

(local
 (defthm queue8$input-format=>q4-1$input-format
   (implies (and (queue8$input-format inputs st data-width)
                 (queue8$valid-st st data-width))
            (queue4$input-format
             (queue8$q4-1-inputs inputs st data-width)
             (nth *queue8$q4-1* st)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             joint-act
                             queue4$valid-st=>natp-data-width
                             queue4$input-format
                             queue4$in-act
                             queue4$out-act
                             queue4$data-in
                             queue8$input-format
                             queue8$valid-st
                             queue8$ready-out
                             queue8$q4-1-inputs)
                            (nthcdr
                             take-of-too-many))))))

(simulate-lemma queue8 :complex-link t)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for Q8' that extracts the future output sequence
;; from the current state.

(defund queue8$extract (st)
  (b* ((q4-0 (get-field *queue8$q4-0* st))
       (q4-1 (get-field *queue8$q4-1* st)))
    (append (queue4$extract q4-0)
            (queue4$extract q4-1))))

(defthm queue8$extract-not-empty
  (implies (and (queue8$ready-out st)
                (queue8$valid-st st data-width))
           (< 0 (len (queue8$extract st))))
  :hints (("Goal" :in-theory (e/d (queue8$valid-st
                                   queue8$extract
                                   queue8$ready-out)
                                  (nfix))))
  :rule-classes :linear)

(defthmd queue8$data-out-rewrite
  (implies (and (queue8$valid-st st data-width)
                (equal n (1- (len (queue8$extract st))))
                (queue8$ready-out st))
           (equal (list (queue8$data-out st))
                  (list (nth n (queue8$extract st)))))
  :hints (("Goal" :in-theory (e/d (queue4$data-out-rewrite
                                   queue8$valid-st
                                   queue8$ready-out
                                   queue8$data-out
                                   queue8$extract)
                                  ()))))

;; The extracted next-state function for Q8'.  Note that this function avoids
;; exploring the internal computation of Q8'.

(defund queue8$extracted-step (inputs st data-width)
  (b* ((data-in (queue8$data-in inputs data-width))
       (extracted-st (queue8$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue8$out-act inputs) t)
      (cond
       ((equal (queue8$in-act inputs) t)
        (cons data-in (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue8$in-act inputs) t)
          (cons data-in extracted-st))
         (t extracted-st))))))

(local
 (defthm queue4$ready-out-lemma
   (implies (and (queue4$valid-st st data-width)
                 (equal (len (queue4$extract st)) 0))
            (not (queue4$ready-out st)))
   :hints (("Goal" :in-theory (enable queue4$valid-st
                                      queue4$extract
                                      queue4$ready-out)))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm queue8$q4-0-data-in-rewrite
     (equal (queue4$data-in
             (queue8$q4-0-inputs inputs st data-width)
             data-width)
            (queue8$data-in inputs data-width))
     :hints (("Goal"
              :in-theory (enable queue4$data-in
                                 queue8$data-in
                                 queue8$q4-0-inputs)))))

  (local
   (defthm queue8$q4-1-data-in-rewrite
     (b* ((q4-0 (nth *queue8$q4-0* st)))
       (implies (queue4$valid-st q4-0 data-width)
                (equal (queue4$data-in
                        (queue8$q4-1-inputs inputs st data-width)
                        data-width)
                       (queue4$data-out q4-0))))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue4$valid-st
                                 queue4$st-format
                                 queue4$data-in
                                 queue4$data-out
                                 queue8$q4-1-inputs)))))

  (local
   (defthm queue8$q4-1-in-act-=-q4-0-out-act
     (equal (queue4$in-act (queue8$q4-1-inputs inputs st data-width))
            (queue4$out-act (queue8$q4-0-inputs inputs st data-width)))
     :hints (("Goal" :in-theory (enable queue4$in-act
                                        queue4$out-act
                                        queue8$q4-0-inputs
                                        queue8$q4-1-inputs)))))

  (local
   (defthm queue8$q4-0-in-act-rewrite
     (equal (queue4$in-act (queue8$q4-0-inputs inputs st data-width))
            (queue8$in-act inputs))
     :hints (("Goal" :in-theory (enable queue4$in-act
                                        queue8$in-act
                                        queue8$q4-0-inputs)))))

  (local
   (defthm queue8$q4-1-out-act-rewrite
     (equal (queue4$out-act (queue8$q4-1-inputs inputs st data-width))
            (queue8$out-act inputs))
     :hints (("Goal" :in-theory (enable queue4$out-act
                                        queue8$out-act
                                        queue8$q4-1-inputs)))))

  (local
   (defthm queue8$extracted-step-correct-aux-1
     (equal (append x (cons e (queue4$extract st)))
            (append (append x (list e))
                    (queue4$extract st)))))

  (local
   (defthm queue8$extracted-step-correct-aux-2
     (equal (append x (cons e (take n (queue4$extract st))))
            (append (append x (list e))
                    (take n (queue4$extract st))))))

  (defthm queue8$extracted-step-correct
    (b* ((next-st (queue8$step inputs st data-width)))
      (implies (and (queue8$input-format inputs st data-width)
                    (queue8$valid-st st data-width))
               (equal (queue8$extract next-st)
                      (queue8$extracted-step inputs st data-width))))
    :hints (("Goal"
             :use queue8$input-format=>q4-0$input-format
             :in-theory (e/d (get-field
                              queue4$valid-st=>natp-data-width
                              queue4$extracted-step
                              queue8$extracted-step
                              queue8$input-format
                              queue8$valid-st
                              queue8$step
                              queue8$in-act
                              queue8$out-act
                              queue8$ready-in-
                              queue8$ready-out
                              queue8$extract)
                             (queue8$input-format=>q4-0$input-format
                              acl2::associativity-of-append
                              nthcdr
                              len-nthcdr
                              pairlis$
                              strip-cars)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Extract the accepted input sequence

(defun queue8$in-seq (inputs-lst st data-width n)
  (declare (ignorable st)
           (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue8$in-act inputs) t)
          (append (queue8$in-seq (cdr inputs-lst)
                                 (queue8$step inputs st data-width)
                                 data-width
                                 (1- n))
                  (list (queue8$data-in inputs data-width)))
        (queue8$in-seq (cdr inputs-lst)
                       (queue8$step inputs st data-width)
                       data-width
                       (1- n))))))

;; Extract the valid output sequence

(defun queue8$out-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue8$out-act inputs) t)
          (append (queue8$out-seq (cdr inputs-lst)
                                  (queue8$step inputs st data-width)
                                  data-width
                                  (1- n))
                  (list (queue8$data-out st)))
        (queue8$out-seq (cdr inputs-lst)
                        (queue8$step inputs st data-width)
                        data-width
                        (1- n))))))

;; Input-output sequence simulator

(defund queue8$in-out-seq-sim (data-width n state)
  (declare (xargs :guard (and (natp data-width)
                              (natp n))
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals (queue8$ins-len data-width))
       ((mv inputs-lst state)
        (signal-vals-gen num-signals n state nil))
       (empty '(nil))
       (invalid-data (make-list data-width :initial-element '(x)))
       (q4-0 (list (list empty invalid-data)
                   (list empty invalid-data)
                   (list empty invalid-data)
                   (list empty invalid-data)))
       (q4-1 (list (list empty invalid-data)
                   (list empty invalid-data)
                   (list empty invalid-data)
                   (list empty invalid-data)))
       (st (list q4-0 q4-1)))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-lst
                   (queue8$in-seq inputs-lst st data-width n))))
      (list (cons 'out-seq
                  (v-to-nat-lst
                   (queue8$out-seq inputs-lst st data-width n)))))
     state)))

;; Prove that queue8$valid-st is an invariant.

(defthm queue8$valid-st-preserved
  (implies (and (queue8$input-format inputs st data-width)
                (queue8$valid-st st data-width))
           (queue8$valid-st (queue8$step inputs st data-width)
                            data-width))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue8$valid-st
                            queue8$step)
                           ()))))

(encapsulate
  ()

  (local
   (defthm queue8$extract-lemma-aux
     (implies (nth 1 inputs)
              (queue4$out-act (queue8$q4-1-inputs inputs st data-width)))
     :hints (("Goal" :in-theory (enable queue4$out-act
                                        queue8$out-act
                                        queue8$q4-1-inputs)))))

  (defthm queue8$extract-lemma
    (implies (and (queue8$input-format inputs st data-width)
                  (queue8$valid-st st data-width)
                  (equal n (1- (len (queue8$extract st))))
                  (queue8$out-act inputs))
             (equal (append
                     (take n (queue8$extract st))
                     (list (queue8$data-out st)))
                    (queue8$extract st)))
    :hints (("Goal"
             :do-not-induct t
             :use queue8$input-format=>q4-1$input-format
             :in-theory (e/d (get-field
                              queue4$valid-st=>natp-data-width
                              queue8$input-format
                              queue8$valid-st
                              queue8$extract
                              queue8$out-act
                              queue8$ready-out
                              queue8$data-out)
                             (queue8$input-format=>q4-1$input-format)))))
  )

(in-out-stream-lemma queue8 :complex-link t)

