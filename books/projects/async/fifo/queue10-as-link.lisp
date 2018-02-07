;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; February 2018

(in-package "ADE")

(include-book "queue5-as-link")

(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of Q10'
;;; 2. Specifying the Final State of Q10' After An N-Step Execution
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of Q10'
;;
;; Constructing a DE module generator for a queue of ten links, Q10', using
;; the link-joint model. Proving the value and state lemmas for this module
;; generator. Note that Q10' is a complex link. It is constructed by
;; concatenating two instances of Q5' via a buffer joint.

(defconst *queue10$prim-go-num* 1)
(defconst *queue10$go-num* (+ *queue10$prim-go-num*
                              (* 2 *queue5$go-num*)))
(defconst *queue10$st-len* 2)

(defun queue10$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun queue10$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (queue10$data-ins-len data-width)
     *queue10$go-num*))

;; DE module generator of Q10'. It reports the "ready-in-" signal at its input
;; port, and the "ready-out" signal and output data at its output port.

(module-generator
 queue10* (data-width)
 (si 'queue10 data-width)
 (list* 'in-act 'out-act (append (sis 'data-in 0 data-width)
                                 (sis 'go 0 *queue10$go-num*)))
 (list* 'ready-in- 'ready-out
        (sis 'data-out 0 data-width))
 '(q5-0 q5-1)
 (list
  ;; LINKS
  ;; 5-link queue Q5-0
  (list 'q5-0
        (list* 'ready-in- 'q5-0-ready-out
               (sis 'q5-0-data-out 0 data-width))
        (si 'queue5 data-width)
        (list* 'in-act 'trans-act
               (append (sis 'data-in 0 data-width)
                       (sis 'go
                            *queue10$prim-go-num*
                            *queue5$go-num*))))

  ;; 5-link queue Q5-1
  (list 'q5-1
        (list* 'q5-1-ready-in- 'ready-out
               (sis 'data-out 0 data-width))
        (si 'queue5 data-width)
        (list* 'trans-act 'out-act
               (append (sis 'q5-1-$data-in 0 data-width)
                       (sis 'go
                            (+ *queue10$prim-go-num*
                               *queue5$go-num*)
                            *queue5$go-num*))))

  ;; JOINT
  ;; Transfer data from Q5-0 to Q5-1
  (list 'trans-cntl
        '(trans-act)
        'joint-cntl
        (list 'q5-0-ready-out 'q5-1-ready-in- (si 'go 0)))
  (list 'trans-op
        (sis 'q5-1-$data-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'q5-0-data-out 0 data-width)))

 :guard (natp data-width))

;; DE netlist generator. A generated netlist will contain an instance of Q10'.

(defun queue10$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (queue10* data-width)
        (union$ (queue5$netlist data-width)
                :test 'equal)))

;; Sanity syntactic check

(defthmd queue10$netlist-64-okp
  (and (net-syntax-okp (queue10$netlist 64))
       (net-arity-okp (queue10$netlist 64))))

;; Recognizer for Q10'

(defund queue10& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (and (equal (assoc (si 'queue10 data-width) netlist)
              (queue10* data-width))
       (b* ((netlist (delete-to-eq (si 'queue10 data-width) netlist)))
         (and (joint-cntl& netlist)
              (v-buf& netlist data-width)
              (queue5& netlist data-width)))))

;; Sanity check

(defthm check-queue10$netlist-64
  (queue10& (queue10$netlist 64) 64))

(defconst *queue10$q5-0* 0)
(defconst *queue10$q5-1* 1)

;; Constraints on the state of Q10'

(defund queue10$valid-st (st data-width)
  (b* ((q5-0 (get-field *queue10$q5-0* st))
       (q5-1 (get-field *queue10$q5-1* st)))
    (and (queue5$valid-st q5-0 data-width)
         (queue5$valid-st q5-1 data-width))))

(defthmd queue10$valid-st=>natp-data-width
  (implies (queue10$valid-st st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue10$valid-st
                                     queue5$valid-st=>natp-data-width)))
  :rule-classes :forward-chaining)

;; Q10' simulator

(progn
  (defun queue10$map-to-links (st)
    (b* ((q5-0 (get-field *queue10$q5-0* st))
         (q5-1 (get-field *queue10$q5-1* st)))
      (append (list (cons 'Q5-0 (queue5$map-to-links q5-0)))
              (list (cons 'Q5-1 (queue5$map-to-links q5-1))))))

  (defun queue10$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (queue10$map-to-links (car x))
            (queue10$map-to-links-list (cdr x)))))

  (defund queue10$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue10$ins-len data-width))
         ((mv inputs-lst state)
          (signal-vals-gen num-signals n state nil))
         ;;(- (cw "~x0~%" inputs-lst))
         (empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (q5-0 (list empty invalid-data
                     empty invalid-data
                     empty invalid-data
                     empty invalid-data
                     empty invalid-data))
         (q5-1 (list empty invalid-data
                     empty invalid-data
                     empty invalid-data
                     empty invalid-data
                     empty invalid-data))
         (st (list q5-0 q5-1)))
      (mv (pretty-list
           (remove-dup-neighbors
            (queue10$map-to-links-list
             (de-sim-list (si 'queue10 data-width)
                          inputs-lst
                          st
                          (queue10$netlist data-width))))
           0)
          state)))
  )

;; Extracting the "in-act" signal. It is an input signal for a complex link.

(defund queue10$in-act (inputs)
  (nth 0 inputs))

;; Extracting the "out-act" signal. It is an input signal for a complex link.

(defund queue10$out-act (inputs)
  (nth 1 inputs))

;; Extracting the input data

(defun queue10$data-in (inputs data-width)
  (declare (xargs :guard (true-listp inputs)))
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (take (mbe :logic (nfix data-width)
             :exec  data-width)
        (nthcdr 2 inputs)))

(defthm len-queue10$data-in
  (equal (len (queue10$data-in inputs data-width))
         (nfix data-width)))

(in-theory (disable queue10$data-in))

;; Extracting the inputs for the Q5-0 link

(defund queue10$q5-0-inputs (inputs st data-width)
  (b* ((in-act (queue10$in-act inputs))
       (data-in (queue10$data-in inputs data-width))
       (go-signals (nthcdr (queue10$data-ins-len data-width) inputs))

       (go-trans (nth 0 go-signals))
       (q5-0-go-signals (take *queue5$go-num*
                              (nthcdr *queue10$prim-go-num* go-signals)))

       (q5-0 (get-field *queue10$q5-0* st))
       (q5-1 (get-field *queue10$q5-1* st))

       (trans-act (joint-act (queue5$ready-out q5-0)
                             (queue5$ready-in- q5-1)
                             go-trans)))

    (list* in-act trans-act
           (append data-in q5-0-go-signals))))

;; Extracting the inputs for the Q5-1 link

(defund queue10$q5-1-inputs (inputs st data-width)
  (b* ((out-act (queue10$out-act inputs))
       (go-signals (nthcdr (queue10$data-ins-len data-width) inputs))

       (go-trans (nth 0 go-signals))
       (q5-1-go-signals (take *queue5$go-num*
                              (nthcdr (+ *queue10$prim-go-num*
                                         *queue5$go-num*)
                                      go-signals)))

       (q5-0 (get-field *queue10$q5-0* st))
       (q5-1 (get-field *queue10$q5-1* st))

       (trans-act (joint-act (queue5$ready-out q5-0)
                             (queue5$ready-in- q5-1)
                             go-trans)))

    (list* trans-act out-act
           (append (queue5$data-out q5-0)
                   q5-1-go-signals))))

;; Extracting the "ready-in-" signal

(defund queue10$ready-in- (st)
  (b* ((q5-0 (get-field *queue10$q5-0* st)))
    (queue5$ready-in- q5-0)))

(defthm booleanp-queue10$ready-in-
  (implies (queue10$valid-st st data-width)
           (booleanp (queue10$ready-in- st)))
  :hints (("Goal" :in-theory (enable queue10$valid-st
                                     queue10$ready-in-)))
  :rule-classes :type-prescription)

;; Extracting the "ready-out" signal

(defund queue10$ready-out (st)
  (b* ((q5-1 (get-field *queue10$q5-1* st)))
    (queue5$ready-out q5-1)))

(defthm booleanp-queue10$ready-out
  (implies (queue10$valid-st st data-width)
           (booleanp (queue10$ready-out st)))
  :hints (("Goal" :in-theory (enable queue10$valid-st
                                     queue10$ready-out)))
  :rule-classes :type-prescription)

;; Extracting the output data

(defund queue10$data-out (st)
  (b* ((q5-1 (get-field *queue10$q5-1* st)))
    (queue5$data-out q5-1)))

(defthm len-queue10$data-out
  (implies (queue10$valid-st st data-width)
           (equal (len (queue10$data-out st))
                  data-width))
  :hints (("Goal" :in-theory (enable queue10$valid-st
                                     queue10$data-out
                                     queue5$valid-st=>natp-data-width))))

(defthm bvp-queue10$data-out
  (implies (and (queue10$valid-st st data-width)
                (queue10$ready-out st))
           (bvp (queue10$data-out st)))
  :hints (("Goal" :in-theory (enable queue10$valid-st
                                     queue10$ready-out
                                     queue10$data-out))))

(not-primp-lemma queue10)

;; The value lemma for Q10'

(defthmd queue10$value
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue10& netlist data-width)
                  (queue10$valid-st st data-width))
             (equal (se (si 'queue10 data-width) inputs st netlist)
                    (list* (queue10$ready-in- st)
                           (queue10$ready-out st)
                           (queue10$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :expand (se (si 'queue10 data-width)
                       (list* in-act out-act (append data-in go-signals))
                       st
                       netlist)
           :in-theory (e/d (de-rules
                            get-field
                            len-1-true-listp=>true-listp
                            not-primp-queue10
                            queue5$valid-st=>natp-data-width
                            queue10&
                            queue10*$destructure
                            joint-cntl$value
                            v-buf$value
                            queue5$value
                            queue10$valid-st
                            queue10$ready-in-
                            queue10$ready-out
                            queue10$data-out)
                           ((queue10*)
                            validp
                            fullp
                            emptyp
                            de-module-disabled-rules)))))

;; This function specifies the next state of Q10'.

(defun queue10$state-fn (inputs st data-width)
  (b* ((q5-0 (get-field *queue10$q5-0* st))
       (q5-1 (get-field *queue10$q5-1* st))

       (q5-0-inputs (queue10$q5-0-inputs inputs st data-width))
       (q5-1-inputs (queue10$q5-1-inputs inputs st data-width)))
    (list
     (queue5$state-fn q5-0-inputs q5-0 data-width)
     (queue5$state-fn q5-1-inputs q5-1 data-width))))

(defthm len-of-queue10$state-fn
  (equal (len (queue10$state-fn inputs st data-width))
         *queue10$st-len*))

(local
 (defthm v-threefix-of-queue5$data-out
   (equal (v-threefix (queue5$data-out st))
          (queue5$data-out st))
   :hints (("Goal" :in-theory (enable queue5$data-out)))))

;; The state lemma for Q10'

(defthmd queue10$state
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue10& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue10$go-num*)
                  (queue10$valid-st st data-width))
             (equal (de (si 'queue10 data-width) inputs st netlist)
                    (queue10$state-fn inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :expand (de (si 'queue10 data-width)
                       (list* in-act out-act (append data-in go-signals))
                       st
                       netlist)
           :in-theory (e/d (de-rules
                            get-field
                            len-1-true-listp=>true-listp
                            not-primp-queue10
                            queue10&
                            queue10*$destructure
                            queue10$valid-st
                            queue10$in-act
                            queue10$out-act
                            queue10$data-in
                            queue10$q5-0-inputs
                            queue10$q5-1-inputs
                            joint-cntl$value
                            v-buf$value
                            queue5$value queue5$state)
                           ((queue10*)
                            validp
                            fullp
                            emptyp
                            de-module-disabled-rules)))))

(in-theory (disable queue10$state-fn))

;; ======================================================================

;; 2. Specifying the Final State of Q10' After An N-Step Execution

;; Conditions on the inputs

(defund queue10$input-format (inputs st data-width)
  (b* ((in-act     (queue10$in-act inputs))
       (out-act    (queue10$out-act inputs))
       (data-in    (queue10$data-in inputs data-width))
       (go-signals (nthcdr (queue10$data-ins-len data-width) inputs))

       (ready-in- (queue10$ready-in- st))
       (ready-out (queue10$ready-out st)))
    (and
     (if ready-in-
         (not in-act)
       (booleanp in-act))
     (if (not ready-out)
         (not out-act)
       (booleanp out-act))
     (or (not in-act) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *queue10$go-num*)
     (equal inputs
            (list* in-act out-act (append data-in go-signals))))))

;; Proving that queue10$valid-st is an invariant.

(progn
  (local
   (defthm queue10$input-format=>q5-0$input-format
     (implies (and (queue10$input-format inputs st data-width)
                   (queue10$valid-st st data-width))
              (queue5$input-format
               (queue10$q5-0-inputs inputs st data-width)
               (nth *queue10$q5-0* st)
               data-width))
     :hints (("Goal"
              :in-theory (e/d (get-field
                               queue5$valid-st=>natp-data-width
                               queue5$input-format
                               queue5$in-act
                               queue5$out-act
                               queue5$data-in
                               queue10$input-format
                               queue10$valid-st
                               queue10$ready-in-
                               queue10$q5-0-inputs)
                              (nthcdr
                               take-of-too-many))))))

  (local
   (defthm queue10$input-format=>q5-1$input-format
     (implies (and (queue10$input-format inputs st data-width)
                   (queue10$valid-st st data-width))
              (queue5$input-format
               (queue10$q5-1-inputs inputs st data-width)
               (nth *queue10$q5-1* st)
               data-width))
     :hints (("Goal"
              :in-theory (e/d (get-field
                               joint-act
                               queue5$valid-st=>natp-data-width
                               queue5$input-format
                               queue5$in-act
                               queue5$out-act
                               queue5$data-in
                               queue10$input-format
                               queue10$valid-st
                               queue10$ready-out
                               queue10$q5-1-inputs)
                              (nthcdr
                               take-of-too-many))))))

  (defthm queue10$valid-st-preserved
    (implies (and (queue10$input-format inputs st data-width)
                  (queue10$valid-st st data-width))
             (queue10$valid-st (queue10$state-fn inputs st data-width)
                               data-width))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              queue10$valid-st
                              queue10$state-fn)
                             ()))))
  )

(defthmd queue10$state-alt
  (implies (and (queue10& netlist data-width)
                (queue10$input-format inputs st data-width)
                (queue10$valid-st st data-width))
           (equal (de (si 'queue10 data-width) inputs st netlist)
                  (queue10$state-fn inputs st data-width)))
  :hints (("Goal"
           :in-theory (enable queue10$valid-st=>natp-data-width
                              queue10$input-format)
           :use (:instance
                 queue10$state
                 (in-act     (queue10$in-act inputs))
                 (out-act    (queue10$out-act inputs))
                 (data-in    (queue10$data-in inputs data-width))
                 (go-signals (nthcdr (queue10$data-ins-len data-width)
                                     inputs))))))

(state-fn-n-gen queue10 data-width)
(input-format-n-with-state-gen queue10 data-width)

(defthmd de-sim-n$queue10
  (implies (and (queue10& netlist data-width)
                (queue10$input-format-n inputs-lst st data-width n)
                (queue10$valid-st st data-width))
           (equal (de-sim-n (si 'queue10 data-width)
                            inputs-lst st netlist
                            n)
                  (queue10$state-fn-n inputs-lst st data-width n)))
  :hints (("Goal" :in-theory (enable queue10$state-alt))))

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for Q10' that extracts the future output sequence
;; from the current state.

(defund queue10$extract-state (st)
  (b* ((q5-0 (get-field *queue10$q5-0* st))
       (q5-1 (get-field *queue10$q5-1* st)))
    (append (queue5$extract-state q5-0)
            (queue5$extract-state q5-1))))

(defthm queue10$extract-state-not-empty
  (implies (and (queue10$ready-out st)
                (queue10$valid-st st data-width))
           (< 0 (len (queue10$extract-state st))))
  :hints (("Goal" :in-theory (e/d (queue10$valid-st
                                   queue10$extract-state
                                   queue10$ready-out)
                                  (nfix))))
  :rule-classes :linear)

(defthmd queue10$data-out-rewrite
  (implies (and (queue10$valid-st st data-width)
                (equal n (1- (len (queue10$extract-state st))))
                (queue10$ready-out st))
           (equal (list (queue10$data-out st))
                  (list (nth n (queue10$extract-state st)))))
  :hints (("Goal" :in-theory (e/d (queue5$data-out-rewrite
                                   queue10$valid-st
                                   queue10$ready-out
                                   queue10$data-out
                                   queue10$extract-state)
                                  ()))))

;; Extracting the accepted input sequence

(defun queue10$in-seq (inputs-lst st data-width n)
  (declare (ignorable st)
           (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue10$in-act inputs) t)
          (append (queue10$in-seq (cdr inputs-lst)
                                  (queue10$state-fn inputs st data-width)
                                  data-width
                                  (1- n))
                  (list (queue10$data-in inputs data-width)))
        (queue10$in-seq (cdr inputs-lst)
                        (queue10$state-fn inputs st data-width)
                        data-width
                        (1- n))))))

;; Extracting the valid output sequence

(defun queue10$out-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue10$out-act inputs) t)
          (append (queue10$out-seq (cdr inputs-lst)
                                   (queue10$state-fn inputs st data-width)
                                   data-width
                                   (1- n))
                  (list (queue10$data-out st)))
        (queue10$out-seq (cdr inputs-lst)
                         (queue10$state-fn inputs st data-width)
                         data-width
                         (1- n))))))

;; Input-output sequence simulator

(defund queue10$in-out-seq-sim (data-width n state)
  (declare (xargs :guard (and (natp data-width)
                              (natp n))
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals (queue10$ins-len data-width))
       ((mv inputs-lst state)
        (signal-vals-gen num-signals n state nil))
       (empty '(nil))
       (invalid-data (make-list data-width :initial-element '(x)))
       (q5-0 (list empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data))
       (q5-1 (list empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data))
       (st (list q5-0 q5-1)))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-lst
                   (queue10$in-seq inputs-lst st data-width n))))
      (list (cons 'out-seq
                  (v-to-nat-lst
                   (queue10$out-seq inputs-lst st data-width n)))))
     state)))

;; The extracted next-state function for Q10'

(defund queue10$step-spec (inputs st data-width)
  (b* ((data-in (queue10$data-in inputs data-width))
       (extracted-st (queue10$extract-state st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue10$out-act inputs) t)
      (cond
       ((equal (queue10$in-act inputs) t)
        (cons data-in (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue10$in-act inputs) t)
          (cons data-in extracted-st))
         (t extracted-st))))))

(local
 (defthm queue5$ready-out-lemma
   (implies (and (queue5$valid-st st data-width)
                 (equal (len (queue5$extract-state st)) 0))
            (not (queue5$ready-out st)))
   :hints (("Goal" :in-theory (enable queue5$valid-st
                                      queue5$extract-state
                                      queue5$ready-out)))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm queue10$q5-0-get-$data-in-rewrite
     (equal (queue5$data-in
             (queue10$q5-0-inputs inputs st data-width)
             data-width)
            (queue10$data-in inputs data-width))
     :hints (("Goal"
              :in-theory (enable queue5$data-in
                                 queue10$data-in
                                 queue10$q5-0-inputs)))))

  (local
   (defthm queue10$q5-1-get-$data-in-rewrite
     (b* ((q5-0 (nth *queue10$q5-0* st)))
       (implies (queue5$valid-st q5-0 data-width)
                (equal (queue5$data-in
                        (queue10$q5-1-inputs inputs st data-width)
                        data-width)
                       (queue5$data-out q5-0))))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue5$valid-st
                                 queue5$data-in
                                 queue5$data-out
                                 queue10$q5-1-inputs)))))

  (local
   (defthm queue10$q5-1-in-act-=-q5-0-out-act
     (equal (queue5$in-act (queue10$q5-1-inputs inputs st data-width))
            (queue5$out-act (queue10$q5-0-inputs inputs st data-width)))
     :hints (("Goal" :in-theory (enable queue5$in-act
                                        queue5$out-act
                                        queue10$q5-0-inputs
                                        queue10$q5-1-inputs)))))

  (local
   (defthm queue10$q5-0-in-act-rewrite
     (equal (queue5$in-act (queue10$q5-0-inputs inputs st data-width))
            (queue10$in-act inputs))
     :hints (("Goal" :in-theory (enable queue5$in-act
                                        queue10$in-act
                                        queue10$q5-0-inputs)))))

  (local
   (defthm queue10$q5-1-out-act-rewrite
     (equal (queue5$out-act (queue10$q5-1-inputs inputs st data-width))
            (queue10$out-act inputs))
     :hints (("Goal" :in-theory (enable queue5$out-act
                                        queue10$out-act
                                        queue10$q5-1-inputs)))))

  (local
   (defthm queue10$step-spec-correct-aux-1
     (equal (append x (cons e (queue5$extract-state st)))
            (append (append x (list e))
                    (queue5$extract-state st)))))

  (local
   (defthm queue10$step-spec-correct-aux-2
     (equal (append x (cons e (take n (queue5$extract-state st))))
            (append (append x (list e))
                    (take n (queue5$extract-state st))))))

  (defthm queue10$step-spec-correct
    (b* ((next-st (queue10$state-fn inputs st data-width)))
      (implies (and (queue10$input-format inputs st data-width)
                    (queue10$valid-st st data-width))
               (equal (queue10$extract-state next-st)
                      (queue10$step-spec inputs st data-width))))
    :hints (("Goal"
             :use queue10$input-format=>q5-0$input-format
             :in-theory (e/d (get-field
                              queue5$valid-st=>natp-data-width
                              queue5$step-spec
                              queue10$step-spec
                              queue10$input-format
                              queue10$valid-st
                              queue10$state-fn
                              queue10$in-act
                              queue10$out-act
                              queue10$ready-in-
                              queue10$ready-out
                              queue10$extract-state)
                             (queue10$input-format=>q5-0$input-format
                              acl2::associativity-of-append
                              nthcdr
                              len-nthcdr
                              pairlis$
                              strip-cars)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

(encapsulate
  ()

  (local
   (defthm queue10$extract-state-lemma-aux
     (implies (nth 1 inputs)
              (queue5$out-act (queue10$q5-1-inputs inputs st data-width)))
     :hints (("Goal" :in-theory (enable queue5$out-act
                                        queue10$out-act
                                        queue10$q5-1-inputs)))))

  (defthm queue10$extract-state-lemma
    (implies (and (queue10$input-format inputs st data-width)
                  (queue10$valid-st st data-width)
                  (equal n (1- (len (queue10$extract-state st))))
                  (queue10$out-act inputs))
             (equal (append
                     (take n (queue10$extract-state st))
                     (list (queue10$data-out st)))
                    (queue10$extract-state st)))
    :hints (("Goal"
             :do-not-induct t
             :use queue10$input-format=>q5-1$input-format
             :in-theory (e/d (get-field
                              queue5$valid-st=>natp-data-width
                              queue10$input-format
                              queue10$valid-st
                              queue10$extract-state
                              queue10$out-act
                              queue10$ready-out
                              queue10$data-out)
                             (queue10$input-format=>q5-1$input-format)))))
  )

(encapsulate
  ()

  (local
   (defthm queue10$dataflow-correct-aux
     (implies (equal (append x1 y1)
                     (append (queue10$in-seq inputs-lst st data-width n)
                             y2))
              (equal (append x1 y1 z)
                     (append (queue10$in-seq inputs-lst st data-width n)
                             y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (acl2::associativity-of-append))))))

  (defthmd queue10$dataflow-correct
    (b* ((extracted-st (queue10$extract-state st))
         (final-st (queue10$state-fn-n inputs-lst st data-width n))
         (final-extracted-st (queue10$extract-state final-st)))
      (implies (and (queue10$input-format-n inputs-lst st data-width n)
                    (queue10$valid-st st data-width))
               (equal (append final-extracted-st
                              (queue10$out-seq inputs-lst st data-width n))
                      (append (queue10$in-seq inputs-lst st data-width n)
                              extracted-st))))
    :hints (("Goal"
             :in-theory (e/d (queue10$step-spec)
                             ()))))
  )

