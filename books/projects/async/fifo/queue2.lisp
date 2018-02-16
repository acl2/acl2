;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; February 2018

(in-package "ADE")

(include-book "../link-joint")
(include-book "../store-n")
(include-book "../vector-module")

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of Q2
;;; 2. Specifying the Final State of Q2 After An N-Step Execution
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of Q2
;;
;; Constructing a DE module generator for a queue of two links, Q2, using the
;; link-joint model. Proving the value and state lemmas for this module
;; generator.

(defconst *queue2$go-num* 3)
(defconst *queue2$st-len* 4)

(defun queue2$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun queue2$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (queue2$data-ins-len data-width)
     *queue2$go-num*))

;; DE module generator of Q2. It reports the "in-act" signal at its input port,
;; and the "out-act" signal and output data at its output port.

(module-generator
 queue2* (data-width)
 (si 'queue2 data-width)
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 data-width)
                                     (sis 'go 0 *queue2$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-width))
 '(l0 d0 l1 d1)
 (list
  ;; LINKS
  ;; L0
  '(l0 (l0-status) link-cntl (in-act trans-act))
  (list 'd0
        (sis 'd0-out 0 data-width)
        (si 'latch-n data-width)
        (list* 'in-act (sis 'd0-in 0 data-width)))

  ;; L1
  '(l1 (l1-status) link-cntl (trans-act out-act))
  (list 'd1
        (sis 'd1-out 0 data-width)
        (si 'latch-n data-width)
        (list* 'trans-act (sis 'd1-in 0 data-width)))

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

  ;; Transfer data
  (list 'trans-cntl
        '(trans-act)
        'joint-cntl
        (list 'l0-status 'l1-status (si 'go 1)))
  (list 'trans-op
        (sis 'd1-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'd0-out 0 data-width))

  ;; Out
  (list 'out-cntl
        '(out-act)
        'joint-cntl
        (list 'l1-status 'empty-out- (si 'go 2)))
  (list 'out-op
        (sis 'data-out 0 data-width)
        (si 'v-buf data-width)
        (sis 'd1-out 0 data-width)))

 :guard (natp data-width))

(make-event
 `(progn
    ,@(state-accessors-gen 'queue2 '(l0 d0 l1 d1) 0)))

;; DE netlist generator. A generated netlist will contain an instance of Q2.

(defun queue2$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (queue2* data-width)
        (union$ (latch-n$netlist data-width)
                (v-buf$netlist data-width)
                *joint-cntl*
                :test 'equal)))

;; Recognizer for Q2

(defund queue2& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (and (equal (assoc (si 'queue2 data-width) netlist)
              (queue2* data-width))
       (b* ((netlist (delete-to-eq (si 'queue2 data-width) netlist)))
         (and (joint-cntl& netlist)
              (latch-n& netlist data-width)
              (v-buf& netlist data-width)))))

;; Sanity check

(local
 (defthmd check-queue2$netlist-64
   (and (net-syntax-okp (queue2$netlist 64))
        (net-arity-okp (queue2$netlist 64))
        (queue2& (queue2$netlist 64) 64))))

;; Constraints on the state of Q2

(defund queue2$st-format (st data-width)
  (b* ((d0 (get-field *queue2$d0* st))
       (d1 (get-field *queue2$d1* st)))
    (and (len-1-true-listp d0)
         (equal (len d0) data-width)

         (len-1-true-listp d1)
         (equal (len d1) data-width))))

(defthm queue2$st-format=>natp-data-width
  (implies (queue2$st-format st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue2$st-format)))
  :rule-classes :forward-chaining)

(defund queue2$valid-st (st data-width)
  (b* ((l0 (get-field *queue2$l0* st))
       (d0 (get-field *queue2$d0* st))
       (l1 (get-field *queue2$l1* st))
       (d1 (get-field *queue2$d1* st)))
    (and (queue2$st-format st data-width)

         (validp l0)
         (or (emptyp l0)
             (bvp (strip-cars d0)))

         (validp l1)
         (or (emptyp l1)
             (bvp (strip-cars d1))))))

(defthmd queue2$valid-st=>natp-data-width
  (implies (queue2$valid-st st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue2$valid-st)))
  :rule-classes :forward-chaining)

;; Q2 simulator

(progn
  (defun queue2$map-to-links (st)
    (b* ((l0 (get-field *queue2$l0* st))
         (d0 (get-field *queue2$d0* st))
         (l1 (get-field *queue2$l1* st))
         (d1 (get-field *queue2$d1* st)))
      (map-to-links (list (list 'l0 l0 d0)
                          (list 'l1 l1 d1)))))

  (defun queue2$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (queue2$map-to-links (car x))
            (queue2$map-to-links-list (cdr x)))))

  (defund queue2$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue2$ins-len data-width))
         ((mv inputs-lst state)
          (signal-vals-gen num-signals n state nil))
         ;;(- (cw "~x0~%" inputs-lst))
         (empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (st (list empty invalid-data
                   empty invalid-data)))
      (mv (pretty-list
           (remove-dup-neighbors
            (queue2$map-to-links-list
             (de-sim-list (si 'queue2 data-width)
                          inputs-lst
                          st
                          (queue2$netlist data-width))))
           0)
          state)))
  )

;; Extracting the input data

(defun queue2$data-in (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (take (mbe :logic (nfix data-width)
             :exec  data-width)
        (nthcdr 2 inputs)))

(defthm len-queue2$data-in
  (equal (len (queue2$data-in inputs data-width))
         (nfix data-width)))

(in-theory (disable queue2$data-in))

;; Extracting the "in-act" signal

(defund queue2$in-act (inputs st data-width)
  (b* ((full-in (nth 0 inputs))
       (go-signals (nthcdr (queue2$data-ins-len data-width) inputs))
       (go-in (nth 0 go-signals))

       (l0 (get-field *queue2$l0* st)))
    (joint-act full-in (car l0) go-in)))

;; Extracting the "out-act" signal

(defund queue2$out-act (inputs st data-width)
  (b* ((empty-out- (nth 1 inputs))
       (go-signals (nthcdr (queue2$data-ins-len data-width) inputs))
       (go-out (nth 2 go-signals))

       (l1 (get-field *queue2$l1* st)))
    (joint-act (car l1) empty-out- go-out)))

;; Extracting the output data

(defund queue2$data-out (st)
  (v-threefix (strip-cars (get-field *queue2$d1* st))))

(defthm len-queue2$data-out-1
  (implies (queue2$st-format st data-width)
           (equal (len (queue2$data-out st))
                  data-width))
  :hints (("Goal" :in-theory (enable queue2$st-format
                                     queue2$data-out))))

(defthm len-queue2$data-out-2
  (implies (queue2$valid-st st data-width)
           (equal (len (queue2$data-out st))
                  data-width))
  :hints (("Goal" :in-theory (enable queue2$valid-st))))

(defthm bvp-queue2$data-out
  (implies (and (queue2$valid-st st data-width)
                (queue2$out-act inputs st data-width))
           (bvp (queue2$data-out st)))
  :hints (("Goal" :in-theory (enable queue2$valid-st
                                     queue2$out-act
                                     queue2$data-out))))

(not-primp-lemma queue2)

;; The value lemma for Q2

(defthmd queue2$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (queue2& netlist data-width)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue2$go-num*)
                  (queue2$st-format st data-width))
             (equal (se (si 'queue2 data-width) inputs st netlist)
                    (list* (queue2$in-act inputs st data-width)
                           (queue2$out-act inputs st data-width)
                           (queue2$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :expand (se (si 'queue2 data-width)
                       (list* full-in empty-out-
                              (append data-in go-signals))
                       st
                       netlist)
           :in-theory (e/d (de-rules
                            get-field
                            len-1-true-listp=>true-listp
                            not-primp-queue2
                            queue2&
                            queue2*$destructure
                            joint-cntl$value
                            latch-n$value
                            v-buf$value
                            queue2$st-format
                            queue2$in-act
                            queue2$out-act
                            queue2$data-out)
                           ((queue2*)
                            de-module-disabled-rules)))))

;; This function specifies the next state of Q2, namely, the next states of two
;; links L0 and L1.

(defun queue2$state-fn (inputs st data-width)
  (b* ((data-in    (queue2$data-in inputs data-width))
       (go-signals (nthcdr (queue2$data-ins-len data-width) inputs))

       (go-trans (nth 1 go-signals))

       (l0 (get-field *queue2$l0* st))
       (d0 (get-field *queue2$d0* st))
       (l1 (get-field *queue2$l1* st))
       (d1 (get-field *queue2$d1* st))

       (in-act (queue2$in-act inputs st data-width))
       (out-act (queue2$out-act inputs st data-width))
       (trans-act (joint-act (car l0) (car l1) go-trans)))
    (list
     ;; L0
     (list (f-sr in-act trans-act (car l0)))
     (pairlis$ (fv-if in-act data-in (strip-cars d0))
               nil)

     ;; L1
     (list (f-sr trans-act out-act (car l1)))
     (pairlis$ (fv-if trans-act (strip-cars d0) (strip-cars d1))
               nil))))

(defthm len-of-queue2$state-fn
  (equal (len (queue2$state-fn inputs st data-width))
         *queue2$st-len*))

;; The state lemma for Q2

(defthmd queue2$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (queue2& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue2$go-num*)
                  (queue2$st-format st data-width))
             (equal (de (si 'queue2 data-width) inputs st netlist)
                    (queue2$state-fn inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :expand (de (si 'queue2 data-width)
                       (list* full-in empty-out-
                              (append data-in go-signals))
                       st
                       netlist)
           :in-theory (e/d (de-rules
                            get-field
                            len-1-true-listp=>true-listp
                            not-primp-queue2
                            queue2&
                            queue2*$destructure
                            queue2$st-format
                            queue2$data-in
                            queue2$in-act
                            queue2$out-act
                            joint-cntl$value
                            latch-n$value latch-n$state
                            v-buf$value)
                           ((queue2*)
                            de-module-disabled-rules)))))

(in-theory (disable queue2$state-fn))

;; ======================================================================

;; 2. Specifying the Final State of Q2 After An N-Step Execution

;; Conditions on the inputs

(defund queue2$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (queue2$data-in inputs data-width))
       (go-signals (nthcdr (queue2$data-ins-len data-width) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *queue2$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(simulate-lemma queue2)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for Q2 that extracts the future output sequence from
;; the current state.

(defund queue2$extract-state (st)
  (b* ((l0 (get-field *queue2$l0* st))
       (d0 (get-field *queue2$d0* st))
       (l1 (get-field *queue2$l1* st))
       (d1 (get-field *queue2$d1* st)))
    (extract-state (list l0 d0 l1 d1))))

(defthm queue2$extract-state-not-empty
  (implies (and (queue2$out-act inputs st data-width)
                (queue2$valid-st st data-width))
           (< 0 (len (queue2$extract-state st))))
  :hints (("Goal"
           :in-theory (e/d (queue2$valid-st
                            queue2$extract-state
                            queue2$out-act)
                           (nfix))))
  :rule-classes :linear)

;; Extracting the accepted input sequence

(defun queue2$in-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue2$in-act inputs st data-width) t)
          (append (queue2$in-seq (cdr inputs-lst)
                                 (queue2$state-fn inputs st data-width)
                                 data-width
                                 (1- n))
                  (list (queue2$data-in inputs data-width)))
        (queue2$in-seq (cdr inputs-lst)
                       (queue2$state-fn inputs st data-width)
                       data-width
                       (1- n))))))

;; Extracting the valid output sequence

(defun queue2$out-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue2$out-act inputs st data-width) t)
          (append (queue2$out-seq (cdr inputs-lst)
                                  (queue2$state-fn inputs st data-width)
                                  data-width
                                  (1- n))
                  (list (queue2$data-out st)))
        (queue2$out-seq (cdr inputs-lst)
                        (queue2$state-fn inputs st data-width)
                        data-width
                        (1- n))))))

;; Input-output sequence simulator

(defund queue2$in-out-seq-sim (data-width n state)
  (declare (xargs :guard (and (natp data-width)
                              (natp n))
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals (queue2$ins-len data-width))
       ((mv inputs-lst state)
        (signal-vals-gen num-signals n state nil))
       (empty '(nil))
       (invalid-data (make-list data-width :initial-element '(x)))
       (st (list empty invalid-data
                 empty invalid-data)))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-lst
                   (queue2$in-seq inputs-lst st data-width n))))
      (list (cons 'out-seq
                  (v-to-nat-lst
                   (queue2$out-seq inputs-lst st data-width n)))))
     state)))

;; The extracted next-state function for Q2

(defund queue2$step-spec (inputs st data-width)
  (b* ((data-in (queue2$data-in inputs data-width))
       (extracted-st (queue2$extract-state st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue2$out-act inputs st data-width) t)
      (cond
       ((equal (queue2$in-act inputs st data-width) t)
        (cons data-in (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue2$in-act inputs st data-width) t)
          (cons data-in extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(defthm queue2$step-spec-correct
  (b* ((next-st (queue2$state-fn inputs st data-width)))
    (implies (and (queue2$input-format inputs data-width)
                  (queue2$valid-st st data-width))
             (equal (queue2$extract-state next-st)
                    (queue2$step-spec inputs st data-width))))
  :hints (("Goal"
           :in-theory (enable get-field
                              f-sr
                              queue2$step-spec
                              queue2$input-format
                              queue2$valid-st
                              queue2$st-format
                              queue2$state-fn
                              queue2$in-act
                              queue2$out-act
                              queue2$extract-state))))

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Proving that queue2$valid-st is an invariant.

(defthm queue2$valid-st-preserved
  (implies (and (queue2$input-format inputs data-width)
                (queue2$valid-st st data-width))
           (queue2$valid-st (queue2$state-fn inputs st data-width)
                            data-width))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue2$input-format
                            queue2$valid-st
                            queue2$st-format
                            queue2$state-fn
                            queue2$in-act
                            queue2$out-act
                            f-sr)
                           (if*
                            nthcdr
                            acl2::true-listp-append)))))

(defthm queue2$extract-state-lemma
  (implies (and (queue2$valid-st st data-width)
                (equal n (1- (len (queue2$extract-state st))))
                (queue2$out-act inputs st data-width))
           (equal (append
                   (take n (queue2$extract-state st))
                   (list (queue2$data-out st)))
                  (queue2$extract-state st)))
  :hints (("Goal"
           :in-theory (enable queue2$valid-st
                              queue2$st-format
                              queue2$extract-state
                              queue2$out-act
                              queue2$data-out))))

(in-out-stream-lemma queue2)

