;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; April 2018

(in-package "ADE")

(include-book "../link-joint")
(include-book "../vector-module")

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of Q4'
;;; 2. Specify the Final State of Q4' After An N-Step Execution
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of Q4'
;;
;; Construct a DE module generator for a queue of four links, Q4', using the
;; link-joint model.  Prove the value and state lemmas for this module
;; generator.  Note that Q4' is a complex link.

(defconst *queue4$go-num* 3)
(defconst *queue4$st-len* 4)

(defun queue4$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun queue4$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (queue4$data-ins-len data-width)
     *queue4$go-num*))

;; DE module generator of Q4'

(module-generator
 queue4* (data-width)
 (si 'queue4 data-width)
 ;; INPUTS
 ;; There are 3 types of inputs for a complex link:
 ;; * in-act and out-act signals,
 ;; * input data,
 ;; * GO signals.
 (list* 'in-act 'out-act (append (sis 'data-in 0 data-width)
                                 (sis 'go 0 *queue4$go-num*)))
 ;; OUTPUTS
 ;; For a complex link, in addition to outputing the data, we also report the
 ;; "ready-in-" signals from the links at the module's input ports and the
 ;; "ready-out" signals from the links at the module's output ports.
 (list* 'ready-in- 'ready-out
        (sis 'data-out 0 data-width))
 '(l0 l1 l2 l3)
 (list
  ;; LINKS
  ;; L0
  (list 'l0
        (list* 'l0-status (sis 'd0-out 0 data-width))
        (si 'link data-width)
        (list* 'in-act 'trans1-act (sis 'data-in 0 data-width)))

  ;; L1
  (list 'l1
        (list* 'l1-status (sis 'd1-out 0 data-width))
        (si 'link data-width)
        (list* 'trans1-act 'trans2-act (sis 'd1-in 0 data-width)))

  ;; L2
  (list 'l2
        (list* 'l2-status (sis 'd2-out 0 data-width))
        (si 'link data-width)
        (list* 'trans2-act 'trans3-act (sis 'd2-in 0 data-width)))

  ;; L3
  (list 'l3
        (list* 'l3-status (sis 'data-out 0 data-width))
        (si 'link data-width)
        (list* 'trans3-act 'out-act (sis 'd3-in 0 data-width)))

  ;; JOINTS
  ;; Transfer data1
  (list 'trans1-cntl
        '(trans1-act)
        'joint-cntl
        (list 'l0-status 'l1-status (si 'go 0)))
  (list 'trans1-op
        (sis 'd1-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'd0-out 0 data-width))

  ;; Transfer data2
  (list 'trans2-cntl
        '(trans2-act)
        'joint-cntl
        (list 'l1-status 'l2-status (si 'go 1)))
  (list 'trans2-op
        (sis 'd2-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'd1-out 0 data-width))

  ;; Transfer data3
  (list 'trans3-cntl
        '(trans3-act)
        'joint-cntl
        (list 'l2-status 'l3-status (si 'go 2)))
  (list 'trans3-op
        (sis 'd3-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'd2-out 0 data-width))

  ;; STATUS
  '(in-status (ready-in-) b-buf (l0-status))
  '(out-status (ready-out) b-buf (l3-status)))

 :guard (natp data-width))

(make-event
 `(progn
    ,@(state-accessors-gen 'queue4 '(l0 l1 l2 l3) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of Q4'.

(defun queue4$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (queue4* data-width)
        (union$ (link$netlist data-width)
                *joint-cntl*
                (v-buf$netlist data-width)
                :test 'equal)))

;; Recognizer for Q4'

(defund queue4& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (and (equal (assoc (si 'queue4 data-width) netlist)
              (queue4* data-width))
       (b* ((netlist (delete-to-eq (si 'queue4 data-width) netlist)))
         (and (joint-cntl& netlist)
              (link& netlist data-width)
              (v-buf& netlist data-width)))))

;; Sanity check

(local
 (defthmd check-queue4$netlist-64
   (and (net-syntax-okp (queue4$netlist 64))
        (net-arity-okp (queue4$netlist 64))
        (queue4& (queue4$netlist 64) 64))))

;; Constraints on the state of Q4'

(defund queue4$st-format (st data-width)
  (b* ((l0 (get-field *queue4$l0* st))
       (l1 (get-field *queue4$l1* st))
       (l2 (get-field *queue4$l2* st))
       (l3 (get-field *queue4$l3* st)))
    (and (link$st-format l0 data-width)
         (link$st-format l1 data-width)
         (link$st-format l2 data-width)
         (link$st-format l3 data-width))))

(defthm queue4$st-format=>natp-data-width
  (implies (queue4$st-format st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue4$st-format)))
  :rule-classes :forward-chaining)

(defund queue4$valid-st (st data-width)
  (b* ((l0 (get-field *queue4$l0* st))
       (l1 (get-field *queue4$l1* st))
       (l2 (get-field *queue4$l2* st))
       (l3 (get-field *queue4$l3* st)))
    (and (link$valid-st l0 data-width)
         (link$valid-st l1 data-width)
         (link$valid-st l2 data-width)
         (link$valid-st l3 data-width))))

(defthmd queue4$valid-st=>natp-data-width
  (implies (queue4$valid-st st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue4$valid-st)))
  :rule-classes :forward-chaining)

;; Extract the input and output signals from Q4'

(progn
  ;; Extract the "in-act" signal

  (defund queue4$in-act (inputs)
    (nth 0 inputs))

  ;; Extract the "out-act" signal

  (defund queue4$out-act (inputs)
    (nth 1 inputs))

  ;; Extract the input data

  (defun queue4$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 2 inputs)))

  (defthm len-queue4$data-in
    (equal (len (queue4$data-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable queue4$data-in))

  ;; Extract the "ready-in-" signal

  (defund queue4$ready-in- (st)
    (b* ((l0 (get-field *queue4$l0* st))
         (l0.s (get-field *link$s* l0)))
      (f-buf (car l0.s))))

  (defthm booleanp-queue4$ready-in-
    (implies (queue4$valid-st st data-width)
             (booleanp (queue4$ready-in- st)))
    :hints (("Goal" :in-theory (enable queue4$valid-st
                                       queue4$ready-in-)))
    :rule-classes :type-prescription)

  ;; Extract the "ready-out" signal

  (defund queue4$ready-out (st)
    (b* ((l3 (get-field *queue4$l3* st))
         (l3.s (get-field *link$s* l3)))
      (f-buf (car l3.s))))

  (defthm booleanp-queue4$ready-out
    (implies (queue4$valid-st st data-width)
             (booleanp (queue4$ready-out st)))
    :hints (("Goal" :in-theory (enable queue4$valid-st
                                       queue4$ready-out)))
    :rule-classes :type-prescription)

  ;; Extract the output data

  (defund queue4$data-out (st)
    (v-threefix (strip-cars (get-field *link$d*
                                       (get-field *queue4$l3* st)))))

  (defthm v-threefix-of-queue4$data-out-canceled
    (equal (v-threefix (queue4$data-out st))
           (queue4$data-out st))
    :hints (("Goal" :in-theory (enable queue4$data-out))))

  (defthm len-queue4$data-out-1
    (implies (queue4$st-format st data-width)
             (equal (len (queue4$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable queue4$st-format
                                       queue4$data-out))))

  (defthm len-queue4$data-out-2
    (implies (queue4$valid-st st data-width)
             (equal (len (queue4$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable queue4$valid-st
                                       queue4$data-out))))

  (defthm bvp-queue4$data-out
    (implies (and (queue4$valid-st st data-width)
                  (queue4$ready-out st))
             (bvp (queue4$data-out st)))
    :hints (("Goal" :in-theory (enable queue4$valid-st
                                       queue4$ready-out
                                       queue4$data-out))))
  )

(not-primp-lemma queue4) ;; Prove that Q4' is not a DE primitive.

;; The value lemma for Q4'

(defthmd queue4$value
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue4& netlist data-width)
                  (queue4$st-format st data-width))
             (equal (se (si 'queue4 data-width) inputs st netlist)
                    (list* (queue4$ready-in- st)
                           (queue4$ready-out st)
                           (queue4$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'queue4 data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            not-primp-queue4
                            queue4&
                            queue4*$destructure
                            link$value
                            joint-cntl$value
                            v-buf$value
                            queue4$st-format
                            queue4$ready-in-
                            queue4$ready-out
                            queue4$data-out)
                           ((queue4*)
                            de-module-disabled-rules)))))

;; This function specifies the next state of Q4'.

(defun queue4$step (inputs st data-width)
  (b* ((in-act     (queue4$in-act inputs))
       (out-act    (queue4$out-act inputs))
       (data-in    (queue4$data-in inputs data-width))
       (go-signals (nthcdr (queue4$data-ins-len data-width) inputs))

       (go-trans1 (nth 0 go-signals))
       (go-trans2 (nth 1 go-signals))
       (go-trans3 (nth 2 go-signals))

       (l0 (get-field *queue4$l0* st))
       (l0.s (get-field *link$s* l0))
       (l0.d (get-field *link$d* l0))
       (l1 (get-field *queue4$l1* st))
       (l1.s (get-field *link$s* l1))
       (l1.d (get-field *link$d* l1))
       (l2 (get-field *queue4$l2* st))
       (l2.s (get-field *link$s* l2))
       (l2.d (get-field *link$d* l2))
       (l3 (get-field *queue4$l3* st))
       (l3.s (get-field *link$s* l3))

       (trans1-act (joint-act (car l0.s) (car l1.s) go-trans1))
       (trans2-act (joint-act (car l1.s) (car l2.s) go-trans2))
       (trans3-act (joint-act (car l2.s) (car l3.s) go-trans3))

       (l0-inputs (list* in-act trans1-act data-in))
       (l1-inputs (list* trans1-act trans2-act
                         (fv-if in-act data-in (strip-cars l0.d))))
       (l2-inputs (list* trans2-act trans3-act (strip-cars l1.d)))
       (l3-inputs (list* trans3-act out-act (strip-cars l2.d))))
    (list
     ;; L0
     (link$step l0-inputs l0 data-width)
     ;; L1
     (link$step l1-inputs l1 data-width)
     ;; L2
     (link$step l2-inputs l2 data-width)
     ;; L3
     (link$step l3-inputs l3 data-width))))

(defthm len-of-queue4$step
  (equal (len (queue4$step inputs st data-width))
         *queue4$st-len*))

(defthm queue4$step-v-threefix-of-data-in-canceled
  (implies
   (and (true-listp data-in)
        (equal (len data-in) data-width))
   (equal (queue4$step (list* in-act out-act
                              (append (v-threefix data-in) go-signals))
                       st
                       data-width)
          (queue4$step (list* in-act out-act
                              (append data-in go-signals))
                       st
                       data-width)))
  :hints (("Goal" :in-theory (enable queue4$step
                                     queue4$data-in
                                     queue4$in-act
                                     queue4$out-act))))

;; The state lemma for Q4'

(defthmd queue4$state
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue4& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue4$go-num*)
                  (queue4$st-format st data-width))
             (equal (de (si 'queue4 data-width) inputs st netlist)
                    (queue4$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'queue4 data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            not-primp-queue4
                            queue4&
                            queue4*$destructure
                            queue4$st-format
                            queue4$in-act
                            queue4$out-act
                            queue4$data-in
                            link$value link$state
                            joint-cntl$value
                            v-buf$value)
                           ((queue4*)
                            de-module-disabled-rules)))))

(in-theory (disable queue4$step))

;; ======================================================================

;; 2. Specify the Final State of Q4' After An N-Step Execution

;; Q4' simulator

(progn
  (defun queue4$map-to-links (st)
    (b* ((l0 (get-field *queue4$l0* st))
         (l1 (get-field *queue4$l1* st))
         (l2 (get-field *queue4$l2* st))
         (l3 (get-field *queue4$l3* st)))
      (map-to-links (list (list* 'l0 l0)
                          (list* 'l1 l1)
                          (list* 'l2 l2)
                          (list* 'l3 l3)))))

  (defun queue4$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (queue4$map-to-links (car x))
            (queue4$map-to-links-list (cdr x)))))

  (defund queue4$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue4$ins-len data-width))
         ((mv inputs-lst state)
          (signal-vals-gen num-signals n state nil))
         ;;(- (cw "~x0~%" inputs-lst))
         (empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (st (list (list empty invalid-data)
                   (list empty invalid-data)
                   (list empty invalid-data)
                   (list empty invalid-data))))
      (mv (pretty-list
           (remove-dup-neighbors
            (queue4$map-to-links-list
             (de-sim-list (si 'queue4 data-width)
                          inputs-lst
                          st
                          (queue4$netlist data-width))))
           0)
          state)))
  )

;; Conditions on the inputs

(defund queue4$input-format (inputs st data-width)
  (b* ((in-act     (queue4$in-act inputs))
       (out-act    (queue4$out-act inputs))
       (data-in    (queue4$data-in inputs data-width))
       (go-signals (nthcdr (queue4$data-ins-len data-width) inputs))

       (ready-in- (queue4$ready-in- st))
       (ready-out (queue4$ready-out st)))
    (and
     (if ready-in-
         (not in-act)
       (booleanp in-act))
     (if (not ready-out)
         (not out-act)
       (booleanp out-act))
     (or (not in-act) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *queue4$go-num*)
     (equal inputs
            (list* in-act out-act (append data-in go-signals))))))

(simulate-lemma queue4 :complex-link t)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for Q4' that extracts the future output sequence
;; from the current state.

(defund queue4$extract (st)
  (b* ((l0 (get-field *queue4$l0* st))
       (l1 (get-field *queue4$l1* st))
       (l2 (get-field *queue4$l2* st))
       (l3 (get-field *queue4$l3* st)))
    (extract-valid-data (list l0 l1 l2 l3))))

(defthm queue4$extract-not-empty
  (implies (and (queue4$ready-out st)
                (queue4$valid-st st data-width))
           (< 0 (len (queue4$extract st))))
  :hints (("Goal" :in-theory (e/d (queue4$valid-st
                                   queue4$extract
                                   queue4$ready-out)
                                  (nfix))))
  :rule-classes :linear)

(defthmd queue4$data-out-rewrite
  (implies (and (queue4$valid-st st data-width)
                (equal n (1- (len (queue4$extract st))))
                (queue4$ready-out st))
           (equal (list (queue4$data-out st))
                  (list (nth n (queue4$extract st)))))
  :hints (("Goal"
           :in-theory (enable queue4$valid-st
                              queue4$extract
                              queue4$ready-out
                              queue4$data-out))))

;; The extracted next-state function for Q4'.  Note that this function avoids
;; exploring the internal computation of Q4'.

(defund queue4$extracted-step (inputs st data-width)
  (b* ((data-in (queue4$data-in inputs data-width))
       (extracted-st (queue4$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue4$out-act inputs) t)
      (cond
       ((equal (queue4$in-act inputs) t)
        (cons data-in (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue4$in-act inputs) t)
          (cons data-in extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(defthm queue4$extracted-step-correct
  (b* ((next-st (queue4$step inputs st data-width)))
    (implies (and (queue4$input-format inputs st data-width)
                  (queue4$valid-st st data-width))
             (equal (queue4$extract next-st)
                    (queue4$extracted-step inputs st data-width))))
  :hints (("Goal"
           :in-theory (enable get-field
                              f-sr
                              queue4$extracted-step
                              queue4$input-format
                              queue4$valid-st
                              queue4$st-format
                              queue4$step
                              queue4$ready-in-
                              queue4$ready-out
                              queue4$extract))))

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Extract the accepted input sequence

(defun queue4$in-seq (inputs-lst st data-width n)
  (declare (ignorable st)
           (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue4$in-act inputs) t)
          (append (queue4$in-seq (cdr inputs-lst)
                                 (queue4$step inputs st data-width)
                                 data-width
                                 (1- n))
                  (list (queue4$data-in inputs data-width)))
        (queue4$in-seq (cdr inputs-lst)
                       (queue4$step inputs st data-width)
                       data-width
                       (1- n))))))

;; Extract the valid output sequence

(defun queue4$out-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue4$out-act inputs) t)
          (append (queue4$out-seq (cdr inputs-lst)
                                  (queue4$step inputs st data-width)
                                  data-width
                                  (1- n))
                  (list (queue4$data-out st)))
        (queue4$out-seq (cdr inputs-lst)
                        (queue4$step inputs st data-width)
                        data-width
                        (1- n))))))

;; Input-output sequence simulator

(defund queue4$in-out-seq-sim (data-width n state)
  (declare (xargs :guard (and (natp data-width)
                              (natp n))
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals (queue4$ins-len data-width))
       ((mv inputs-lst state)
        (signal-vals-gen num-signals n state nil))
       (empty '(nil))
       (invalid-data (make-list data-width :initial-element '(x)))
       (st (list (list empty invalid-data)
                 (list empty invalid-data)
                 (list empty invalid-data)
                 (list empty invalid-data))))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-lst
                   (queue4$in-seq inputs-lst st data-width n))))
      (list (cons 'out-seq
                  (v-to-nat-lst
                   (queue4$out-seq inputs-lst st data-width n)))))
     state)))

;; Prove that queue4$valid-st is an invariant.

(defthm queue4$valid-st-preserved
  (implies (and (queue4$input-format inputs st data-width)
                (queue4$valid-st st data-width))
           (queue4$valid-st (queue4$step inputs st data-width)
                            data-width))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue4$input-format
                            queue4$valid-st
                            queue4$st-format
                            queue4$step
                            queue4$ready-in-
                            queue4$ready-out
                            f-sr)
                           (if*
                            nthcdr
                            acl2::true-listp-append)))))

(defthm queue4$extract-lemma
  (implies (and (queue4$input-format inputs st data-width)
                (queue4$valid-st st data-width)
                (equal n (1- (len (queue4$extract st))))
                (queue4$out-act inputs))
           (equal (append
                   (take n (queue4$extract st))
                   (list (queue4$data-out st)))
                  (queue4$extract st)))
  :hints (("Goal"
           :in-theory (enable queue4$input-format
                              queue4$valid-st
                              queue4$st-format
                              queue4$extract
                              queue4$out-act
                              queue4$ready-out
                              queue4$data-out))))

(in-out-stream-lemma queue4 :complex-link t)

