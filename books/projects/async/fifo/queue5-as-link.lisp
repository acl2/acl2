;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; April 2018

(in-package "ADE")

(include-book "../link-joint")
(include-book "../store-n")
(include-book "../vector-module")

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of Q5'
;;; 2. Specify the Final State of Q5' After An N-Step Execution
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of Q5'
;;
;; Construct a DE module generator for a queue of five links, Q5', using the
;; link-joint model.  Prove the value and state lemmas for this module
;; generator.  Note that Q5' is a complex link.

(defconst *queue5$go-num* 4)
(defconst *queue5$st-len* 5)

(defun queue5$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun queue5$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (queue5$data-ins-len data-width)
     *queue5$go-num*))

;; DE module generator of Q5'

(module-generator
 queue5* (data-width)
 (si 'queue5 data-width)
 ;; INPUTS
 ;; There are 3 types of inputs for a complex link:
 ;; * in-act and out-act signals,
 ;; * input data,
 ;; * GO signals.
 (list* 'in-act 'out-act (append (sis 'data-in 0 data-width)
                                 (sis 'go 0 *queue5$go-num*)))
 ;; OUTPUTS
 ;; For a complex link, in addition to outputing the data, we also report the
 ;; "ready-in-" signals from the links at the module's input ports and the
 ;; "ready-out" signals from the links at the module's output ports.
 (list* 'ready-in- 'ready-out
        (sis 'data-out 0 data-width))
 '(l0 l1 l2 l3 l4)
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
        (list* 'l3-status (sis 'd3-out 0 data-width))
        (si 'link data-width)
        (list* 'trans3-act 'trans4-act (sis 'd3-in 0 data-width)))

  ;; L4
  (list 'l4
        (list* 'l4-status (sis 'data-out 0 data-width))
        (si 'link data-width)
        (list* 'trans4-act 'out-act (sis 'd4-in 0 data-width)))

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

  ;; Transfer data4
  (list 'trans4-cntl
        '(trans4-act)
        'joint-cntl
        (list 'l3-status 'l4-status (si 'go 3)))
  (list 'trans4-op
        (sis 'd4-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'd3-out 0 data-width))

  ;; STATUS
  '(in-status (ready-in-) b-buf (l0-status))
  '(out-status (ready-out) b-buf (l4-status)))

 :guard (natp data-width))

(make-event
 `(progn
    ,@(state-accessors-gen 'queue5 '(l0 l1 l2 l3 l4) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of Q5'.

(defun queue5$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (queue5* data-width)
        (union$ (link$netlist data-width)
                *joint-cntl*
                (v-buf$netlist data-width)
                :test 'equal)))

;; Recognizer for Q5'

(defund queue5& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (and (equal (assoc (si 'queue5 data-width) netlist)
              (queue5* data-width))
       (b* ((netlist (delete-to-eq (si 'queue5 data-width) netlist)))
         (and (link& netlist data-width)
              (joint-cntl& netlist)
              (v-buf& netlist data-width)))))

;; Sanity check

(local
 (defthmd check-queue5$netlist-64
   (and (net-syntax-okp (queue5$netlist 64))
        (net-arity-okp (queue5$netlist 64))
        (queue5& (queue5$netlist 64) 64))))

;; Constraints on the state of Q5'

(defund queue5$st-format (st data-width)
  (b* ((l0 (get-field *queue5$l0* st))
       (l1 (get-field *queue5$l1* st))
       (l2 (get-field *queue5$l2* st))
       (l3 (get-field *queue5$l3* st))
       (l4 (get-field *queue5$l4* st)))
    (and (link$st-format l0 data-width)
         (link$st-format l1 data-width)
         (link$st-format l2 data-width)
         (link$st-format l3 data-width)
         (link$st-format l4 data-width))))

(defthm queue5$st-format=>natp-data-width
  (implies (queue5$st-format st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue5$st-format)))
  :rule-classes :forward-chaining)

(defund queue5$valid-st (st data-width)
  (b* ((l0 (get-field *queue5$l0* st))
       (l1 (get-field *queue5$l1* st))
       (l2 (get-field *queue5$l2* st))
       (l3 (get-field *queue5$l3* st))
       (l4 (get-field *queue5$l4* st)))
    (and (link$valid-st l0 data-width)
         (link$valid-st l1 data-width)
         (link$valid-st l2 data-width)
         (link$valid-st l3 data-width)
         (link$valid-st l4 data-width))))

(defthmd queue5$valid-st=>natp-data-width
  (implies (queue5$valid-st st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue5$valid-st)))
  :rule-classes :forward-chaining)

;; Extract the input and output signals from Q5'

(progn
  ;; Extract the "in-act" signal

  (defund queue5$in-act (inputs)
    (nth 0 inputs))

  ;; Extract the "out-act" signal

  (defund queue5$out-act (inputs)
    (nth 1 inputs))

  ;; Extract the input data

  (defun queue5$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 2 inputs)))

  (defthm len-queue5$data-in
    (equal (len (queue5$data-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable queue5$data-in))

  ;; Extract the "ready-in-" signal

  (defund queue5$ready-in- (st)
    (b* ((l0 (get-field *queue5$l0* st))
         (l0.s (get-field *link$s* l0)))
      (f-buf (car l0.s))))

  (defthm booleanp-queue5$ready-in-
    (implies (queue5$valid-st st data-width)
             (booleanp (queue5$ready-in- st)))
    :hints (("Goal" :in-theory (enable queue5$valid-st
                                       queue5$ready-in-)))
    :rule-classes :type-prescription)

  ;; Extract the "ready-out" signal

  (defund queue5$ready-out (st)
    (b* ((l4 (get-field *queue5$l4* st))
         (l4.s (get-field *link$s* l4)))
      (f-buf (car l4.s))))

  (defthm booleanp-queue5$ready-out
    (implies (queue5$valid-st st data-width)
             (booleanp (queue5$ready-out st)))
    :hints (("Goal" :in-theory (enable queue5$valid-st
                                       queue5$ready-out)))
    :rule-classes :type-prescription)

  ;; Extract the output data

  (defund queue5$data-out (st)
    (v-threefix (strip-cars (get-field *link$d*
                                       (get-field *queue5$l4* st)))))

  (defthm v-threefix-of-queue5$data-out-canceled
    (equal (v-threefix (queue5$data-out st))
           (queue5$data-out st))
    :hints (("Goal" :in-theory (enable queue5$data-out))))

  (defthm len-queue5$data-out-1
    (implies (queue5$st-format st data-width)
             (equal (len (queue5$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable queue5$st-format
                                       queue5$data-out))))

  (defthm len-queue5$data-out-2
    (implies (queue5$valid-st st data-width)
             (equal (len (queue5$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable queue5$valid-st
                                       queue5$data-out))))

  (defthm bvp-queue5$data-out
    (implies (and (queue5$valid-st st data-width)
                  (queue5$ready-out st))
             (bvp (queue5$data-out st)))
    :hints (("Goal" :in-theory (enable queue5$valid-st
                                       queue5$ready-out
                                       queue5$data-out))))
  )

(not-primp-lemma queue5) ;; Prove that Q5' is not a DE primitive.

;; The value lemma for Q5'

(defthmd queue5$value
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue5& netlist data-width)
                  (queue5$st-format st data-width))
             (equal (se (si 'queue5 data-width) inputs st netlist)
                    (list* (queue5$ready-in- st)
                           (queue5$ready-out st)
                           (queue5$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'queue5 data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            not-primp-queue5
                            queue5&
                            queue5*$destructure
                            link$value
                            joint-cntl$value
                            v-buf$value
                            queue5$st-format
                            queue5$ready-in-
                            queue5$ready-out
                            queue5$data-out)
                           ((queue5*)
                            de-module-disabled-rules)))))

;; This function specifies the next state of Q5'.

(defun queue5$step (inputs st data-width)
  (b* ((in-act     (queue5$in-act inputs))
       (out-act    (queue5$out-act inputs))
       (data-in    (queue5$data-in inputs data-width))
       (go-signals (nthcdr (queue5$data-ins-len data-width) inputs))

       (go-trans1 (nth 0 go-signals))
       (go-trans2 (nth 1 go-signals))
       (go-trans3 (nth 2 go-signals))
       (go-trans4 (nth 3 go-signals))

       (l0 (get-field *queue5$l0* st))
       (l0.s (get-field *link$s* l0))
       (l0.d (get-field *link$d* l0))
       (l1 (get-field *queue5$l1* st))
       (l1.s (get-field *link$s* l1))
       (l1.d (get-field *link$d* l1))
       (l2 (get-field *queue5$l2* st))
       (l2.s (get-field *link$s* l2))
       (l2.d (get-field *link$d* l2))
       (l3 (get-field *queue5$l3* st))
       (l3.s (get-field *link$s* l3))
       (l3.d (get-field *link$d* l3))
       (l4 (get-field *queue5$l4* st))
       (l4.s (get-field *link$s* l4))

       (trans1-act (joint-act (car l0.s) (car l1.s) go-trans1))
       (trans2-act (joint-act (car l1.s) (car l2.s) go-trans2))
       (trans3-act (joint-act (car l2.s) (car l3.s) go-trans3))
       (trans4-act (joint-act (car l3.s) (car l4.s) go-trans4))

       (l0-inputs (list* in-act trans1-act data-in))
       (l1-inputs (list* trans1-act trans2-act
                         (fv-if in-act data-in (strip-cars l0.d))))
       (l2-inputs (list* trans2-act trans3-act (strip-cars l1.d)))
       (l3-inputs (list* trans3-act trans4-act (strip-cars l2.d)))
       (l4-inputs (list* trans4-act out-act (strip-cars l3.d))))
    (list
     ;; L0
     (link$step l0-inputs l0 data-width)
     ;; L1
     (link$step l1-inputs l1 data-width)
     ;; L2
     (link$step l2-inputs l2 data-width)
     ;; L3
     (link$step l3-inputs l3 data-width)
     ;; L4
     (link$step l4-inputs l4 data-width))))

(defthm len-of-queue5$step
  (equal (len (queue5$step inputs st data-width))
         *queue5$st-len*))

(defthm queue5$step-v-threefix-of-data-in-canceled
  (implies
   (and (true-listp data-in)
        (equal (len data-in) data-width))
   (equal (queue5$step (list* in-act out-act
                              (append (v-threefix data-in) go-signals))
                       st
                       data-width)
          (queue5$step (list* in-act out-act
                              (append data-in go-signals))
                       st
                       data-width)))
  :hints (("Goal" :in-theory (enable queue5$step
                                     queue5$data-in
                                     queue5$in-act
                                     queue5$out-act))))

;; The state lemma for Q5'

(defthmd queue5$state
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue5& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue5$go-num*)
                  (queue5$st-format st data-width))
             (equal (de (si 'queue5 data-width) inputs st netlist)
                    (queue5$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'queue5 data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            not-primp-queue5
                            queue5&
                            queue5*$destructure
                            queue5$st-format
                            queue5$in-act
                            queue5$out-act
                            queue5$data-in
                            link$value link$state
                            joint-cntl$value
                            v-buf$value)
                           ((queue5*)
                            de-module-disabled-rules)))))

(in-theory (disable queue5$step))

;; ======================================================================

;; 2. Specify the Final State of Q5' After An N-Step Execution

;; Q5' simulator

(progn
  (defun queue5$map-to-links (st)
    (b* ((l0 (get-field *queue5$l0* st))
         (l1 (get-field *queue5$l1* st))
         (l2 (get-field *queue5$l2* st))
         (l3 (get-field *queue5$l3* st))
         (l4 (get-field *queue5$l4* st)))
      (map-to-links (list (list* 'l0 l0)
                          (list* 'l1 l1)
                          (list* 'l2 l2)
                          (list* 'l3 l3)
                          (list* 'l4 l4)))))

  (defun queue5$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (queue5$map-to-links (car x))
            (queue5$map-to-links-list (cdr x)))))

  (defund queue5$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue5$ins-len data-width))
         ((mv inputs-lst state)
          (signal-vals-gen num-signals n state nil))
         ;;(- (cw "~x0~%" inputs-lst))
         (empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (st (list (list empty invalid-data)
                   (list empty invalid-data)
                   (list empty invalid-data)
                   (list empty invalid-data)
                   (list empty invalid-data))))
      (mv (pretty-list
           (remove-dup-neighbors
            (queue5$map-to-links-list
             (de-sim-list (si 'queue5 data-width)
                          inputs-lst
                          st
                          (queue5$netlist data-width))))
           0)
          state)))
  )

;; Conditions on the inputs

(defund queue5$input-format (inputs st data-width)
  (b* ((in-act     (queue5$in-act inputs))
       (out-act    (queue5$out-act inputs))
       (data-in    (queue5$data-in inputs data-width))
       (go-signals (nthcdr (queue5$data-ins-len data-width) inputs))

       (ready-in- (queue5$ready-in- st))
       (ready-out (queue5$ready-out st)))
    (and
     (if ready-in-
         (not in-act)
       (booleanp in-act))
     (if (not ready-out)
         (not out-act)
       (booleanp out-act))
     (or (not in-act) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *queue5$go-num*)
     (equal inputs
            (list* in-act out-act (append data-in go-signals))))))

(simulate-lemma queue5 :complex-link t)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for Q5' that extracts the future output sequence
;; from the current state.

(defund queue5$extract (st)
  (b* ((l0 (get-field *queue5$l0* st))
       (l1 (get-field *queue5$l1* st))
       (l2 (get-field *queue5$l2* st))
       (l3 (get-field *queue5$l3* st))
       (l4 (get-field *queue5$l4* st)))
    (extract-valid-data (list l0 l1 l2 l3 l4))))

(defthm queue5$extract-not-empty
  (implies (and (queue5$ready-out st)
                (queue5$valid-st st data-width))
           (< 0 (len (queue5$extract st))))
  :hints (("Goal" :in-theory (e/d (queue5$valid-st
                                   queue5$extract
                                   queue5$ready-out)
                                  (nfix))))
  :rule-classes :linear)

(defthmd queue5$data-out-rewrite
  (implies (and (queue5$valid-st st data-width)
                (equal n (1- (len (queue5$extract st))))
                (queue5$ready-out st))
           (equal (list (queue5$data-out st))
                  (list (nth n (queue5$extract st)))))
  :hints (("Goal"
           :in-theory (enable queue5$valid-st
                              queue5$extract
                              queue5$ready-out
                              queue5$data-out))))

;; The extracted next-state function for Q5'.  Note that this function avoids
;; exploring the internal computation of Q5'.

(defund queue5$extracted-step (inputs st data-width)
  (b* ((data-in (queue5$data-in inputs data-width))
       (extracted-st (queue5$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue5$out-act inputs) t)
      (cond
       ((equal (queue5$in-act inputs) t)
        (cons data-in (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue5$in-act inputs) t)
          (cons data-in extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(defthm queue5$extracted-step-correct
  (b* ((next-st (queue5$step inputs st data-width)))
    (implies (and (queue5$input-format inputs st data-width)
                  (queue5$valid-st st data-width))
             (equal (queue5$extract next-st)
                    (queue5$extracted-step inputs st data-width))))
  :hints (("Goal"
           :in-theory (enable get-field
                              f-sr
                              queue5$extracted-step
                              queue5$input-format
                              queue5$valid-st
                              queue5$st-format
                              queue5$step
                              queue5$ready-in-
                              queue5$ready-out
                              queue5$extract))))

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Extract the accepted input sequence

(defun queue5$in-seq (inputs-lst st data-width n)
  (declare (ignorable st)
           (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue5$in-act inputs) t)
          (append (queue5$in-seq (cdr inputs-lst)
                                 (queue5$step inputs st data-width)
                                 data-width
                                 (1- n))
                  (list (queue5$data-in inputs data-width)))
        (queue5$in-seq (cdr inputs-lst)
                       (queue5$step inputs st data-width)
                       data-width
                       (1- n))))))

;; Extract the valid output sequence

(defun queue5$out-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue5$out-act inputs) t)
          (append (queue5$out-seq (cdr inputs-lst)
                                  (queue5$step inputs st data-width)
                                  data-width
                                  (1- n))
                  (list (queue5$data-out st)))
        (queue5$out-seq (cdr inputs-lst)
                        (queue5$step inputs st data-width)
                        data-width
                        (1- n))))))

;; Input-output sequence simulator

(defund queue5$in-out-seq-sim (data-width n state)
  (declare (xargs :guard (and (natp data-width)
                              (natp n))
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals (queue5$ins-len data-width))
       ((mv inputs-lst state)
        (signal-vals-gen num-signals n state nil))
       (empty '(nil))
       (invalid-data (make-list data-width :initial-element '(x)))
       (st (list (list empty invalid-data)
                 (list empty invalid-data)
                 (list empty invalid-data)
                 (list empty invalid-data)
                 (list empty invalid-data))))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-lst
                   (queue5$in-seq inputs-lst st data-width n))))
      (list (cons 'out-seq
                  (v-to-nat-lst
                   (queue5$out-seq inputs-lst st data-width n)))))
     state)))

;; Prove that queue5$valid-st is an invariant.

(defthm queue5$valid-st-preserved
  (implies (and (queue5$input-format inputs st data-width)
                (queue5$valid-st st data-width))
           (queue5$valid-st (queue5$step inputs st data-width)
                            data-width))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue5$input-format
                            queue5$valid-st
                            queue5$st-format
                            queue5$step
                            queue5$ready-in-
                            queue5$ready-out
                            f-sr)
                           (if*
                            nthcdr
                            acl2::true-listp-append)))))

(defthm queue5$extract-lemma
  (implies (and (queue5$input-format inputs st data-width)
                (queue5$valid-st st data-width)
                (equal n (1- (len (queue5$extract st))))
                (queue5$out-act inputs))
           (equal (append
                   (take n (queue5$extract st))
                   (list (queue5$data-out st)))
                  (queue5$extract st)))
  :hints (("Goal"
           :in-theory (enable queue5$input-format
                              queue5$valid-st
                              queue5$st-format
                              queue5$extract
                              queue5$out-act
                              queue5$ready-out
                              queue5$data-out))))

(in-out-stream-lemma queue5 :complex-link t)

