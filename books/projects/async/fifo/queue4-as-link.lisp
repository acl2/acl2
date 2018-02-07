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
;;; 1. DE Module Generator of Q4'
;;; 2. Specifying the Final State of Q4' After An N-Step Execution
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of Q4'
;;
;; Constructing a DE module generator for a queue of four links, Q4', using the
;; link-joint model. Proving the value and state lemmas for this module
;; generator. Note that Q4' is a complex link.

(defconst *queue4$go-num* 3)
(defconst *queue4$st-len* 8)

(defun queue4$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun queue4$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (queue4$data-ins-len data-width)
     *queue4$go-num*))

;; DE module generator of Q4'. It reports the "ready-in-" signal at its input
;; port, and the "ready-out" signal and output data at its output port.

(module-generator
 queue4* (data-width)
 (si 'queue4 data-width)
 (list* 'in-act 'out-act (append (sis 'data-in 0 data-width)
                                 (sis 'go 0 *queue4$go-num*)))
 (list* 'ready-in- 'ready-out
        (sis 'data-out 0 data-width))
 '(l0 d0 l1 d1 l2 d2 l3 d3)
 (list
  ;; LINKS
  ;; L0
  '(l0 (l0-status) link-cntl (in-act trans1-act))
  (list 'd0
        (sis 'd0-out 0 data-width)
        (si 'latch-n data-width)
        (list* 'in-act (sis 'data-in 0 data-width)))

  ;; L1
  '(l1 (l1-status) link-cntl (trans1-act trans2-act))
  (list 'd1
        (sis 'd1-out 0 data-width)
        (si 'latch-n data-width)
        (list* 'trans1-act (sis 'd1-in 0 data-width)))

  ;; L2
  '(l2 (l2-status) link-cntl (trans2-act trans3-act))
  (list 'd2
        (sis 'd2-out 0 data-width)
        (si 'latch-n data-width)
        (list* 'trans2-act (sis 'd2-in 0 data-width)))

  ;; L3
  '(l3 (l3-status) link-cntl (trans3-act out-act))
  (list 'd3
        (sis 'data-out 0 data-width)
        (si 'latch-n data-width)
        (list* 'trans3-act (sis 'd3-in 0 data-width)))

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

;; DE netlist generator. A generated netlist will contain an instance of Q4'.

(defun queue4$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (queue4* data-width)
        (union$ (latch-n$netlist data-width)
                (v-buf$netlist data-width)
                *joint-cntl*
                :test 'equal)))

;; Sanity syntactic check

(defthmd queue4$netlist-64-okp
  (and (net-syntax-okp (queue4$netlist 64))
       (net-arity-okp (queue4$netlist 64))))

;; Recognizer for Q4'

(defund queue4& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (and (equal (assoc (si 'queue4 data-width) netlist)
              (queue4* data-width))
       (b* ((netlist (delete-to-eq (si 'queue4 data-width) netlist)))
         (and (joint-cntl& netlist)
              (latch-n& netlist data-width)
              (v-buf& netlist data-width)))))

;; Sanity check

(defthm check-queue4$netlist-64
  (queue4& (queue4$netlist 64) 64))

(defconst *queue4$l0* 0)
(defconst *queue4$d0* 1)
(defconst *queue4$l1* 2)
(defconst *queue4$d1* 3)
(defconst *queue4$l2* 4)
(defconst *queue4$d2* 5)
(defconst *queue4$l3* 6)
(defconst *queue4$d3* 7)

;; Constraints on the state of Q4'

(defund queue4$valid-st (st data-width)
  (b* ((l0 (get-field *queue4$l0* st))
       (d0 (get-field *queue4$d0* st))
       (l1 (get-field *queue4$l1* st))
       (d1 (get-field *queue4$d1* st))
       (l2 (get-field *queue4$l2* st))
       (d2 (get-field *queue4$d2* st))
       (l3 (get-field *queue4$l3* st))
       (d3 (get-field *queue4$d3* st)))
    (and (validp l0)
         (len-1-true-listp d0)
         (equal (len d0) data-width)
         (or (emptyp l0)
             (bvp (strip-cars d0)))

         (validp l1)
         (len-1-true-listp d1)
         (equal (len d1) data-width)
         (or (emptyp l1)
             (bvp (strip-cars d1)))

         (validp l2)
         (len-1-true-listp d2)
         (equal (len d2) data-width)
         (or (emptyp l2)
             (bvp (strip-cars d2)))

         (validp l3)
         (len-1-true-listp d3)
         (equal (len d3) data-width)
         (or (emptyp l3)
             (bvp (strip-cars d3))))))

(defthmd queue4$valid-st=>natp-data-width
  (implies (queue4$valid-st st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue4$valid-st)))
  :rule-classes :forward-chaining)

;; Q4' simulator

(progn
  (defun queue4$map-to-links (st)
    (b* ((l0 (get-field *queue4$l0* st))
         (d0 (get-field *queue4$d0* st))
         (l1 (get-field *queue4$l1* st))
         (d1 (get-field *queue4$d1* st))
         (l2 (get-field *queue4$l2* st))
         (d2 (get-field *queue4$d2* st))
         (l3 (get-field *queue4$l3* st))
         (d3 (get-field *queue4$d3* st)))
      (map-to-links (list (list 'l0 l0 d0)
                          (list 'l1 l1 d1)
                          (list 'l2 l2 d2)
                          (list 'l3 l3 d3)))))

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
         (st (list empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data)))
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

;; Extracting the "in-act" signal. It is an input signal for a complex link.

(defund queue4$in-act (inputs)
  (nth 0 inputs))

;; Extracting the "out-act" signal. It is an input signal for a complex link.

(defund queue4$out-act (inputs)
  (nth 1 inputs))

;; Extracting the input data

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

;; Extracting the "ready-in-" signal

(defund queue4$ready-in- (st)
  (b* ((l0 (get-field *queue4$l0* st)))
    (f-buf (car l0))))

(defthm booleanp-queue4$ready-in-
  (implies (queue4$valid-st st data-width)
           (booleanp (queue4$ready-in- st)))
  :hints (("Goal" :in-theory (enable queue4$valid-st
                                     queue4$ready-in-)))
  :rule-classes :type-prescription)

;; Extracting the "ready-out" signal

(defund queue4$ready-out (st)
  (b* ((l3 (get-field *queue4$l3* st)))
    (f-buf (car l3))))

(defthm booleanp-queue4$ready-out
  (implies (queue4$valid-st st data-width)
           (booleanp (queue4$ready-out st)))
  :hints (("Goal" :in-theory (enable queue4$valid-st
                                     queue4$ready-out)))
  :rule-classes :type-prescription)

;; Extracting the output data

(defund queue4$data-out (st)
  (v-threefix (strip-cars (get-field *queue4$d3* st))))

(defthm len-queue4$data-out
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

(not-primp-lemma queue4)

;; The value lemma for Q4'

(defthmd queue4$value
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue4& netlist data-width)
                  (queue4$valid-st st data-width))
             (equal (se (si 'queue4 data-width) inputs st netlist)
                    (list* (queue4$ready-in- st)
                           (queue4$ready-out st)
                           (queue4$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :expand (se (si 'queue4 data-width)
                       (list* in-act out-act (append data-in go-signals))
                       st
                       netlist)
           :in-theory (e/d (de-rules
                            get-field
                            len-1-true-listp=>true-listp
                            not-primp-queue4
                            queue4&
                            queue4*$destructure
                            joint-cntl$value
                            latch-n$value
                            v-buf$value
                            queue4$valid-st
                            queue4$ready-in-
                            queue4$ready-out
                            queue4$data-out)
                           ((queue4*)
                            validp
                            fullp
                            emptyp
                            de-module-disabled-rules)))))

;; This function specifies the next state of Q4'.

(defun queue4$state-fn (inputs st data-width)
  (b* ((in-act     (queue4$in-act inputs))
       (out-act    (queue4$out-act inputs))
       (data-in    (queue4$data-in inputs data-width))
       (go-signals (nthcdr (queue4$data-ins-len data-width) inputs))

       (go-trans1 (nth 0 go-signals))
       (go-trans2 (nth 1 go-signals))
       (go-trans3 (nth 2 go-signals))

       (l0 (get-field *queue4$l0* st))
       (d0 (get-field *queue4$d0* st))
       (l1 (get-field *queue4$l1* st))
       (d1 (get-field *queue4$d1* st))
       (l2 (get-field *queue4$l2* st))
       (d2 (get-field *queue4$d2* st))
       (l3 (get-field *queue4$l3* st))
       (d3 (get-field *queue4$d3* st))

       (trans1-act (joint-act (car l0) (car l1) go-trans1))
       (trans2-act (joint-act (car l1) (car l2) go-trans2))
       (trans3-act (joint-act (car l2) (car l3) go-trans3)))
    (list
     ;; L0
     (list (f-sr in-act trans1-act (car l0)))
     (pairlis$ (fv-if in-act data-in (strip-cars d0))
               nil)

     ;; L1
     (list (f-sr trans1-act trans2-act (car l1)))
     (pairlis$ (fv-if trans1-act
                      (fv-if in-act data-in (strip-cars d0))
                      (strip-cars d1))
               nil)

     ;; L2
     (list (f-sr trans2-act trans3-act (car l2)))
     (pairlis$ (fv-if trans2-act (strip-cars d1) (strip-cars d2))
               nil)

     ;; L3
     (list (f-sr trans3-act out-act (car l3)))
     (pairlis$ (fv-if trans3-act (strip-cars d2) (strip-cars d3))
               nil))))

(defthm len-of-queue4$state-fn
  (equal (len (queue4$state-fn inputs st data-width))
         *queue4$st-len*))

;; The state lemma for Q4'

(defthmd queue4$state
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue4& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue4$go-num*)
                  (queue4$valid-st st data-width))
             (equal (de (si 'queue4 data-width) inputs st netlist)
                    (queue4$state-fn inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :expand (de (si 'queue4 data-width)
                       (list* in-act out-act (append data-in go-signals))
                       st
                       netlist)
           :in-theory (e/d (de-rules
                            get-field
                            len-1-true-listp=>true-listp
                            not-primp-queue4
                            queue4&
                            queue4*$destructure
                            queue4$valid-st
                            queue4$in-act
                            queue4$out-act
                            queue4$data-in
                            joint-cntl$value
                            latch-n$value latch-n$state
                            v-buf$value)
                           ((queue4*)
                            validp
                            fullp
                            emptyp
                            de-module-disabled-rules)))))

(in-theory (disable queue4$state-fn))

;; ======================================================================

;; 2. Specifying the Final State of Q4' After An N-Step Execution

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

;; Proving that queue4$valid-st is an invariant.

(defthm queue4$valid-st-preserved
  (implies (and (queue4$input-format inputs st data-width)
                (queue4$valid-st st data-width))
           (queue4$valid-st (queue4$state-fn inputs st data-width)
                            data-width))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue4$input-format
                            queue4$valid-st
                            queue4$state-fn
                            queue4$ready-in-
                            queue4$ready-out
                            f-sr)
                           (if*
                            nthcdr
                            acl2::true-listp-append)))))

(defthmd queue4$state-alt
  (implies (and (queue4& netlist data-width)
                (queue4$input-format inputs st data-width)
                (queue4$valid-st st data-width))
           (equal (de (si 'queue4 data-width) inputs st netlist)
                  (queue4$state-fn inputs st data-width)))
  :hints (("Goal"
           :in-theory (enable queue4$valid-st=>natp-data-width
                              queue4$input-format)
           :use (:instance
                 queue4$state
                 (in-act     (queue4$in-act inputs))
                 (out-act    (queue4$out-act inputs))
                 (data-in    (queue4$data-in inputs data-width))
                 (go-signals (nthcdr (queue4$data-ins-len data-width)
                                     inputs))))))

(state-fn-n-gen queue4 data-width)
(input-format-n-with-state-gen queue4 data-width)

(defthmd de-sim-n$queue4
  (implies (and (queue4& netlist data-width)
                (queue4$input-format-n inputs-lst st data-width n)
                (queue4$valid-st st data-width))
           (equal (de-sim-n (si 'queue4 data-width)
                            inputs-lst st netlist
                            n)
                  (queue4$state-fn-n inputs-lst st data-width n)))
  :hints (("Goal" :in-theory (enable queue4$state-alt))))

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for Q4' that extracts the future output sequence
;; from the current state.

(defund queue4$extract-state (st)
  (b* ((l0 (get-field *queue4$l0* st))
       (d0 (get-field *queue4$d0* st))
       (l1 (get-field *queue4$l1* st))
       (d1 (get-field *queue4$d1* st))
       (l2 (get-field *queue4$l2* st))
       (d2 (get-field *queue4$d2* st))
       (l3 (get-field *queue4$l3* st))
       (d3 (get-field *queue4$d3* st)))
    (extract-state (list l0 d0 l1 d1 l2 d2 l3 d3))))

(defthm queue4$extract-state-not-empty
  (implies (and (queue4$ready-out st)
                (queue4$valid-st st data-width))
           (< 0 (len (queue4$extract-state st))))
  :hints (("Goal" :in-theory (e/d (queue4$valid-st
                                   queue4$extract-state
                                   queue4$ready-out)
                                  (nfix))))
  :rule-classes :linear)

(defthmd queue4$data-out-rewrite
  (implies (and (queue4$valid-st st data-width)
                (equal n (1- (len (queue4$extract-state st))))
                (queue4$ready-out st))
           (equal (list (queue4$data-out st))
                  (list (nth n (queue4$extract-state st)))))
  :hints (("Goal"
           :in-theory (enable queue4$valid-st
                              queue4$extract-state
                              queue4$ready-out
                              queue4$data-out))))

;; Extracting the accepted input sequence

(defun queue4$in-seq (inputs-lst st data-width n)
  (declare (ignorable st)
           (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue4$in-act inputs) t)
          (append (queue4$in-seq (cdr inputs-lst)
                                 (queue4$state-fn inputs st data-width)
                                 data-width
                                 (1- n))
                  (list (queue4$data-in inputs data-width)))
        (queue4$in-seq (cdr inputs-lst)
                       (queue4$state-fn inputs st data-width)
                       data-width
                       (1- n))))))

;; Extracting the valid output sequence

(defun queue4$out-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue4$out-act inputs) t)
          (append (queue4$out-seq (cdr inputs-lst)
                                  (queue4$state-fn inputs st data-width)
                                  data-width
                                  (1- n))
                  (list (queue4$data-out st)))
        (queue4$out-seq (cdr inputs-lst)
                        (queue4$state-fn inputs st data-width)
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
       (st (list empty invalid-data
                 empty invalid-data
                 empty invalid-data
                 empty invalid-data)))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-lst
                   (queue4$in-seq inputs-lst st data-width n))))
      (list (cons 'out-seq
                  (v-to-nat-lst
                   (queue4$out-seq inputs-lst st data-width n)))))
     state)))

;; The extracted next-state function for Q4'

(defund queue4$step-spec (inputs st data-width)
  (b* ((data-in (queue4$data-in inputs data-width))
       (extracted-st (queue4$extract-state st))
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

(defthm queue4$step-spec-correct
  (b* ((next-st (queue4$state-fn inputs st data-width)))
    (implies (and (queue4$input-format inputs st data-width)
                  (queue4$valid-st st data-width))
             (equal (queue4$extract-state next-st)
                    (queue4$step-spec inputs st data-width))))
  :hints (("Goal"
           :in-theory (enable get-field
                              f-sr
                              queue4$step-spec
                              queue4$input-format
                              queue4$valid-st
                              queue4$state-fn
                              queue4$ready-in-
                              queue4$ready-out
                              queue4$extract-state))))

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

(defthm queue4$extract-state-lemma
  (implies (and (queue4$input-format inputs st data-width)
                (queue4$valid-st st data-width)
                (equal n (1- (len (queue4$extract-state st))))
                (queue4$out-act inputs))
           (equal (append
                   (take n (queue4$extract-state st))
                   (list (queue4$data-out st)))
                  (queue4$extract-state st)))
  :hints (("Goal"
           :in-theory (enable queue4$input-format
                              queue4$valid-st
                              queue4$extract-state
                              queue4$out-act
                              queue4$ready-out
                              queue4$data-out))))

(encapsulate
  ()

  (local
   (defthm queue4$dataflow-correct-aux
     (implies (equal (append x1 y1)
                     (append (queue4$in-seq inputs-lst st data-width n)
                             y2))
              (equal (append x1 y1 z)
                     (append (queue4$in-seq inputs-lst st data-width n)
                             y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (acl2::associativity-of-append))))))

  (defthmd queue4$dataflow-correct
    (b* ((extracted-st (queue4$extract-state st))
         (final-st (queue4$state-fn-n inputs-lst st data-width n))
         (final-extracted-st (queue4$extract-state final-st)))
      (implies (and (queue4$input-format-n inputs-lst st data-width n)
                    (queue4$valid-st st data-width))
               (equal (append final-extracted-st
                              (queue4$out-seq inputs-lst st data-width n))
                      (append (queue4$in-seq inputs-lst st data-width n)
                              extracted-st))))
    :hints (("Goal"
             :in-theory (e/d (queue4$step-spec)
                             ()))))
  )

