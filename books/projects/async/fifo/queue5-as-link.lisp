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
;;; 1. DE Module Generator of Q5'
;;; 2. Specifying the Final State of Q5' After An N-Step Execution
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of Q5'
;;
;; Constructing a DE module generator for a queue of five links, Q5', using the
;; link-joint model. Proving the value and state lemmas for this module
;; generator. Note that Q5' is a complex link.

(defconst *queue5$go-num* 4)
(defconst *queue5$st-len* 10)

(defun queue5$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun queue5$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (queue5$data-ins-len data-width)
     *queue5$go-num*))

;; DE module generator of Q5'. It reports the "ready-in-" signal at its input
;; port, and the "ready-out" signal and output data at its output port.

(module-generator
 queue5* (data-width)
 (si 'queue5 data-width)
 (list* 'in-act 'out-act (append (sis 'data-in 0 data-width)
                                 (sis 'go 0 *queue5$go-num*)))
 (list* 'ready-in- 'ready-out
        (sis 'data-out 0 data-width))
 '(l0 d0 l1 d1 l2 d2 l3 d3 l4 d4)
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
  '(l3 (l3-status) link-cntl (trans3-act trans4-act))
  (list 'd3
        (sis 'd3-out 0 data-width)
        (si 'latch-n data-width)
        (list* 'trans3-act (sis 'd3-in 0 data-width)))

  ;; L4
  '(l4 (l4-status) link-cntl (trans4-act out-act))
  (list 'd4
        (sis 'data-out 0 data-width)
        (si 'latch-n data-width)
        (list* 'trans4-act (sis 'd4-in 0 data-width)))

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

;; DE netlist generator. A generated netlist will contain an instance of Q5'.

(defun queue5$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (queue5* data-width)
        (union$ (latch-n$netlist data-width)
                (v-buf$netlist data-width)
                *joint-cntl*
                :test 'equal)))

;; Sanity syntactic check

(defthmd queue5$netlist-64-okp
  (and (net-syntax-okp (queue5$netlist 64))
       (net-arity-okp (queue5$netlist 64))))

;; Recognizer for Q5'

(defund queue5& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (and (equal (assoc (si 'queue5 data-width) netlist)
              (queue5* data-width))
       (b* ((netlist (delete-to-eq (si 'queue5 data-width) netlist)))
         (and (joint-cntl& netlist)
              (latch-n& netlist data-width)
              (v-buf& netlist data-width)))))

;; Sanity check

(defthm check-queue5$netlist-64
  (queue5& (queue5$netlist 64) 64))

(defconst *queue5$l0* 0)
(defconst *queue5$d0* 1)
(defconst *queue5$l1* 2)
(defconst *queue5$d1* 3)
(defconst *queue5$l2* 4)
(defconst *queue5$d2* 5)
(defconst *queue5$l3* 6)
(defconst *queue5$d3* 7)
(defconst *queue5$l4* 8)
(defconst *queue5$d4* 9)

;; Constraints on the state of Q5'

(defund queue5$st-format (st data-width)
  (b* ((d0 (get-field *queue5$d0* st))
       (d1 (get-field *queue5$d1* st))
       (d2 (get-field *queue5$d2* st))
       (d3 (get-field *queue5$d3* st))
       (d4 (get-field *queue5$d4* st)))
    (and (len-1-true-listp d0)
         (equal (len d0) data-width)

         (len-1-true-listp d1)
         (equal (len d1) data-width)

         (len-1-true-listp d2)
         (equal (len d2) data-width)

         (len-1-true-listp d3)
         (equal (len d3) data-width)

         (len-1-true-listp d4)
         (equal (len d4) data-width))))

(defthmd queue5$st-format=>natp-data-width
  (implies (queue5$st-format st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue5$st-format)))
  :rule-classes :forward-chaining)

(defund queue5$valid-st (st data-width)
  (b* ((l0 (get-field *queue5$l0* st))
       (d0 (get-field *queue5$d0* st))
       (l1 (get-field *queue5$l1* st))
       (d1 (get-field *queue5$d1* st))
       (l2 (get-field *queue5$l2* st))
       (d2 (get-field *queue5$d2* st))
       (l3 (get-field *queue5$l3* st))
       (d3 (get-field *queue5$d3* st))
       (l4 (get-field *queue5$l4* st))
       (d4 (get-field *queue5$d4* st)))
    (and (queue5$st-format st data-width)

         (validp l0)
         (or (emptyp l0)
             (bvp (strip-cars d0)))

         (validp l1)
         (or (emptyp l1)
             (bvp (strip-cars d1)))

         (validp l2)
         (or (emptyp l2)
             (bvp (strip-cars d2)))

         (validp l3)
         (or (emptyp l3)
             (bvp (strip-cars d3)))

         (validp l4)
         (or (emptyp l4)
             (bvp (strip-cars d4))))))

(defthmd queue5$valid-st=>natp-data-width
  (implies (queue5$valid-st st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue5$st-format=>natp-data-width
                                     queue5$valid-st)))
  :rule-classes :forward-chaining)

;; Q5' simulator

(progn
  (defun queue5$map-to-links (st)
    (b* ((l0 (get-field *queue5$l0* st))
         (d0 (get-field *queue5$d0* st))
         (l1 (get-field *queue5$l1* st))
         (d1 (get-field *queue5$d1* st))
         (l2 (get-field *queue5$l2* st))
         (d2 (get-field *queue5$d2* st))
         (l3 (get-field *queue5$l3* st))
         (d3 (get-field *queue5$d3* st))
         (l4 (get-field *queue5$l4* st))
         (d4 (get-field *queue5$d4* st)))
      (map-to-links (list (list 'l0 l0 d0)
                          (list 'l1 l1 d1)
                          (list 'l2 l2 d2)
                          (list 'l3 l3 d3)
                          (list 'l4 l4 d4)))))

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
         (st (list empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data)))
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

;; Extracting the "in-act" signal. It is an input signal for a complex link.

(defund queue5$in-act (inputs)
  (nth 0 inputs))

;; Extracting the "out-act" signal. It is an input signal for a complex link.

(defund queue5$out-act (inputs)
  (nth 1 inputs))

;; Extracting the input data

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

;; Extracting the "ready-in-" signal

(defund queue5$ready-in- (st)
  (b* ((l0 (get-field *queue5$l0* st)))
    (f-buf (car l0))))

(defthm booleanp-queue5$ready-in-
  (implies (queue5$valid-st st data-width)
           (booleanp (queue5$ready-in- st)))
  :hints (("Goal" :in-theory (enable queue5$valid-st
                                     queue5$ready-in-)))
  :rule-classes :type-prescription)

;; Extracting the "ready-out" signal

(defund queue5$ready-out (st)
  (b* ((l4 (get-field *queue5$l4* st)))
    (f-buf (car l4))))

(defthm booleanp-queue5$ready-out
  (implies (queue5$valid-st st data-width)
           (booleanp (queue5$ready-out st)))
  :hints (("Goal" :in-theory (enable queue5$valid-st
                                     queue5$ready-out)))
  :rule-classes :type-prescription)

;; Extracting the output data

(defund queue5$data-out (st)
  (v-threefix (strip-cars (get-field *queue5$d4* st))))

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
  :hints (("Goal" :in-theory (enable queue5$valid-st))))

(defthm bvp-queue5$data-out
  (implies (and (queue5$valid-st st data-width)
                (queue5$ready-out st))
           (bvp (queue5$data-out st)))
  :hints (("Goal" :in-theory (enable queue5$valid-st
                                     queue5$ready-out
                                     queue5$data-out))))

(not-primp-lemma queue5)

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
           :do-not '(preprocess)
           :expand (se (si 'queue5 data-width)
                       (list* in-act out-act (append data-in go-signals))
                       st
                       netlist)
           :in-theory (e/d (de-rules
                            get-field
                            len-1-true-listp=>true-listp
                            not-primp-queue5
                            queue5&
                            queue5*$destructure
                            joint-cntl$value
                            latch-n$value
                            v-buf$value
                            queue5$st-format
                            queue5$ready-in-
                            queue5$ready-out
                            queue5$data-out)
                           ((queue5*)
                            validp
                            fullp
                            emptyp
                            de-module-disabled-rules)))))

;; This function specifies the next state of Q5'.

(defun queue5$state-fn (inputs st data-width)
  (b* ((in-act     (queue5$in-act inputs))
       (out-act    (queue5$out-act inputs))
       (data-in    (queue5$data-in inputs data-width))
       (go-signals (nthcdr (queue5$data-ins-len data-width) inputs))

       (go-trans1 (nth 0 go-signals))
       (go-trans2 (nth 1 go-signals))
       (go-trans3 (nth 2 go-signals))
       (go-trans4 (nth 3 go-signals))

       (l0 (get-field *queue5$l0* st))
       (d0 (get-field *queue5$d0* st))
       (l1 (get-field *queue5$l1* st))
       (d1 (get-field *queue5$d1* st))
       (l2 (get-field *queue5$l2* st))
       (d2 (get-field *queue5$d2* st))
       (l3 (get-field *queue5$l3* st))
       (d3 (get-field *queue5$d3* st))
       (l4 (get-field *queue5$l4* st))
       (d4 (get-field *queue5$d4* st))

       (trans1-act (joint-act (car l0) (car l1) go-trans1))
       (trans2-act (joint-act (car l1) (car l2) go-trans2))
       (trans3-act (joint-act (car l2) (car l3) go-trans3))
       (trans4-act (joint-act (car l3) (car l4) go-trans4)))
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
     (list (f-sr trans3-act trans4-act (car l3)))
     (pairlis$ (fv-if trans3-act (strip-cars d2) (strip-cars d3))
               nil)

     ;; L4
     (list (f-sr trans4-act out-act (car l4)))
     (pairlis$ (fv-if trans4-act (strip-cars d3) (strip-cars d4))
               nil))))

(defthm len-of-queue5$state-fn
  (equal (len (queue5$state-fn inputs st data-width))
         *queue5$st-len*))

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
                    (queue5$state-fn inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :expand (de (si 'queue5 data-width)
                       (list* in-act out-act (append data-in go-signals))
                       st
                       netlist)
           :in-theory (e/d (de-rules
                            get-field
                            len-1-true-listp=>true-listp
                            not-primp-queue5
                            queue5&
                            queue5*$destructure
                            queue5$st-format
                            queue5$in-act
                            queue5$out-act
                            queue5$data-in
                            joint-cntl$value
                            latch-n$value latch-n$state
                            v-buf$value)
                           ((queue5*)
                            validp
                            fullp
                            emptyp
                            de-module-disabled-rules)))))

(in-theory (disable queue5$state-fn))

;; ======================================================================

;; 2. Specifying the Final State of Q5' After An N-Step Execution

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

;; Proving that queue5$st-format is an invariant.

(defthm queue5$st-format-preserved
  (implies (queue5$st-format st data-width)
           (queue5$st-format (queue5$state-fn inputs st data-width)
                             data-width))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue5$st-format
                            queue5$state-fn)
                           ()))))

(defthmd queue5$state-alt
  (implies (and (queue5& netlist data-width)
                (queue5$input-format inputs st data-width)
                (queue5$st-format st data-width))
           (equal (de (si 'queue5 data-width) inputs st netlist)
                  (queue5$state-fn inputs st data-width)))
  :hints (("Goal"
           :in-theory (enable queue5$st-format=>natp-data-width
                              queue5$input-format)
           :use (:instance
                 queue5$state
                 (in-act     (queue5$in-act inputs))
                 (out-act    (queue5$out-act inputs))
                 (data-in    (queue5$data-in inputs data-width))
                 (go-signals (nthcdr (queue5$data-ins-len data-width)
                                     inputs))))))

(state-fn-n-gen queue5 data-width)
(input-format-n-with-state-gen queue5 data-width)

(defthmd de-sim-n$queue5
  (implies (and (queue5& netlist data-width)
                (queue5$input-format-n inputs-lst st data-width n)
                (queue5$st-format st data-width))
           (equal (de-sim-n (si 'queue5 data-width)
                            inputs-lst st netlist
                            n)
                  (queue5$state-fn-n inputs-lst st data-width n)))
  :hints (("Goal" :in-theory (enable queue5$state-alt))))

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for Q5' that extracts the future output sequence
;; from the current state.

(defund queue5$extract-state (st)
  (b* ((l0 (get-field *queue5$l0* st))
       (d0 (get-field *queue5$d0* st))
       (l1 (get-field *queue5$l1* st))
       (d1 (get-field *queue5$d1* st))
       (l2 (get-field *queue5$l2* st))
       (d2 (get-field *queue5$d2* st))
       (l3 (get-field *queue5$l3* st))
       (d3 (get-field *queue5$d3* st))
       (l4 (get-field *queue5$l4* st))
       (d4 (get-field *queue5$d4* st)))
    (extract-state (list l0 d0 l1 d1 l2 d2 l3 d3 l4 d4))))

(defthm queue5$extract-state-not-empty
  (implies (and (queue5$ready-out st)
                (queue5$valid-st st data-width))
           (< 0 (len (queue5$extract-state st))))
  :hints (("Goal" :in-theory (e/d (queue5$valid-st
                                   queue5$extract-state
                                   queue5$ready-out)
                                  (nfix))))
  :rule-classes :linear)

(defthmd queue5$data-out-rewrite
  (implies (and (queue5$valid-st st data-width)
                (equal n (1- (len (queue5$extract-state st))))
                (queue5$ready-out st))
           (equal (list (queue5$data-out st))
                  (list (nth n (queue5$extract-state st)))))
  :hints (("Goal"
           :in-theory (enable queue5$valid-st
                              queue5$extract-state
                              queue5$ready-out
                              queue5$data-out))))

;; Extracting the accepted input sequence

(defun queue5$in-seq (inputs-lst st data-width n)
  (declare (ignorable st)
           (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue5$in-act inputs) t)
          (append (queue5$in-seq (cdr inputs-lst)
                                 (queue5$state-fn inputs st data-width)
                                 data-width
                                 (1- n))
                  (list (queue5$data-in inputs data-width)))
        (queue5$in-seq (cdr inputs-lst)
                       (queue5$state-fn inputs st data-width)
                       data-width
                       (1- n))))))

;; Extracting the valid output sequence

(defun queue5$out-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue5$out-act inputs) t)
          (append (queue5$out-seq (cdr inputs-lst)
                                  (queue5$state-fn inputs st data-width)
                                  data-width
                                  (1- n))
                  (list (queue5$data-out st)))
        (queue5$out-seq (cdr inputs-lst)
                        (queue5$state-fn inputs st data-width)
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
       (st (list empty invalid-data
                 empty invalid-data
                 empty invalid-data
                 empty invalid-data
                 empty invalid-data)))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-lst
                   (queue5$in-seq inputs-lst st data-width n))))
      (list (cons 'out-seq
                  (v-to-nat-lst
                   (queue5$out-seq inputs-lst st data-width n)))))
     state)))

;; The extracted next-state function for Q5'

(defund queue5$step-spec (inputs st data-width)
  (b* ((data-in (queue5$data-in inputs data-width))
       (extracted-st (queue5$extract-state st))
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

(defthm queue5$step-spec-correct
  (b* ((next-st (queue5$state-fn inputs st data-width)))
    (implies (and (queue5$input-format inputs st data-width)
                  (queue5$valid-st st data-width))
             (equal (queue5$extract-state next-st)
                    (queue5$step-spec inputs st data-width))))
  :hints (("Goal"
           :in-theory (enable get-field
                              f-sr
                              queue5$step-spec
                              queue5$input-format
                              queue5$valid-st
                              queue5$st-format
                              queue5$state-fn
                              queue5$ready-in-
                              queue5$ready-out
                              queue5$extract-state))))

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Proving that queue5$valid-st is an invariant.

(defthm queue5$valid-st-preserved
  (implies (and (queue5$input-format inputs st data-width)
                (queue5$valid-st st data-width))
           (queue5$valid-st (queue5$state-fn inputs st data-width)
                            data-width))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue5$input-format
                            queue5$valid-st
                            queue5$st-format
                            queue5$state-fn
                            queue5$ready-in-
                            queue5$ready-out
                            f-sr)
                           (if*
                            nthcdr
                            acl2::true-listp-append)))))

(defthm queue5$extract-state-lemma
  (implies (and (queue5$input-format inputs st data-width)
                (queue5$valid-st st data-width)
                (equal n (1- (len (queue5$extract-state st))))
                (queue5$out-act inputs))
           (equal (append
                   (take n (queue5$extract-state st))
                   (list (queue5$data-out st)))
                  (queue5$extract-state st)))
  :hints (("Goal"
           :in-theory (enable queue5$input-format
                              queue5$valid-st
                              queue5$st-format
                              queue5$extract-state
                              queue5$out-act
                              queue5$ready-out
                              queue5$data-out))))

(encapsulate
  ()

  (local
   (defthm queue5$dataflow-correct-aux
     (implies (equal (append x1 y1)
                     (append (queue5$in-seq inputs-lst st data-width n)
                             y2))
              (equal (append x1 y1 z)
                     (append (queue5$in-seq inputs-lst st data-width n)
                             y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (acl2::associativity-of-append))))))

  (defthmd queue5$dataflow-correct
    (b* ((extracted-st (queue5$extract-state st))
         (final-st (queue5$state-fn-n inputs-lst st data-width n))
         (final-extracted-st (queue5$extract-state final-st)))
      (implies (and (queue5$input-format-n inputs-lst st data-width n)
                    (queue5$valid-st st data-width))
               (equal (append final-extracted-st
                              (queue5$out-seq inputs-lst st data-width n))
                      (append (queue5$in-seq inputs-lst st data-width n)
                              extracted-st))))
    :hints (("Goal"
             :in-theory (e/d (queue5$step-spec)
                             ()))))
  )

