;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; January 2018

(in-package "ADE")

(include-book "link-joint")
(include-book "store-n")
(include-book "vector-module")

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of Q3
;;; 2. Specifying the Final State of Q3 After An N-Step Execution
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of Q3
;;
;; Constructing a DE module generator for a queue of three links, Q3, using the
;; link-joint model. Proving the value and state lemmas for this module
;; generator.

(defconst *queue3$go-num* 4)
(defconst *queue3$st-len* 6)

(defun queue3$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun queue3$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (queue3$data-ins-len data-width)
     *queue3$go-num*))

;; DE module generator of Q3. It reports the "in-act" signal at its input port,
;; and the "out-act" signal and output data at its output port.

(module-generator
 queue3* (data-width)
 (si 'queue3 data-width)
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 data-width)
                                     (sis 'go 0 *queue3$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-width))
 '(l0 d0 l1 d1 l2 d2)
 (list
  ;; LINKS
  ;; L0
  '(l0 (l0-status) link-cntl (in-act trans1-act))
  (list 'd0
        (sis 'd0-out 0 data-width)
        (si 'latch-n data-width)
        (list* 'in-act (sis 'd0-in 0 data-width)))

  ;; L1
  '(l1 (l1-status) link-cntl (trans1-act trans2-act))
  (list 'd1
        (sis 'd1-out 0 data-width)
        (si 'latch-n data-width)
        (list* 'trans1-act (sis 'd1-in 0 data-width)))

  ;; L2
  '(l2 (l2-status) link-cntl (trans2-act out-act))
  (list 'd2
        (sis 'd2-out 0 data-width)
        (si 'latch-n data-width)
        (list* 'trans2-act (sis 'd2-in 0 data-width)))

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

  ;; Transfer data1
  (list 'trans1-cntl
        '(trans1-act)
        'joint-cntl
        (list 'l0-status 'l1-status (si 'go 1)))
  (list 'trans1-op
        (sis 'd1-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'd0-out 0 data-width))

  ;; Transfer data2
  (list 'trans2-cntl
        '(trans2-act)
        'joint-cntl
        (list 'l1-status 'l2-status (si 'go 2)))
  (list 'trans2-op
        (sis 'd2-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'd1-out 0 data-width))

  ;; Out
  (list 'out-cntl
        '(out-act)
        'joint-cntl
        (list 'l2-status 'empty-out- (si 'go 3)))
  (list 'out-op
        (sis 'data-out 0 data-width)
        (si 'v-buf data-width)
        (sis 'd2-out 0 data-width)))

 :guard (natp data-width))

;; DE netlist generator. A generated netlist will contain an instance of Q3.

(defun queue3$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (queue3* data-width)
        (union$ (latch-n$netlist data-width)
                (v-buf$netlist data-width)
                *joint-cntl*
                :test 'equal)))

;; Sanity syntactic check

(defthmd queue3$netlist-64-okp
  (and (net-syntax-okp (queue3$netlist 64))
       (net-arity-okp (queue3$netlist 64))))

;; Recognizer for Q3

(defund queue3& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (and (equal (assoc (si 'queue3 data-width) netlist)
              (queue3* data-width))
       (b* ((netlist (delete-to-eq (si 'queue3 data-width) netlist)))
         (and (joint-cntl& netlist)
              (latch-n& netlist data-width)
              (v-buf& netlist data-width)))))

;; Sanity check

(defthm check-queue3$netlist-64
  (queue3& (queue3$netlist 64) 64))

(defconst *queue3$l0* 0)
(defconst *queue3$d0* 1)
(defconst *queue3$l1* 2)
(defconst *queue3$d1* 3)
(defconst *queue3$l2* 4)
(defconst *queue3$d2* 5)

;; Constraints on the state of Q3

(defund queue3$valid-st (st data-width)
  (b* ((l0 (get-field *queue3$l0* st))
       (d0 (get-field *queue3$d0* st))
       (l1 (get-field *queue3$l1* st))
       (d1 (get-field *queue3$d1* st))
       (l2 (get-field *queue3$l2* st))
       (d2 (get-field *queue3$d2* st)))
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
             (bvp (strip-cars d2))))))

(defthmd queue3$valid-st=>natp-data-width
  (implies (queue3$valid-st st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable queue3$valid-st)))
  :rule-classes :forward-chaining)

;; Q3 simulator

(progn
  (defun queue3$map-to-links (st)
    (b* ((l0 (get-field *queue3$l0* st))
         (d0 (get-field *queue3$d0* st))
         (l1 (get-field *queue3$l1* st))
         (d1 (get-field *queue3$d1* st))
         (l2 (get-field *queue3$l2* st))
         (d2 (get-field *queue3$d2* st)))
      (map-to-links (list (list 'l0 l0 d0)
                          (list 'l1 l1 d1)
                          (list 'l2 l2 d2)))))

  (defun queue3$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (queue3$map-to-links (car x))
            (queue3$map-to-links-list (cdr x)))))

  (defund queue3$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue3$ins-len data-width))
         ((mv inputs-lst state)
          (signal-vals-gen num-signals n state nil))
         ;;(- (cw "~x0~%" inputs-lst))
         (empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (st (list empty invalid-data
                   empty invalid-data
                   empty invalid-data)))
      (mv (pretty-list
           (remove-dup-neighbors
            (queue3$map-to-links-list
             (de-sim-list (si 'queue3 data-width)
                          inputs-lst
                          st
                          (queue3$netlist data-width))))
           0)
          state)))
  )

;; Extracting the input data

(defun queue3$data-in (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (take (mbe :logic (nfix data-width)
             :exec  data-width)
        (nthcdr 2 inputs)))

(defthm len-queue3$data-in
  (equal (len (queue3$data-in inputs data-width))
         (nfix data-width)))

(in-theory (disable queue3$data-in))

;; Extracting the "in-act" signal

(defund queue3$in-act (inputs st data-width)
  (b* ((full-in (nth 0 inputs))
       (go-signals (nthcdr (queue3$data-ins-len data-width) inputs))
       (go-in (nth 0 go-signals))

       (l0 (get-field *queue3$l0* st)))
    (joint-act full-in (car l0) go-in)))

;; Extracting the "out-act" signal

(defund queue3$out-act (inputs st data-width)
  (b* ((empty-out- (nth 1 inputs))
       (go-signals (nthcdr (queue3$data-ins-len data-width) inputs))
       (go-out (nth 3 go-signals))

       (l2 (get-field *queue3$l2* st)))
    (joint-act (car l2) empty-out- go-out)))

;; Extracting the output data

(defund queue3$data-out (st)
  (v-threefix (strip-cars (get-field *queue3$d2* st))))

(defthm len-queue3$data-out
  (implies (queue3$valid-st st data-width)
           (equal (len (queue3$data-out st))
                  data-width))
  :hints (("Goal" :in-theory (enable queue3$valid-st
                                     queue3$data-out))))

(defthm bvp-queue3$data-out
  (implies (and (queue3$valid-st st data-width)
                (queue3$out-act inputs st data-width))
           (bvp (queue3$data-out st)))
  :hints (("Goal" :in-theory (enable queue3$valid-st
                                     queue3$out-act
                                     queue3$data-out))))

(not-primp-lemma queue3)

;; The value lemma for Q3

(defthmd queue3$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (queue3& netlist data-width)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue3$go-num*)
                  (queue3$valid-st st data-width))
             (equal (se (si 'queue3 data-width) inputs st netlist)
                    (list* (queue3$in-act inputs st data-width)
                           (queue3$out-act inputs st data-width)
                           (queue3$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :expand (se (si 'queue3 data-width)
                       (list* full-in empty-out-
                              (append data-in go-signals))
                       st
                       netlist)
           :in-theory (e/d (de-rules
                            get-field
                            len-1-true-listp=>true-listp
                            not-primp-queue3
                            queue3&
                            queue3*$destructure
                            joint-cntl$value
                            latch-n$value
                            v-buf$value
                            queue3$valid-st
                            queue3$in-act
                            queue3$out-act
                            queue3$data-out)
                           ((queue3*)
                            validp
                            fullp
                            emptyp
                            de-module-disabled-rules)))))

;; This function specifies the next state of Q3, namely, the next states of three
;; links L0, L1, and L2.

(defun queue3$state-fn (inputs st data-width)
  (b* ((data-in    (queue3$data-in inputs data-width))
       (go-signals (nthcdr (queue3$data-ins-len data-width) inputs))

       (go-trans1 (nth 1 go-signals))
       (go-trans2 (nth 2 go-signals))

       (l0 (get-field *queue3$l0* st))
       (d0 (get-field *queue3$d0* st))
       (l1 (get-field *queue3$l1* st))
       (d1 (get-field *queue3$d1* st))
       (l2 (get-field *queue3$l2* st))
       (d2 (get-field *queue3$d2* st))

       (in-act (queue3$in-act inputs st data-width))
       (out-act (queue3$out-act inputs st data-width))
       (trans1-act (joint-act (car l0) (car l1) go-trans1))
       (trans2-act (joint-act (car l1) (car l2) go-trans2)))
    (list
     ;; L0
     (list (f-sr in-act trans1-act (car l0)))
     (pairlis$ (fv-if in-act data-in (strip-cars d0))
               nil)

     ;; L1
     (list (f-sr trans1-act trans2-act (car l1)))
     (pairlis$ (fv-if trans1-act (strip-cars d0) (strip-cars d1))
               nil)

     ;; L2
     (list (f-sr trans2-act out-act (car l2)))
     (pairlis$ (fv-if trans2-act (strip-cars d1) (strip-cars d2))
               nil))))

(defthm len-of-queue3$state-fn
  (equal (len (queue3$state-fn inputs st data-width))
         *queue3$st-len*))

;; The state lemma for Q3

(defthmd queue3$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (queue3& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue3$go-num*)
                  (queue3$valid-st st data-width))
             (equal (de (si 'queue3 data-width) inputs st netlist)
                    (queue3$state-fn inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :expand (de (si 'queue3 data-width)
                       (list* full-in empty-out-
                              (append data-in go-signals))
                       st
                       netlist)
           :in-theory (e/d (de-rules
                            get-field
                            len-1-true-listp=>true-listp
                            not-primp-queue3
                            queue3&
                            queue3*$destructure
                            queue3$valid-st
                            queue3$data-in
                            queue3$in-act
                            queue3$out-act
                            joint-cntl$value
                            latch-n$value latch-n$state
                            v-buf$value)
                           ((queue3*)
                            validp
                            fullp
                            emptyp
                            de-module-disabled-rules)))))

(in-theory (disable queue3$state-fn))

;; ======================================================================

;; 2. Specifying the Final State of Q3 After An N-Step Execution

;; Conditions on the inputs

(defund queue3$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out-  (nth 1 inputs))
       (data-in    (queue3$data-in inputs data-width))
       (go-signals (nthcdr (queue3$data-ins-len data-width) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *queue3$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

;; Proving that queue3$valid-st is an invariant.

(defthm queue3$valid-st-preserved
  (implies (and (queue3$input-format inputs data-width)
                (queue3$valid-st st data-width))
           (queue3$valid-st (queue3$state-fn inputs st data-width)
                            data-width))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue3$input-format
                            queue3$valid-st
                            queue3$state-fn
                            queue3$in-act
                            queue3$out-act
                            f-sr)
                           (if*
                            nthcdr
                            acl2::true-listp-append)))))

(defthmd queue3$state-alt
  (implies (and (queue3& netlist data-width)
                (queue3$input-format inputs data-width)
                (queue3$valid-st st data-width))
           (equal (de (si 'queue3 data-width) inputs st netlist)
                  (queue3$state-fn inputs st data-width)))
  :hints (("Goal"
           :in-theory (enable queue3$valid-st=>natp-data-width
                              queue3$input-format)
           :use (:instance
                 queue3$state
                 (full-in    (nth 0 inputs))
                 (empty-out- (nth 1 inputs))
                 (data-in    (queue3$data-in inputs data-width))
                 (go-signals (nthcdr (queue3$data-ins-len data-width)
                                     inputs))))))

(state-fn-n-gen queue3 data-width)
(input-format-n-gen queue3 data-width)

(defthmd de-sim-n$queue3
  (implies (and (queue3& netlist data-width)
                (queue3$input-format-n inputs-lst data-width n)
                (queue3$valid-st st data-width))
           (equal (de-sim-n (si 'queue3 data-width)
                            inputs-lst st netlist
                            n)
                  (queue3$state-fn-n inputs-lst st data-width n)))
  :hints (("Goal" :in-theory (enable queue3$state-alt))))

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for Q3 that computes the future output sequence from
;; the current state.

(defund queue3$extract-state (st)
  (b* ((l0 (get-field *queue3$l0* st))
       (d0 (get-field *queue3$d0* st))
       (l1 (get-field *queue3$l1* st))
       (d1 (get-field *queue3$d1* st))
       (l2 (get-field *queue3$l2* st))
       (d2 (get-field *queue3$d2* st)))
    (extract-state (list l0 d0 l1 d1 l2 d2))))

;; Extracting the accepted input sequence

(defun queue3$in-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue3$in-act inputs st data-width) t)
          (append (queue3$in-seq (cdr inputs-lst)
                                 (queue3$state-fn inputs st data-width)
                                 data-width
                                 (1- n))
                  (list (queue3$data-in inputs data-width)))
        (queue3$in-seq (cdr inputs-lst)
                       (queue3$state-fn inputs st data-width)
                       data-width
                       (1- n))))))

;; Extracting the valid output sequence

(defun queue3$out-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue3$out-act inputs st data-width) t)
          (append (queue3$out-seq (cdr inputs-lst)
                                  (queue3$state-fn inputs st data-width)
                                  data-width
                                  (1- n))
                  (list (queue3$data-out st)))
        (queue3$out-seq (cdr inputs-lst)
                        (queue3$state-fn inputs st data-width)
                        data-width
                        (1- n))))))

;; Input-output sequence simulator

(defund queue3$in-out-seq-sim (data-width n state)
  (declare (xargs :guard (and (natp data-width)
                              (natp n))
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals (queue3$ins-len data-width))
       ((mv inputs-lst state)
        (signal-vals-gen num-signals n state nil))
       (empty '(nil))
       (invalid-data (make-list data-width :initial-element '(x)))
       (st (list empty invalid-data
                 empty invalid-data
                 empty invalid-data)))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-lst
                   (queue3$in-seq inputs-lst st data-width n))))
      (list (cons 'out-seq
                  (v-to-nat-lst
                   (queue3$out-seq inputs-lst st data-width n)))))
     state)))

;; The extracted next-state function for Q3

(defund queue3$step-spec (inputs st data-width)
  (b* ((data-in (queue3$data-in inputs data-width))
       (extracted-st (queue3$extract-state st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue3$out-act inputs st data-width) t)
      (cond
       ((equal (queue3$in-act inputs st data-width) t)
        (cons data-in (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue3$in-act inputs st data-width) t)
          (cons data-in extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(defthm queue3$step-spec-correct
  (b* ((next-st (queue3$state-fn inputs st data-width)))
    (implies (and (queue3$input-format inputs data-width)
                  (queue3$valid-st st data-width))
             (equal (queue3$extract-state next-st)
                    (queue3$step-spec inputs st data-width))))
  :hints (("Goal"
           :in-theory (enable get-field
                              f-sr
                              queue3$step-spec
                              queue3$input-format
                              queue3$valid-st
                              queue3$state-fn
                              queue3$in-act
                              queue3$out-act
                              queue3$extract-state))))

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; (defthm consp-queue3$extract-state
;;   (implies (and (queue3$valid-st st data-width)
;;                 (queue3$out-act inputs st data-width))
;;            (consp (queue3$extract-state st)))
;;   :hints (("Goal"
;;            :in-theory (enable queue3$valid-st
;;                               queue3$extract-state
;;                               queue3$out-act)))
;;   :rule-classes :type-prescription)

(defthm queue3$extract-state-lemma
  (implies (and (queue3$valid-st st data-width)
                (equal n (1- (len (queue3$extract-state st))))
                (queue3$out-act inputs st data-width))
           (equal (append
                   (take n (queue3$extract-state st))
                   (list (queue3$data-out st)))
                  (queue3$extract-state st)))
  :hints (("Goal"
           :in-theory (enable queue3$valid-st
                              queue3$extract-state
                              queue3$out-act
                              queue3$data-out))))

(encapsulate
  ()

  (local
   (defthm queue3$dataflow-correct-aux
     (implies (equal (append x1 y1)
                     (append (queue3$in-seq inputs-lst st data-width n)
                             y2))
              (equal (append x1 y1 z)
                     (append (queue3$in-seq inputs-lst st data-width n)
                             y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (acl2::associativity-of-append))))))

  (defthmd queue3$dataflow-correct
    (b* ((extracted-st (queue3$extract-state st))
         (final-st (queue3$state-fn-n inputs-lst st data-width n))
         (final-extracted-st (queue3$extract-state final-st)))
      (implies (and (queue3$input-format-n inputs-lst data-width n)
                    (queue3$valid-st st data-width))
               (equal (append final-extracted-st
                              (queue3$out-seq inputs-lst st data-width n))
                      (append (queue3$in-seq inputs-lst st data-width n)
                              extracted-st))))
    :hints (("Goal"
             :in-theory (e/d (queue3$step-spec)
                             ()))))
  )

