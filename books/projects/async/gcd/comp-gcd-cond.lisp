;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; April 2018

(in-package "ADE")

(include-book "gcd-cond")
(include-book "../fifo/queue2")
(include-book "../fifo/queue3")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of COMP-GCD-COND
;;; 2. Specify the Final State of COMP-GCD-COND After An N-Step Execution
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of COMP-GCD-COND
;;
;; Construct a DE module generator for COMP-GCD-COND using the link-joint
;; model.  Prove the value and state lemmas for this module generator.

(defconst *comp-gcd-cond$prim-go-num* 1)
(defconst *comp-gcd-cond$go-num* (+ *comp-gcd-cond$prim-go-num*
                                    *queue2$go-num*
                                    *queue3$go-num*
                                    *gcd-cond$go-num*))
(defconst *comp-gcd-cond$st-len* 10)

(defun comp-gcd-cond$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 3 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun comp-gcd-cond$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (comp-gcd-cond$data-ins-len data-width)
     *comp-gcd-cond$go-num*))

;; DE module generator of COMP-GCD-COND

(module-generator
 comp-gcd-cond* (data-width)
 (si 'comp-gcd-cond data-width)
 (list* 'full-in 'empty-out0- 'empty-out1-
        (append (sis 'data-in 0 (* 2 data-width))
                (sis 'go 0 *comp-gcd-cond$go-num*)))
 (list* 'in-act 'out-act 'out-act0 'out-act1 'flag
        (append (sis 'data-out0 0 data-width)
                (sis 'data-out1 0 (* 2 data-width))))
 '(la0 a0 lb0 b0 la1 a1 lb1 b1 q2 q3)
 (list
  ;; LINKS
  ;; A0
  '(la0 (a0-status) link-cntl (in-act q2-in-act))
  (list 'a0
        (sis 'a0-out 0 data-width)
        (si 'latch-n data-width)
        (list* 'in-act (sis 'a0-in 0 data-width)))

  ;; B0
  '(lb0 (b0-status) link-cntl (in-act q3-in-act))
  (list 'b0
        (sis 'b0-out 0 data-width)
        (si 'latch-n data-width)
        (list* 'in-act (sis 'b0-in 0 data-width)))

  ;; A1
  '(la1 (a1-status) link-cntl (q2-out-act out-act))
  (list 'a1
        (sis 'a1-out 0 data-width)
        (si 'latch-n data-width)
        (list* 'q2-out-act (sis 'q2-data-out 0 data-width)))

  ;; B1
  '(lb1 (b1-status) link-cntl (q3-out-act out-act))
  (list 'b1
        (sis 'b1-out 0 data-width)
        (si 'latch-n data-width)
        (list* 'q3-out-act (sis 'q3-data-out 0 data-width)))

  ;; STATUS
  '(in-status (ready-in-) b-or (a0-status b0-status))
  '(out-status (ready-out) b-and (a1-status b1-status))

  ;; JOINTS
  ;; 2-link queue Q2
  (list 'q2
        (list* 'q2-in-act 'q2-out-act
               (sis 'q2-data-out 0 data-width))
        (si 'queue2 data-width)
        (list* 'a0-status 'a1-status
               (append (sis 'a0-out 0 data-width)
                       (sis 'go
                            (+ *comp-gcd-cond$prim-go-num*
                               *gcd-cond$go-num*)
                            *queue2$go-num*))))

  ;; 3-link queue Q3
  (list 'q3
        (list* 'q3-in-act 'q3-out-act
               (sis 'q3-data-out 0 data-width))
        (si 'queue3 data-width)
        (list* 'b0-status 'b1-status
               (append (sis 'b0-out 0 data-width)
                       (sis 'go
                            (+ *comp-gcd-cond$prim-go-num*
                               *gcd-cond$go-num*
                               *queue2$go-num*)
                            *queue3$go-num*))))

  ;; In
  (list 'in-cntl
        '(in-act)
        'joint-cntl
        (list 'full-in 'ready-in- (si 'go 0)))
  (list 'in-op0
        (sis 'a0-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'data-in 0 data-width))
  (list 'in-op1
        (sis 'b0-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'data-in data-width data-width))

  ;; Out
  (list 'branch-out
        (list* 'out-act 'out-act0 'out-act1 'flag
               (append (sis 'data-out0 0 data-width)
                       (sis 'data-out1 0 (* 2 data-width))))
        (si 'gcd-cond data-width)
        (list* 'ready-out 'empty-out0- 'empty-out1-
               (append (append (sis 'a1-out 0 data-width)
                               (sis 'b1-out 0 data-width))
                       (sis 'go
                            *comp-gcd-cond$prim-go-num*
                            *gcd-cond$go-num*)))))

 :guard (natp data-width))

(make-event
 `(progn
    ,@(state-accessors-gen 'comp-gcd-cond
                           '(la0 a0 lb0 b0 la1 a1 lb1 b1 q2 q3)
                           0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; COMP-GCD-COND.

(defun comp-gcd-cond$netlist (data-width)
  (declare (xargs :guard (and (natp data-width)
                              (<= 2 data-width))))
  (cons (comp-gcd-cond* data-width)
        (union$ (queue2$netlist data-width)
                (queue3$netlist data-width)
                (gcd-cond$netlist data-width)
                :test 'equal)))

;; Recognizer for COMP-GCD-COND

(defund comp-gcd-cond& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (and (natp data-width)
                              (<= 2 data-width)))))
  (and (equal (assoc (si 'comp-gcd-cond data-width) netlist)
              (comp-gcd-cond* data-width))
       (b* ((netlist (delete-to-eq (si 'comp-gcd-cond data-width) netlist)))
         (and (joint-cntl& netlist)
              (latch-n& netlist data-width)
              (v-buf& netlist data-width)
              (gcd-cond& netlist data-width)
              (queue2& netlist data-width)
              (queue3& netlist data-width)))))

;; Sanity check

(local
 (defthmd check-comp-gcd-cond$netlist-64
   (and (net-syntax-okp (comp-gcd-cond$netlist 64))
        (net-arity-okp (comp-gcd-cond$netlist 64))
        (comp-gcd-cond& (comp-gcd-cond$netlist 64) 64))))

;; Constraints on the state of COMP-GCD-COND

(defund comp-gcd-cond$st-format (st data-width)
  (b* ((a0 (get-field *comp-gcd-cond$a0* st))
       (b0 (get-field *comp-gcd-cond$b0* st))
       (a1 (get-field *comp-gcd-cond$a1* st))
       (b1 (get-field *comp-gcd-cond$b1* st))
       (q2 (get-field *comp-gcd-cond$q2* st))
       (q3 (get-field *comp-gcd-cond$q3* st)))
    (and (natp data-width)
         (<= 3 data-width)

         (len-1-true-listp a0)
         (equal (len a0) data-width)

         (len-1-true-listp b0)
         (equal (len b0) data-width)

         (len-1-true-listp a1)
         (equal (len a1) data-width)

         (len-1-true-listp b1)
         (equal (len b1) data-width)

         (queue2$st-format q2 data-width)
         (queue3$st-format q3 data-width))))

(defthm comp-gcd-cond$st-format=>data-width-constraint
  (implies (comp-gcd-cond$st-format st data-width)
           (and (natp data-width)
                (<= 3 data-width)))
  :hints (("Goal" :in-theory (enable comp-gcd-cond$st-format)))
  :rule-classes :forward-chaining)

(defund comp-gcd-cond$valid-st (st data-width)
  (b* ((la0 (get-field *comp-gcd-cond$la0* st))
       (a0  (get-field *comp-gcd-cond$a0* st))
       (lb0 (get-field *comp-gcd-cond$lb0* st))
       (b0  (get-field *comp-gcd-cond$b0* st))
       (la1 (get-field *comp-gcd-cond$la1* st))
       (a1  (get-field *comp-gcd-cond$a1* st))
       (lb1 (get-field *comp-gcd-cond$lb1* st))
       (b1  (get-field *comp-gcd-cond$b1* st))
       (q2  (get-field *comp-gcd-cond$q2* st))
       (q3  (get-field *comp-gcd-cond$q3* st)))
    (and (comp-gcd-cond$st-format st data-width)

         (validp la0)
         (or (emptyp la0)
             (bvp (strip-cars a0)))

         (validp lb0)
         (or (emptyp lb0)
             (bvp (strip-cars b0)))

         (validp la1)
         (or (emptyp la1)
             (bvp (strip-cars a1)))

         (validp lb1)
         (or (emptyp lb1)
             (bvp (strip-cars b1)))

         (queue2$valid-st q2 data-width)
         (queue3$valid-st q3 data-width))))

(defthmd comp-gcd-cond$valid-st=>data-width-constraint
  (implies (comp-gcd-cond$valid-st st data-width)
           (and (natp data-width)
                (<= 3 data-width)))
  :hints (("Goal"
           :in-theory (enable comp-gcd-cond$valid-st)))
  :rule-classes :forward-chaining)

;; Extract the input and output signals from COMP-GCD-COND

(progn
  ;; Extract the input data

  (defun comp-gcd-cond$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (* 2 (mbe :logic (nfix data-width)
                    :exec  data-width))
          (nthcdr 3 inputs)))

  (defthm len-comp-gcd-cond$data-in
    (equal (len (comp-gcd-cond$data-in inputs data-width))
           (* 2 (nfix data-width))))

  (in-theory (disable comp-gcd-cond$data-in))

  ;; Extract the inputs for the Q2 joint

  (defund comp-gcd-cond$q2-inputs (inputs st data-width)
    (b* ((go-signals (nthcdr (comp-gcd-cond$data-ins-len data-width) inputs))

         (q2-go-signals (take *queue2$go-num*
                              (nthcdr (+ *comp-gcd-cond$prim-go-num*
                                         *gcd-cond$go-num*)
                                      go-signals)))

         (la0 (get-field *comp-gcd-cond$la0* st))
         (a0  (get-field *comp-gcd-cond$a0* st))
         (la1 (get-field *comp-gcd-cond$la1* st)))

      (list* (f-buf (car la0)) (f-buf (car la1))
             (append (v-threefix (strip-cars a0))
                     q2-go-signals))))

  ;; Extract the inputs for the Q3 joint

  (defund comp-gcd-cond$q3-inputs (inputs st data-width)
    (b* ((go-signals (nthcdr (comp-gcd-cond$data-ins-len data-width) inputs))

         (q3-go-signals (take *queue3$go-num*
                              (nthcdr (+ *comp-gcd-cond$prim-go-num*
                                         *gcd-cond$go-num*
                                         *queue2$go-num*)
                                      go-signals)))

         (lb0 (get-field *comp-gcd-cond$lb0* st))
         (b0  (get-field *comp-gcd-cond$b0* st))
         (lb1 (get-field *comp-gcd-cond$lb1* st)))

      (list* (f-buf (car lb0)) (f-buf (car lb1))
             (append (v-threefix (strip-cars b0))
                     q3-go-signals))))

  ;; Extract the inputs for the branch-out joint

  (defund comp-gcd-cond$br-inputs (inputs st data-width)
    (b* ((empty-out0- (nth 1 inputs))
         (empty-out1- (nth 2 inputs))
         (go-signals (nthcdr (comp-gcd-cond$data-ins-len data-width)
                             inputs))

         (br-go-signals (take *gcd-cond$go-num*
                              (nthcdr *comp-gcd-cond$prim-go-num*
                                      go-signals)))

         (la1 (get-field *comp-gcd-cond$la1* st))
         (a1  (get-field *comp-gcd-cond$a1* st))
         (lb1 (get-field *comp-gcd-cond$lb1* st))
         (b1  (get-field *comp-gcd-cond$b1* st))

         (br-full-in (f-and (car la1) (car lb1))))

      (list* br-full-in empty-out0- empty-out1-
             (append (append (v-threefix (strip-cars a1))
                             (v-threefix (strip-cars b1)))
                     br-go-signals))))

  ;; Extract the "in-act" signal

  (defund comp-gcd-cond$in-act (inputs st data-width)
    (b* ((full-in (nth 0 inputs))
         (go-signals (nthcdr (comp-gcd-cond$data-ins-len data-width) inputs))
         (go-in (nth 0 go-signals))
         (la0 (get-field *comp-gcd-cond$la0* st))
         (lb0 (get-field *comp-gcd-cond$lb0* st)))
      (joint-act full-in
                 (f-or (car la0) (car lb0))
                 go-in)))

  ;; Extract the "out-act0" signal

  (defund comp-gcd-cond$out-act0 (inputs st data-width)
    (gcd-cond$act0 (comp-gcd-cond$br-inputs inputs st data-width)
                   data-width))

  ;; Extract the "out-act1" signal

  (defund comp-gcd-cond$out-act1 (inputs st data-width)
    (gcd-cond$act1 (comp-gcd-cond$br-inputs inputs st data-width)
                   data-width))

  ;; Extract the "out-act" signal

  (defund comp-gcd-cond$out-act (inputs st data-width)
    (f-or (comp-gcd-cond$out-act0 inputs st data-width)
          (comp-gcd-cond$out-act1 inputs st data-width)))

  ;; Extract the "flag" signal

  (defund comp-gcd-cond$flag (inputs st data-width)
    (gcd-cond$flag (comp-gcd-cond$br-inputs inputs st data-width)
                   data-width))

  ;; Extract the 1st output data item

  (defund comp-gcd-cond$data-out0 (inputs st data-width)
    (gcd-cond$data-out0 (comp-gcd-cond$br-inputs inputs st data-width)
                        data-width))

  (defthm len-comp-gcd-cond$data-out0-1
    (implies (comp-gcd-cond$st-format st data-width)
             (equal (len (comp-gcd-cond$data-out0 inputs st data-width))
                    data-width))
    :hints (("Goal" :in-theory (enable comp-gcd-cond$st-format
                                       comp-gcd-cond$data-out0))))

  (defthm len-comp-gcd-cond$data-out0-2
    (implies (comp-gcd-cond$valid-st st data-width)
             (equal (len (comp-gcd-cond$data-out0 inputs st data-width))
                    data-width))
    :hints (("Goal" :in-theory (enable comp-gcd-cond$valid-st))))

  (defthm bvp-comp-gcd-cond$data-out0
    (implies (and (comp-gcd-cond$valid-st st data-width)
                  (comp-gcd-cond$out-act0 inputs st data-width))
             (bvp (comp-gcd-cond$data-out0 inputs st data-width)))
    :hints (("Goal" :in-theory (enable gcd-cond$act0
                                       gcd-cond$br-inputs
                                       gcd-cond$data-in
                                       branch$act0
                                       comp-gcd-cond$br-inputs
                                       comp-gcd-cond$valid-st
                                       comp-gcd-cond$st-format
                                       comp-gcd-cond$out-act0
                                       comp-gcd-cond$data-out0))))

  ;; Extract the 2nd output data item

  (defund comp-gcd-cond$data-out1 (inputs st data-width)
    (gcd-cond$data-out1 (comp-gcd-cond$br-inputs inputs st data-width)
                        data-width))

  (defthm len-comp-gcd-cond$data-out1-1
    (implies (comp-gcd-cond$st-format st data-width)
             (equal (len (comp-gcd-cond$data-out1 inputs st data-width))
                    (* 2 data-width)))
    :hints (("Goal" :in-theory (enable comp-gcd-cond$st-format
                                       comp-gcd-cond$data-out1))))

  (defthm len-comp-gcd-cond$data-out1-2
    (implies (comp-gcd-cond$valid-st st data-width)
             (equal (len (comp-gcd-cond$data-out1 inputs st data-width))
                    (* 2 data-width)))
    :hints (("Goal" :in-theory (enable comp-gcd-cond$valid-st))))

  (defthm bvp-comp-gcd-cond$data-out1
    (implies (and (comp-gcd-cond$valid-st st data-width)
                  (comp-gcd-cond$out-act1 inputs st data-width))
             (bvp (comp-gcd-cond$data-out1 inputs st data-width)))
    :hints (("Goal" :in-theory (enable gcd-cond$act1
                                       gcd-cond$br-inputs
                                       gcd-cond$data-in
                                       branch$act1
                                       comp-gcd-cond$br-inputs
                                       comp-gcd-cond$valid-st
                                       comp-gcd-cond$st-format
                                       comp-gcd-cond$out-act1
                                       comp-gcd-cond$data-out1))))

  ;; Extract the output data

  (defund comp-gcd-cond$data-outs (inputs st data-width)
    (cons (comp-gcd-cond$flag inputs st data-width)
          (append (comp-gcd-cond$data-out0 inputs st data-width)
                  (comp-gcd-cond$data-out1 inputs st data-width))))
  )

(not-primp-lemma comp-gcd-cond) ;; Prove that COMP-GCD-COND is not
                                ;; a DE primitive.

(encapsulate
  ()

  (local
   (defthm gcd-cond$value-alt
     (b* ((inputs (list* full-in empty-out0- empty-out1-
                         (append a b go-signals))))
       (implies
        (and (natp data-width)
             (<= 3 data-width)
             (gcd-cond& netlist data-width)
             (true-listp a)
             (equal (len a) data-width)
             (true-listp b)
             (equal (len b) data-width)
             (true-listp go-signals)
             (equal (len go-signals)
                    *gcd-cond$go-num*))
        (equal (se (si 'gcd-cond data-width) inputs st netlist)
               (list* (gcd-cond$act inputs data-width)
                      (gcd-cond$act0 inputs data-width)
                      (gcd-cond$act1 inputs data-width)
                      (gcd-cond$flag inputs data-width)
                      (append (gcd-cond$data-out0 inputs data-width)
                              (gcd-cond$data-out1 inputs data-width))))))
     :hints (("Goal"
              :use (:instance gcd-cond$value
                              (data-in (append a b)))))))

  ;; The value lemma for COMP-GCD-COND

  (defthmd comp-gcd-cond$value
    (b* ((inputs (list* full-in empty-out0- empty-out1-
                        (append data-in go-signals))))
      (implies
       (and (comp-gcd-cond& netlist data-width)
            (equal (len data-in) (* 2 data-width))
            (true-listp go-signals)
            (equal (len go-signals) *comp-gcd-cond$go-num*)
            (comp-gcd-cond$st-format st data-width))
       (equal (se (si 'comp-gcd-cond data-width) inputs st netlist)
              (list*
               (comp-gcd-cond$in-act inputs st data-width)
               (comp-gcd-cond$out-act inputs st data-width)
               (comp-gcd-cond$out-act0 inputs st data-width)
               (comp-gcd-cond$out-act1 inputs st data-width)
               (comp-gcd-cond$flag inputs st data-width)
               (append (comp-gcd-cond$data-out0 inputs st data-width)
                       (comp-gcd-cond$data-out1 inputs st data-width))))))
    :hints (("Goal"
             :do-not-induct t
             :do-not '(preprocess)
             :expand (se (si 'comp-gcd-cond data-width)
                         (list* full-in empty-out0- empty-out1-
                                (append data-in go-signals))
                         st
                         netlist)
             :in-theory (e/d (de-rules
                              nthcdr-of-pos-const-idx
                              not-primp-comp-gcd-cond
                              comp-gcd-cond&
                              comp-gcd-cond*$destructure
                              queue2$value
                              queue3$value
                              joint-cntl$value
                              latch-n$value
                              v-buf$value
                              gcd-cond$act
                              comp-gcd-cond$st-format
                              comp-gcd-cond$br-inputs
                              comp-gcd-cond$in-act
                              comp-gcd-cond$out-act
                              comp-gcd-cond$out-act0
                              comp-gcd-cond$out-act1
                              comp-gcd-cond$flag
                              comp-gcd-cond$data-out0
                              comp-gcd-cond$data-out1)
                             ((comp-gcd-cond*)
                              nfix
                              append
                              append-v-threefix
                              de-module-disabled-rules)))))

  ;; This function specifies the next state of COMP-GCD-COND.

  (defun comp-gcd-cond$step (inputs st data-width)
    (b* ((data-in (comp-gcd-cond$data-in inputs data-width))

         (la0 (get-field *comp-gcd-cond$la0* st))
         (a0  (get-field *comp-gcd-cond$a0* st))
         (lb0 (get-field *comp-gcd-cond$lb0* st))
         (b0  (get-field *comp-gcd-cond$b0* st))
         (la1 (get-field *comp-gcd-cond$la1* st))
         (a1  (get-field *comp-gcd-cond$a1* st))
         (lb1 (get-field *comp-gcd-cond$lb1* st))
         (b1  (get-field *comp-gcd-cond$b1* st))
         (q2  (get-field *comp-gcd-cond$q2* st))
         (q3  (get-field *comp-gcd-cond$q3* st))

         (q2-inputs (comp-gcd-cond$q2-inputs inputs st data-width))
         (q2-in-act (queue2$in-act q2-inputs q2 data-width))
         (q2-out-act (queue2$out-act q2-inputs q2 data-width))
         (q2-data-out (queue2$data-out q2))

         (q3-inputs (comp-gcd-cond$q3-inputs inputs st data-width))
         (q3-in-act (queue3$in-act q3-inputs q3 data-width))
         (q3-out-act (queue3$out-act q3-inputs q3 data-width))
         (q3-data-out (queue3$data-out q3))

         (in-act (comp-gcd-cond$in-act inputs st data-width))
         (out-act (comp-gcd-cond$out-act inputs st data-width)))

      (list
       ;; A0
       (list (f-sr in-act q2-in-act (car la0)))
       (pairlis$ (fv-if in-act (take data-width data-in) (strip-cars a0))
                 nil)

       ;; B0
       (list (f-sr in-act q3-in-act (car lb0)))
       (pairlis$ (fv-if in-act (nthcdr data-width data-in) (strip-cars b0))
                 nil)

       ;; A1
       (list (f-sr q2-out-act out-act (car la1)))
       (pairlis$ (fv-if q2-out-act q2-data-out (strip-cars a1))
                 nil)

       ;; B1
       (list (f-sr q3-out-act out-act (car lb1)))
       (pairlis$ (fv-if q3-out-act q3-data-out (strip-cars b1))
                 nil)

       ;; Joint Q2
       (queue2$step q2-inputs q2 data-width)
       ;; Joint Q3
       (queue3$step q3-inputs q3 data-width))))

  (defthm len-of-comp-gcd-cond$step
    (equal (len (comp-gcd-cond$step inputs st data-width))
           *comp-gcd-cond$st-len*))

  ;; The state lemma for COMP-GCD-COND

  (defthmd comp-gcd-cond$state
    (b* ((inputs (list* full-in empty-out0- empty-out1-
                        (append data-in go-signals))))
      (implies (and (comp-gcd-cond& netlist data-width)
                    (true-listp data-in)
                    (equal (len data-in) (* 2 data-width))
                    (true-listp go-signals)
                    (equal (len go-signals) *comp-gcd-cond$go-num*)
                    (comp-gcd-cond$st-format st data-width))
               (equal (de (si 'comp-gcd-cond data-width) inputs st netlist)
                      (comp-gcd-cond$step inputs st data-width))))
    :hints (("Goal"
             :do-not-induct t
             :do-not '(preprocess)
             :expand (de (si 'comp-gcd-cond data-width)
                         (list* full-in empty-out0- empty-out1-
                                (append data-in go-signals))
                         st
                         netlist)
             :in-theory (e/d (de-rules
                              nthcdr-of-pos-const-idx
                              not-primp-comp-gcd-cond
                              comp-gcd-cond&
                              comp-gcd-cond*$destructure
                              comp-gcd-cond$st-format
                              comp-gcd-cond$br-inputs
                              comp-gcd-cond$data-in
                              comp-gcd-cond$in-act
                              comp-gcd-cond$out-act
                              comp-gcd-cond$out-act0
                              comp-gcd-cond$out-act1
                              comp-gcd-cond$q2-inputs
                              comp-gcd-cond$q3-inputs
                              gcd-cond$act
                              queue2$value queue2$state
                              queue3$value queue3$state
                              joint-cntl$value
                              latch-n$value latch-n$state
                              v-buf$value)
                             ((comp-gcd-cond*)
                              nfix
                              append
                              append-v-threefix
                              de-module-disabled-rules)))))

  (in-theory (disable comp-gcd-cond$step))
  )

;; ======================================================================

;; 2. Specify the Final State of COMP-GCD-COND After An N-Step Execution

;; COMP-GCD-COND simulator

(progn
  (defun comp-gcd-cond$map-to-links (st)
    (b* ((la0 (get-field *comp-gcd-cond$la0* st))
         (a0  (get-field *comp-gcd-cond$a0* st))
         (lb0 (get-field *comp-gcd-cond$lb0* st))
         (b0  (get-field *comp-gcd-cond$b0* st))
         (la1 (get-field *comp-gcd-cond$la1* st))
         (a1  (get-field *comp-gcd-cond$a1* st))
         (lb1 (get-field *comp-gcd-cond$lb1* st))
         (b1  (get-field *comp-gcd-cond$b1* st))
         (q2  (get-field *comp-gcd-cond$q2* st))
         (q3  (get-field *comp-gcd-cond$q3* st)))
      (append (map-to-links (list (list 'a0 la0 a0)
                                  (list 'b0 lb0 b0)))
              (cons (cons 'Q2 (queue2$map-to-links q2))
                    (cons (cons 'Q3 (queue3$map-to-links q3))
                          (map-to-links (list (list 'a1 la1 a1)
                                              (list 'b1 lb1 b1))))))))

  (defun comp-gcd-cond$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (comp-gcd-cond$map-to-links (car x))
            (comp-gcd-cond$map-to-links-list (cdr x)))))

  (defund comp-gcd-cond$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd-cond$ins-len data-width))
         ((mv inputs-lst state)
          (signal-vals-gen num-signals n state nil))
         ;;(- (cw "~x0~%" inputs-lst))
         (empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (la0 empty)
         (a0 invalid-data)
         (lb0 empty)
         (b0 invalid-data)
         (la1 empty)
         (a1 invalid-data)
         (lb1 empty)
         (b1 invalid-data)
         (q2 (list empty invalid-data
                   empty invalid-data))
         (q3 (list empty invalid-data
                   empty invalid-data
                   empty invalid-data))
         (st (list la0 a0 lb0 b0 la1 a1 lb1 b1 q2 q3)))
      (mv (pretty-list
           (remove-dup-neighbors
            (comp-gcd-cond$map-to-links-list
             (de-sim-list (si 'comp-gcd-cond data-width)
                          inputs-lst
                          st
                          (comp-gcd-cond$netlist data-width))))
           0)
          state)))
  )

;; Conditions on the inputs

(defund comp-gcd-cond$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in     (nth 0 inputs))
       (empty-out0- (nth 1 inputs))
       (empty-out1- (nth 2 inputs))
       (data-in (comp-gcd-cond$data-in inputs data-width))
       (go-signals (nthcdr (comp-gcd-cond$data-ins-len data-width)
                           inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out0-)
     (booleanp empty-out1-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *comp-gcd-cond$go-num*)
     (equal inputs
            (list* full-in empty-out0- empty-out1-
                   (append data-in go-signals))))))

(local
 (defthm comp-gcd-cond$input-format=>q2$input-format
   (implies (and (comp-gcd-cond$input-format inputs data-width)
                 (comp-gcd-cond$valid-st st data-width))
            (queue2$input-format
             (comp-gcd-cond$q2-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (comp-gcd-cond$input-format
                             queue2$input-format
                             queue2$data-in
                             comp-gcd-cond$valid-st
                             comp-gcd-cond$st-format
                             comp-gcd-cond$q2-inputs)
                            (nthcdr
                             len
                             take-of-too-many))))))

(local
 (defthm comp-gcd-cond$input-format=>q3$input-format
   (implies (and (comp-gcd-cond$input-format inputs data-width)
                 (comp-gcd-cond$valid-st st data-width))
            (queue3$input-format
             (comp-gcd-cond$q3-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (comp-gcd-cond$input-format
                             queue3$input-format
                             queue3$data-in
                             comp-gcd-cond$valid-st
                             comp-gcd-cond$st-format
                             comp-gcd-cond$q3-inputs)
                            (nthcdr
                             len
                             take-of-too-many))))))

(simulate-lemma comp-gcd-cond)

;; ======================================================================

;; 3. Single-Step-Update Property

;; Specify the functionality of COMP-GCD-COND

(defund comp-gcd-cond$op (x)
  (append (car x) (cdr x)))

;; The operation of COMP-GCD-COND over a data sequence

(defun comp-gcd-cond$op-seq (seq)
  (if (atom seq)
      nil
    (cons (comp-gcd-cond$op (car seq))
          (comp-gcd-cond$op-seq (cdr seq)))))

(defthm len-of-comp-gcd-cond$op-seq
  (equal (len (comp-gcd-cond$op-seq x))
         (len x)))

(defthm comp-gcd-cond$op-seq-of-append
  (equal (comp-gcd-cond$op-seq (append x y))
         (append (comp-gcd-cond$op-seq x)
                 (comp-gcd-cond$op-seq y))))

;; The extraction function for COMP-GCD-COND that extracts the future output
;; sequence from the current state.

(defund comp-gcd-cond$extract (st)
  (b* ((la0 (get-field *comp-gcd-cond$la0* st))
       (a0  (get-field *comp-gcd-cond$a0* st))
       (lb0 (get-field *comp-gcd-cond$lb0* st))
       (b0  (get-field *comp-gcd-cond$b0* st))
       (la1 (get-field *comp-gcd-cond$la1* st))
       (a1  (get-field *comp-gcd-cond$a1* st))
       (lb1 (get-field *comp-gcd-cond$lb1* st))
       (b1  (get-field *comp-gcd-cond$b1* st))
       (q2  (get-field *comp-gcd-cond$q2* st))
       (q3  (get-field *comp-gcd-cond$q3* st))

       (a-seq (append (extract-valid-data (list la0 a0))
                      (queue2$extract q2)
                      (extract-valid-data (list la1 a1))))
       (b-seq (append (extract-valid-data (list lb0 b0))
                      (queue3$extract q3)
                      (extract-valid-data (list lb1 b1)))))
    (comp-gcd-cond$op-seq (pairlis$ a-seq b-seq))))

(defthm comp-gcd-cond$extract-not-empty
  (implies (and (comp-gcd-cond$out-act0 inputs st data-width)
                (comp-gcd-cond$valid-st st data-width))
           (< 0 (len (comp-gcd-cond$extract st))))
  :hints (("Goal"
           :in-theory (e/d (branch$act0
                            gcd-cond$br-inputs
                            gcd-cond$act0
                            comp-gcd-cond$br-inputs
                            comp-gcd-cond$out-act0
                            comp-gcd-cond$valid-st
                            comp-gcd-cond$extract)
                           (nfix))))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund comp-gcd-cond$inv (st)
    (b* ((la0 (get-field *comp-gcd-cond$la0* st))
         (a0  (get-field *comp-gcd-cond$a0* st))
         (lb0 (get-field *comp-gcd-cond$lb0* st))
         (b0  (get-field *comp-gcd-cond$b0* st))
         (la1 (get-field *comp-gcd-cond$la1* st))
         (a1  (get-field *comp-gcd-cond$a1* st))
         (lb1 (get-field *comp-gcd-cond$lb1* st))
         (b1  (get-field *comp-gcd-cond$b1* st))
         (q2  (get-field *comp-gcd-cond$q2* st))
         (q3  (get-field *comp-gcd-cond$q3* st))

         (a-seq (append (extract-valid-data (list la0 a0))
                        (queue2$extract q2)
                        (extract-valid-data (list la1 a1))))
         (b-seq (append (extract-valid-data (list lb0 b0))
                        (queue3$extract q3)
                        (extract-valid-data (list lb1 b1)))))
      (equal (len a-seq) (len b-seq))))

  (local
   (defthm booleanp-comp-gcd-cond$q2-in-act
     (implies (and (or (equal (nth *comp-gcd-cond$la0* st) '(t))
                       (equal (nth *comp-gcd-cond$la0* st) '(nil)))
                   (queue2$valid-st (nth *comp-gcd-cond$q2* st) data-width))
              (booleanp
               (queue2$in-act (comp-gcd-cond$q2-inputs inputs st data-width)
                              (nth *comp-gcd-cond$q2* st)
                              data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 comp-gcd-cond$q2-inputs
                                 queue2$valid-st
                                 queue2$in-act)))
     :rule-classes :type-prescription))

  (local
   (defthm booleanp-comp-gcd-cond$q3-in-act
     (implies (and (or (equal (nth *comp-gcd-cond$lb0* st) '(t))
                       (equal (nth *comp-gcd-cond$lb0* st) '(nil)))
                   (queue3$valid-st (nth *comp-gcd-cond$q3* st) data-width))
              (booleanp
               (queue3$in-act (comp-gcd-cond$q3-inputs inputs st data-width)
                              (nth *comp-gcd-cond$q3* st)
                              data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 comp-gcd-cond$q3-inputs
                                 queue3$valid-st
                                 queue3$in-act)))
     :rule-classes :type-prescription))

  (local
   (defthm comp-gcd-cond$q2-in-act-nil
     (implies (equal (nth *comp-gcd-cond$la0* st) '(nil))
              (not (queue2$in-act (comp-gcd-cond$q2-inputs
                                   inputs st data-width)
                                  (nth *comp-gcd-cond$q2* st)
                                  data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 comp-gcd-cond$q2-inputs
                                 queue2$in-act)))))

  (local
   (defthm comp-gcd-cond$q3-in-act-nil
     (implies (equal (nth *comp-gcd-cond$lb0* st) '(nil))
              (not (queue3$in-act (comp-gcd-cond$q3-inputs
                                   inputs st data-width)
                                  (nth *comp-gcd-cond$q3* st)
                                  data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 comp-gcd-cond$q3-inputs
                                 queue3$in-act)))))

  (local
   (defthm booleanp-comp-gcd-cond$q2-out-act
     (implies (and (or (equal (nth *comp-gcd-cond$la1* st) '(t))
                       (equal (nth *comp-gcd-cond$la1* st) '(nil)))
                   (queue2$valid-st (nth *comp-gcd-cond$q2* st) data-width))
              (booleanp
               (queue2$out-act (comp-gcd-cond$q2-inputs inputs st data-width)
                               (nth *comp-gcd-cond$q2* st)
                               data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 comp-gcd-cond$q2-inputs
                                 queue2$valid-st
                                 queue2$out-act)))
     :rule-classes :type-prescription))

  (local
   (defthm booleanp-comp-gcd-cond$q3-out-act
     (implies (and (or (equal (nth *comp-gcd-cond$lb1* st) '(t))
                       (equal (nth *comp-gcd-cond$lb1* st) '(nil)))
                   (queue3$valid-st (nth *comp-gcd-cond$q3* st) data-width))
              (booleanp
               (queue3$out-act (comp-gcd-cond$q3-inputs inputs st data-width)
                               (nth *comp-gcd-cond$q3* st)
                               data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 comp-gcd-cond$q3-inputs
                                 queue3$valid-st
                                 queue3$out-act)))
     :rule-classes :type-prescription))

  (local
   (defthm comp-gcd-cond$q2-out-act-nil
     (implies (equal (nth *comp-gcd-cond$la1* st) '(t))
              (not (queue2$out-act (comp-gcd-cond$q2-inputs
                                    inputs st data-width)
                                   (nth *comp-gcd-cond$q2* st)
                                   data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 comp-gcd-cond$q2-inputs
                                 queue2$out-act)))))

  (local
   (defthm comp-gcd-cond$q3-out-act-nil
     (implies (equal (nth *comp-gcd-cond$lb1* st) '(t))
              (not (queue3$out-act (comp-gcd-cond$q3-inputs
                                    inputs st data-width)
                                   (nth *comp-gcd-cond$q3* st)
                                   data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 comp-gcd-cond$q3-inputs
                                 queue3$out-act)))))

  (defthm comp-gcd-cond$inv-preserved
    (implies (and (comp-gcd-cond$input-format inputs data-width)
                  (comp-gcd-cond$valid-st st data-width)
                  (comp-gcd-cond$inv st))
             (comp-gcd-cond$inv
              (comp-gcd-cond$step inputs st data-width)))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              queue2$extracted-step
                              queue3$extracted-step
                              branch$act0
                              branch$act1
                              gcd-cond$act0
                              gcd-cond$act1
                              gcd-cond$flag
                              gcd-cond$data-in
                              gcd-cond$br-inputs
                              comp-gcd-cond$input-format
                              comp-gcd-cond$valid-st
                              comp-gcd-cond$st-format
                              comp-gcd-cond$inv
                              comp-gcd-cond$step
                              comp-gcd-cond$br-inputs
                              comp-gcd-cond$in-act
                              comp-gcd-cond$out-act
                              comp-gcd-cond$out-act0
                              comp-gcd-cond$out-act1
                              f-sr)
                             (if*
                              b-nor3
                              b-not
                              b-or
                              nfix
                              nthcdr
                              take-of-too-many
                              open-v-threefix)))))
  )

;; The extracted next-state function for COMP-GCD-COND.  Note that this
;; function avoids exploring the internal computation of COMP-GCD-COND.

(defund comp-gcd-cond$extracted-step (inputs st data-width)
  (b* ((a (take data-width (comp-gcd-cond$data-in inputs data-width)))
       (b (nthcdr data-width (comp-gcd-cond$data-in inputs data-width)))
       (data (comp-gcd-cond$op (cons a b)))
       (extracted-st (comp-gcd-cond$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-gcd-cond$out-act inputs st data-width) t)
      (cond
       ((equal (comp-gcd-cond$in-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (comp-gcd-cond$in-act inputs st data-width) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm comp-gcd-cond$q2-get-$data-in-rewrite
     (b* ((a0 (get-field *comp-gcd-cond$a0* st)))
       (implies (and (bvp (strip-cars a0))
                     (equal (len a0) data-width))
                (equal (queue2$data-in
                        (comp-gcd-cond$q2-inputs inputs st data-width)
                        data-width)
                       (strip-cars a0))))
     :hints (("Goal"
              :in-theory (enable queue2$data-in
                                 comp-gcd-cond$q2-inputs)))))

  (local
   (defthm comp-gcd-cond$q3-get-$data-in-rewrite
     (b* ((b0 (get-field *comp-gcd-cond$b0* st)))
       (implies (and (bvp (strip-cars b0))
                     (equal (len b0) data-width))
                (equal (queue3$data-in
                        (comp-gcd-cond$q3-inputs inputs st data-width)
                        data-width)
                       (strip-cars b0))))
     :hints (("Goal"
              :in-theory (enable queue3$data-in
                                 comp-gcd-cond$q3-inputs)))))

  (local
   (defthm car-queue3$extract-lemma
     (implies (and (<= (len (queue3$extract st))
                       1)
                   (queue3$valid-st st data-width)
                   (queue3$out-act inputs st data-width))
              (equal (car (queue3$extract st))
                     (queue3$data-out st)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue3$valid-st
                                 queue3$extract
                                 queue3$out-act
                                 queue3$data-out)))))

  (local
   (defthm comp-gcd-cond$extracted-step-correct-aux
     (and (equal (cons e (append (queue2$extract st)
                                 x))
                 (append (cons e (queue2$extract st))
                         x))
          (equal (cons e (append (queue3$extract st)
                                 x))
                 (append (cons e (queue3$extract st))
                         x)))))

  (defthm comp-gcd-cond$extracted-step-correct
    (b* ((next-st (comp-gcd-cond$step inputs st data-width)))
      (implies (and (comp-gcd-cond$input-format inputs data-width)
                    (comp-gcd-cond$valid-st st data-width)
                    (comp-gcd-cond$inv st))
               (equal (comp-gcd-cond$extract next-st)
                      (comp-gcd-cond$extracted-step inputs st data-width))))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              queue2$extracted-step
                              queue3$extracted-step
                              branch$act0
                              branch$act1
                              gcd-cond$act0
                              gcd-cond$act1
                              gcd-cond$flag
                              gcd-cond$data-in
                              gcd-cond$br-inputs
                              comp-gcd-cond$extracted-step
                              comp-gcd-cond$input-format
                              comp-gcd-cond$valid-st
                              comp-gcd-cond$st-format
                              comp-gcd-cond$inv
                              comp-gcd-cond$step
                              comp-gcd-cond$br-inputs
                              comp-gcd-cond$in-act
                              comp-gcd-cond$out-act
                              comp-gcd-cond$out-act0
                              comp-gcd-cond$out-act1
                              comp-gcd-cond$extract)
                             (nfix
                              b-nor3
                              b-not
                              b-or
                              take-redefinition
                              not
                              nthcdr
                              if*
                              strip-cars
                              default-car
                              default-cdr
                              acl2::append-of-cons)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Extract the accepted input sequence

(defun comp-gcd-cond$in-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (comp-gcd-cond$in-act inputs st data-width) t)
          (append (comp-gcd-cond$in-seq
                   (cdr inputs-lst)
                   (comp-gcd-cond$step inputs st data-width)
                   data-width
                   (1- n))
                  (list
                   (cons (take data-width
                               (comp-gcd-cond$data-in inputs data-width))
                         (nthcdr data-width
                                 (comp-gcd-cond$data-in inputs data-width)))))
        (comp-gcd-cond$in-seq (cdr inputs-lst)
                              (comp-gcd-cond$step inputs st data-width)
                              data-width
                              (1- n))))))

;; Extract the valid output sequence

(defun comp-gcd-cond$out-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (comp-gcd-cond$out-act inputs st data-width) t)
          (append (comp-gcd-cond$out-seq
                   (cdr inputs-lst)
                   (comp-gcd-cond$step inputs st data-width)
                   data-width
                   (1- n))
                  (list (comp-gcd-cond$data-out1 inputs st data-width)))
        (comp-gcd-cond$out-seq (cdr inputs-lst)
                               (comp-gcd-cond$step inputs st data-width)
                               data-width
                               (1- n))))))

;; Input-output sequence simulator

(progn
  (defun v-to-nat-2-lst (x)
    (declare (xargs :guard (alistp x)))
    (if (atom x)
        nil
      (cons (list (v-to-nat (caar x))
                  (v-to-nat (cdar x)))
            (v-to-nat-2-lst (cdr x)))))

  (defund comp-gcd-cond$in-out-seq-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd-cond$ins-len data-width))
         ((mv inputs-lst state)
          (signal-vals-gen num-signals n state nil))
         (empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (la0 empty)
         (a0 invalid-data)
         (lb0 empty)
         (b0 invalid-data)
         (la1 empty)
         (a1 invalid-data)
         (lb1 empty)
         (b1 invalid-data)
         (q2 (list empty invalid-data
                   empty invalid-data))
         (q3 (list empty invalid-data
                   empty invalid-data
                   empty invalid-data))
         (st (list la0 a0 lb0 b0 la1 a1 lb1 b1 q2 q3)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-2-lst
                     (comp-gcd-cond$in-seq inputs-lst st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (comp-gcd-cond$out-seq inputs-lst st data-width n)))))
       state)))
  )

;; Prove that comp-gcd-cond$valid-st is an invariant.

(defthm comp-gcd-cond$valid-st-preserved
  (implies (and (comp-gcd-cond$input-format inputs data-width)
                (comp-gcd-cond$valid-st st data-width))
           (comp-gcd-cond$valid-st (comp-gcd-cond$step inputs st data-width)
                                   data-width))
  :hints (("Goal"
           :use ((:instance
                  queue2$valid-st-preserved
                  (inputs (comp-gcd-cond$q2-inputs inputs st data-width))
                  (st (get-field *comp-gcd-cond$q2* st)))
                 (:instance
                  queue3$valid-st-preserved
                  (inputs (comp-gcd-cond$q3-inputs inputs st data-width))
                  (st (get-field *comp-gcd-cond$q3* st))))
           :in-theory (e/d (get-field
                            branch$act0
                            branch$act1
                            gcd-cond$act0
                            gcd-cond$act1
                            gcd-cond$flag
                            gcd-cond$data-in
                            gcd-cond$br-inputs
                            comp-gcd-cond$input-format
                            comp-gcd-cond$valid-st
                            comp-gcd-cond$st-format
                            comp-gcd-cond$step
                            comp-gcd-cond$br-inputs
                            comp-gcd-cond$in-act
                            comp-gcd-cond$out-act
                            comp-gcd-cond$out-act0
                            comp-gcd-cond$out-act1
                            f-sr)
                           (queue2$valid-st-preserved
                            queue3$valid-st-preserved
                            nfix
                            if*
                            b-not
                            b-or
                            b-nor3
                            nthcdr
                            take-of-too-many
                            open-v-threefix)))))

(encapsulate
  ()

  (local
   (defthm take-of-comp-gcd-cond$op-seq-of-pairlis$
     (implies (and (equal (len x) (len y))
                   (<= n (len x)))
              (equal (take n (comp-gcd-cond$op-seq (pairlis$ x y)))
                     (comp-gcd-cond$op-seq (pairlis$ (take n x)
                                                     (take n y)))))))

  (local
   (defthm take-of-comp-gcd-cond$op-seq-of-pairlis$-instance
     (implies
      (and (equal (len (append x1
                               (queue2$extract q2)
                               (list e1)))
                  (len (append x2
                               (queue3$extract q3)
                               (list e2))))
           (equal n (1- (len (append x1
                                     (queue2$extract q2)
                                     (list e1))))))
      (equal (take n (comp-gcd-cond$op-seq
                      (pairlis$
                       (append x1
                               (queue2$extract q2)
                               (list e1))
                       (append x2
                               (queue3$extract q3)
                               (list e2)))))
             (comp-gcd-cond$op-seq
              (pairlis$
               (append x1
                       (queue2$extract q2))
               (append x2
                       (queue3$extract q3))))))))

  (local
   (defthm append-of-comp-gcd-cond$op-seq-pairlis$-instance
     (implies (equal (len (append x (list e1)))
                     (len (append y (list e2))))
              (equal (append (comp-gcd-cond$op-seq (pairlis$ x y))
                             (list (comp-gcd-cond$op (cons e1 e2))))
                     (comp-gcd-cond$op-seq
                      (pairlis$ (append x (list e1))
                                (append y (list e2))))))))

  (local
   (defthm comp-gcd-cond$data-outs-rewrite
     (b* ((a1 (get-field *comp-gcd-cond$a1* st))
          (b1 (get-field *comp-gcd-cond$b1* st)))
       (implies (and (comp-gcd-cond$valid-st st data-width)
                     (comp-gcd-cond$out-act inputs st data-width))
                (equal (comp-gcd-cond$data-out1 inputs st data-width)
                       (comp-gcd-cond$op (cons (strip-cars a1)
                                               (strip-cars b1))))))
     :hints (("Goal" :in-theory (e/d (branch$act0
                                      branch$act1
                                      gcd-cond$data-in
                                      gcd-cond$br-inputs
                                      gcd-cond$act0
                                      gcd-cond$act1
                                      gcd-cond$flag
                                      gcd-cond$data-out0
                                      gcd-cond$data-out1
                                      comp-gcd-cond$valid-st
                                      comp-gcd-cond$st-format
                                      comp-gcd-cond$out-act
                                      comp-gcd-cond$out-act0
                                      comp-gcd-cond$out-act1
                                      comp-gcd-cond$br-inputs
                                      comp-gcd-cond$data-outs
                                      comp-gcd-cond$flag
                                      comp-gcd-cond$data-out0
                                      comp-gcd-cond$data-out1
                                      comp-gcd-cond$op)
                                     (nfix
                                      b-nor3
                                      b-not
                                      b-or
                                      take-redefinition
                                      not
                                      nthcdr
                                      len-nthcdr
                                      acl2::take-of-cons
                                      if*
                                      strip-cars))))))

  (defthm comp-gcd-cond$extract-lemma
    (implies
     (and (comp-gcd-cond$valid-st st data-width)
          (comp-gcd-cond$inv st)
          (equal n (1- (len (comp-gcd-cond$extract st))))
          (comp-gcd-cond$out-act inputs st data-width))
     (equal (append (take n (comp-gcd-cond$extract st))
                    (list (comp-gcd-cond$data-out1 inputs st data-width)))
            (comp-gcd-cond$extract st)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (branch$act0
                              branch$act1
                              gcd-cond$br-inputs
                              gcd-cond$act0
                              gcd-cond$act1
                              comp-gcd-cond$valid-st
                              comp-gcd-cond$st-format
                              comp-gcd-cond$inv
                              comp-gcd-cond$extract
                              comp-gcd-cond$br-inputs
                              comp-gcd-cond$out-act
                              comp-gcd-cond$out-act0
                              comp-gcd-cond$out-act1)
                             (pairlis$
                              append
                              acl2::append-of-cons
                              acl2::append-when-not-consp
                              pairlis$-append
                              acl2::len-of-append)))))
  )

(in-out-stream-lemma comp-gcd-cond :op t :inv t)

