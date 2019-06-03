;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "queue2")
(include-book "queue3")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of COMP-V-OR
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of COMP-V-OR
;;
;; Construct a DE module generator for COMP-V-OR using the link-joint model.
;; Prove the value and state lemmas for this module generator.  COMP-V-OR
;; computes the bitwise OR on the two input operands.

(defconst *comp-v-or$prim-go-num* 2)
(defconst *comp-v-or$go-num* (+ *comp-v-or$prim-go-num*
                                *queue2$go-num*
                                *queue3$go-num*))

(defun comp-v-or$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (* 2 (mbe :logic (nfix data-size)
                 :exec  data-size))))

(defun comp-v-or$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (comp-v-or$data-ins-len data-size)
     *comp-v-or$go-num*))

;; DE module generator of COMP-V-OR

(module-generator
 comp-v-or* (data-size)
 (si 'comp-v-or data-size)
 (list* 'full-in 'empty-out-
        (append (sis 'a 0 data-size)
                (sis 'b 0 data-size)
                (sis 'go 0 *comp-v-or$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-size))
 '(a0 b0 a1 b1 q2 q3)
 (list
  ;; LINKS
  ;; A0
  (list 'a0
        (list* 'a0-status (sis 'a0-out 0 data-size))
        (si 'link data-size)
        (list* 'in-act 'q2-in-act (sis 'a0-in 0 data-size)))

  ;; B0
  (list 'b0
        (list* 'b0-status (sis 'b0-out 0 data-size))
        (si 'link data-size)
        (list* 'in-act 'q3-in-act (sis 'b0-in 0 data-size)))

  ;; A1
  (list 'a1
        (list* 'a1-status (sis 'a1-out 0 data-size))
        (si 'link data-size)
        (list* 'q2-out-act 'out-act (sis 'q2-data-out 0 data-size)))

  ;; B1
  (list 'b1
        (list* 'b1-status (sis 'b1-out 0 data-size))
        (si 'link data-size)
        (list* 'q3-out-act 'out-act (sis 'q3-data-out 0 data-size)))

  ;; STATUS
  '(in-status (ready-in-) b-or (a0-status b0-status))
  '(out-status (ready-out) b-and (a1-status b1-status))

  ;; JOINTS
  ;; 2-link queue Q2
  (list 'q2
        (list* 'q2-in-act 'q2-out-act
               (sis 'q2-data-out 0 data-size))
        (si 'queue2 data-size)
        (list* 'a0-status 'a1-status
               (append (sis 'a0-out 0 data-size)
                       (sis 'go
                            *comp-v-or$prim-go-num*
                            *queue2$go-num*))))

  ;; 3-link queue Q3
  (list 'q3
        (list* 'q3-in-act 'q3-out-act
               (sis 'q3-data-out 0 data-size))
        (si 'queue3 data-size)
        (list* 'b0-status 'b1-status
               (append (sis 'b0-out 0 data-size)
                       (sis 'go
                            (+ *comp-v-or$prim-go-num*
                               *queue2$go-num*)
                            *queue3$go-num*))))

  ;; In
  (list 'in-cntl
        '(in-act)
        'joint-cntl
        (list 'full-in 'ready-in- (si 'go 0)))
  (list 'in-op0
        (sis 'a0-in 0 data-size)
        (si 'v-buf data-size)
        (sis 'a 0 data-size))
  (list 'in-op1
        (sis 'b0-in 0 data-size)
        (si 'v-buf data-size)
        (sis 'b 0 data-size))

  ;; Out
  (list 'out-cntl
        '(out-act)
        'joint-cntl
        (list 'ready-out 'empty-out- (si 'go 1)))
  (list 'out-op
        (sis 'data-out 0 data-size)
        (si 'v-or data-size)
        (append (sis 'a1-out 0 data-size)
                (sis 'b1-out 0 data-size))))

 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'comp-v-or '(a0 b0 a1 b1 q2 q3) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; COMP-V-OR.

(defund comp-v-or$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (comp-v-or* data-size)
        (union$ (queue2$netlist data-size)
                (queue3$netlist data-size)
                (v-or$netlist data-size)
                :test 'equal)))

;; Recognizer for COMP-V-OR

(defund comp-v-or& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'comp-v-or data-size) netlist)))
    (and (equal (assoc (si 'comp-v-or data-size) netlist)
                (comp-v-or* data-size))
         (link& subnetlist data-size)
         (joint-cntl& subnetlist)
         (v-buf& subnetlist data-size)
         (v-or& subnetlist data-size)
         (queue2& subnetlist data-size)
         (queue3& subnetlist data-size))))

;; Sanity check

(local
 (defthmd check-comp-v-or$netlist-64
   (and (net-syntax-okp (comp-v-or$netlist 64))
        (net-arity-okp (comp-v-or$netlist 64))
        (comp-v-or& (comp-v-or$netlist 64) 64))))

;; Constraints on the state of COMP-V-OR

(defund comp-v-or$st-format (st data-size)
  (b* ((a0 (nth *comp-v-or$a0* st))
       (b0 (nth *comp-v-or$b0* st))
       (a1 (nth *comp-v-or$a1* st))
       (b1 (nth *comp-v-or$b1* st))
       (q2 (nth *comp-v-or$q2* st))
       (q3 (nth *comp-v-or$q3* st)))
    (and (link$st-format a0 data-size)
         (link$st-format b0 data-size)
         (link$st-format a1 data-size)
         (link$st-format b1 data-size)

         (queue2$st-format q2 data-size)
         (queue3$st-format q3 data-size))))

(defthm comp-v-or$st-format=>constraint
  (implies (comp-v-or$st-format st data-size)
           (natp data-size))
  :hints (("Goal" :in-theory (enable comp-v-or$st-format)))
  :rule-classes :forward-chaining)

(defund comp-v-or$valid-st (st data-size)
  (b* ((a0 (nth *comp-v-or$a0* st))
       (b0 (nth *comp-v-or$b0* st))
       (a1 (nth *comp-v-or$a1* st))
       (b1 (nth *comp-v-or$b1* st))
       (q2 (nth *comp-v-or$q2* st))
       (q3 (nth *comp-v-or$q3* st)))
    (and (link$valid-st a0 data-size)
         (link$valid-st b0 data-size)
         (link$valid-st a1 data-size)
         (link$valid-st b1 data-size)

         (queue2$valid-st q2 data-size)
         (queue3$valid-st q3 data-size))))

(defthmd comp-v-or$valid-st=>constraint
  (implies (comp-v-or$valid-st st data-size)
           (natp data-size))
  :hints (("Goal" :in-theory (enable comp-v-or$valid-st)))
  :rule-classes :forward-chaining)

(defthmd comp-v-or$valid-st=>st-format
  (implies (comp-v-or$valid-st st data-size)
           (comp-v-or$st-format st data-size))
  :hints (("Goal" :in-theory (e/d (queue2$valid-st=>st-format
                                   queue3$valid-st=>st-format
                                   comp-v-or$st-format
                                   comp-v-or$valid-st)
                                  (link$st-format)))))

;; Extract the input and output signals for COMP-V-OR

(progn
  ;; Extract the input operand A

  (defun comp-v-or$a (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (mbe :logic (nfix data-size)
               :exec  data-size)
          (nthcdr 2 inputs)))

  (defthm len-comp-v-or$a
    (equal (len (comp-v-or$a inputs data-size))
           (nfix data-size)))

  (in-theory (disable comp-v-or$a))

  ;; Extract the input operand B

  (defun comp-v-or$b (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (b* ((size (mbe :logic (nfix data-size)
                     :exec  data-size)))
      (take size
            (nthcdr (+ 2 size) inputs))))

  (defthm len-comp-v-or$b
    (equal (len (comp-v-or$b inputs data-size))
           (nfix data-size)))

  (in-theory (disable comp-v-or$b))

  ;; Extract the inputs for joint Q2

  (defund comp-v-or$q2-inputs (inputs st data-size)
    (b* ((go-signals (nthcdr (comp-v-or$data-ins-len data-size) inputs))

         (q2-go-signals (take *queue2$go-num*
                              (nthcdr *comp-v-or$prim-go-num*
                                      go-signals)))

         (a0  (nth *comp-v-or$a0* st))
         (a0.s (nth *link$s* a0))
         (a0.d (nth *link$d* a0))
         (a1 (nth *comp-v-or$a1* st))
         (a1.s (nth *link$s* a1)))

      (list* (f-buf (car a0.s)) (f-buf (car a1.s))
             (append (v-threefix (strip-cars a0.d))
                     q2-go-signals))))

  ;; Extract the inputs for joint Q3

  (defund comp-v-or$q3-inputs (inputs st data-size)
    (b* ((go-signals (nthcdr (comp-v-or$data-ins-len data-size) inputs))

         (q3-go-signals (take *queue3$go-num*
                              (nthcdr (+ *comp-v-or$prim-go-num*
                                         *queue2$go-num*)
                                      go-signals)))

         (b0  (nth *comp-v-or$b0* st))
         (b0.s (nth *link$s* b0))
         (b0.d (nth *link$d* b0))
         (b1 (nth *comp-v-or$b1* st))
         (b1.s (nth *link$s* b1)))

      (list* (f-buf (car b0.s)) (f-buf (car b1.s))
             (append (v-threefix (strip-cars b0.d))
                     q3-go-signals))))

  ;; Extract the "in-act" signal

  (defund comp-v-or$in-act (inputs st data-size)
    (b* ((full-in (nth 0 inputs))
         (go-signals (nthcdr (comp-v-or$data-ins-len data-size) inputs))
         (go-in (nth 0 go-signals))
         (a0 (nth *comp-v-or$a0* st))
         (a0.s (nth *link$s* a0))
         (b0 (nth *comp-v-or$b0* st))
         (b0.s (nth *link$s* b0)))
      (joint-act full-in
                 (f-or (car a0.s) (car b0.s))
                 go-in)))

  (defthm comp-v-or$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (comp-v-or$in-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-v-or$in-act))))

  ;; Extract the "out-act" signal

  (defund comp-v-or$out-act (inputs st data-size)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (comp-v-or$data-ins-len data-size) inputs))
         (go-out (nth 1 go-signals))

         (a1 (nth *comp-v-or$a1* st))
         (a1.s (nth *link$s* a1))
         (b1 (nth *comp-v-or$b1* st))
         (b1.s (nth *link$s* b1)))
      (joint-act (f-and (car a1.s) (car b1.s))
                 empty-out-
                 go-out)))

  (defthm comp-v-or$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (comp-v-or$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-v-or$out-act))))

  ;; Extract the output data

  (defund comp-v-or$data-out (st)
    (fv-or (strip-cars (nth *link$d*
                                  (nth *comp-v-or$a1* st)))
           (strip-cars (nth *link$d*
                                  (nth *comp-v-or$b1* st)))))

  (defthm len-comp-v-or$data-out-1
    (implies (comp-v-or$st-format st data-size)
             (equal (len (comp-v-or$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable comp-v-or$st-format
                                       comp-v-or$data-out))))

  (defthm len-comp-v-or$data-out-2
    (implies (comp-v-or$valid-st st data-size)
             (equal (len (comp-v-or$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable comp-v-or$valid-st
                                       comp-v-or$data-out))))

  (defthm bvp-comp-v-or$data-out
    (implies (and (comp-v-or$valid-st st data-size)
                  (comp-v-or$out-act inputs st data-size))
             (bvp (comp-v-or$data-out st)))
    :hints (("Goal" :in-theory (enable comp-v-or$valid-st
                                       comp-v-or$st-format
                                       comp-v-or$out-act
                                       comp-v-or$data-out))))

  (defun comp-v-or$outputs (inputs st data-size)
    (list* (comp-v-or$in-act inputs st data-size)
           (comp-v-or$out-act inputs st data-size)
           (comp-v-or$data-out st)))
  )

;; The value lemma for COMP-V-OR

(defthm comp-v-or$value
  (b* ((inputs (list* full-in empty-out- (append a b go-signals))))
    (implies (and (comp-v-or& netlist data-size)
                  (equal (len a) data-size)
                  (equal (len b) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-v-or$go-num*)
                  (comp-v-or$st-format st data-size))
             (equal (se (si 'comp-v-or data-size) inputs st netlist)
                    (comp-v-or$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'comp-v-or data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            comp-v-or&
                            comp-v-or*$destructure
                            comp-v-or$st-format
                            comp-v-or$in-act
                            comp-v-or$out-act
                            comp-v-or$data-out)
                           (append
                            append-v-threefix
                            de-module-disabled-rules)))))

;; This function specifies the next state of COMP-V-OR.

(defun comp-v-or$step (inputs st data-size)
  (b* ((a (comp-v-or$a inputs data-size))
       (b (comp-v-or$b inputs data-size))

       (a0 (nth *comp-v-or$a0* st))
       (b0 (nth *comp-v-or$b0* st))
       (a1 (nth *comp-v-or$a1* st))
       (b1 (nth *comp-v-or$b1* st))
       (q2 (nth *comp-v-or$q2* st))
       (q3 (nth *comp-v-or$q3* st))

       (q2-inputs (comp-v-or$q2-inputs inputs st data-size))
       (q2-in-act (queue2$in-act q2-inputs q2 data-size))
       (q2-out-act (queue2$out-act q2-inputs q2 data-size))
       (q2-data-out (queue2$data-out q2))

       (q3-inputs (comp-v-or$q3-inputs inputs st data-size))
       (q3-in-act (queue3$in-act q3-inputs q3 data-size))
       (q3-out-act (queue3$out-act q3-inputs q3 data-size))
       (q3-data-out (queue3$data-out q3))

       (in-act (comp-v-or$in-act inputs st data-size))
       (out-act (comp-v-or$out-act inputs st data-size))

       (a0-inputs (list* in-act q2-in-act a))
       (b0-inputs (list* in-act q3-in-act b))
       (a1-inputs (list* q2-out-act out-act q2-data-out))
       (b1-inputs (list* q3-out-act out-act q3-data-out)))

    (list
     ;; A0
     (link$step a0-inputs a0 data-size)
     ;; B0
     (link$step b0-inputs b0 data-size)
     ;; A1
     (link$step a1-inputs a1 data-size)
     ;; B1
     (link$step b1-inputs b1 data-size)

     ;; Joint Q2
     (queue2$step q2-inputs q2 data-size)
     ;; Joint Q3
     (queue3$step q3-inputs q3 data-size))))

;; The state lemma for COMP-V-OR

(defthm comp-v-or$state
  (b* ((inputs (list* full-in empty-out- (append a b go-signals))))
    (implies (and (comp-v-or& netlist data-size)
                  (true-listp a)
                  (equal (len a) data-size)
                  (true-listp b)
                  (equal (len b) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-v-or$go-num*)
                  (comp-v-or$st-format st data-size))
             (equal (de (si 'comp-v-or data-size) inputs st netlist)
                    (comp-v-or$step inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'comp-v-or data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            comp-v-or&
                            comp-v-or*$destructure
                            comp-v-or$st-format
                            comp-v-or$a
                            comp-v-or$b
                            comp-v-or$in-act
                            comp-v-or$out-act
                            comp-v-or$q2-inputs
                            comp-v-or$q3-inputs)
                           (append
                            de-module-disabled-rules)))))

(in-theory (disable comp-v-or$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund comp-v-or$input-format (inputs data-size)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-size))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (a (comp-v-or$a inputs data-size))
       (b (comp-v-or$b inputs data-size))
       (go-signals (nthcdr (comp-v-or$data-ins-len data-size) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp a))
     (or (not full-in) (bvp b))
     (true-listp go-signals)
     (= (len go-signals) *comp-v-or$go-num*)
     (equal inputs
            (list* full-in empty-out- (append a b go-signals))))))

(local
 (defthm comp-v-or$input-format=>q2$input-format
   (implies (and (comp-v-or$input-format inputs data-size)
                 (comp-v-or$valid-st st data-size))
            (queue2$input-format
             (comp-v-or$q2-inputs inputs st data-size)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (comp-v-or$input-format
                             queue2$input-format
                             queue2$data-in
                             comp-v-or$valid-st
                             comp-v-or$q2-inputs)
                            (len
                             take-of-too-many))))))

(local
 (defthm comp-v-or$input-format=>q3$input-format
   (implies (and (comp-v-or$input-format inputs data-size)
                 (comp-v-or$valid-st st data-size))
            (queue3$input-format
             (comp-v-or$q3-inputs inputs st data-size)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (comp-v-or$input-format
                             queue3$input-format
                             queue3$data-in
                             comp-v-or$valid-st
                             comp-v-or$q3-inputs)
                            (len
                             take-of-too-many))))))

(defthm booleanp-comp-v-or$in-act
  (implies (and (comp-v-or$input-format inputs data-size)
                (comp-v-or$valid-st st data-size))
           (booleanp (comp-v-or$in-act inputs st data-size)))
  :hints (("Goal" :in-theory (enable comp-v-or$input-format
                                     comp-v-or$valid-st
                                     comp-v-or$in-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-v-or$out-act
  (implies (and (comp-v-or$input-format inputs data-size)
                (comp-v-or$valid-st st data-size))
           (booleanp (comp-v-or$out-act inputs st data-size)))
  :hints (("Goal" :in-theory (enable comp-v-or$input-format
                                     comp-v-or$valid-st
                                     comp-v-or$out-act)))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma comp-v-or)

;; ======================================================================

;; 3. Single-Step-Update Property

;; Specify the functionality of COMP-V-OR over a data sequence

(defun comp-v-or$op-map (x)
  (if (atom x)
      nil
    (cons (v-or (caar x) (cdar x))
          (comp-v-or$op-map (cdr x)))))

(defthm len-of-comp-v-or$op-map
  (equal (len (comp-v-or$op-map x))
         (len x)))

(defthm comp-v-or$op-map-of-append
  (equal (comp-v-or$op-map (append x y))
         (append (comp-v-or$op-map x) (comp-v-or$op-map y))))

;; The extraction function for COMP-V-OR that extracts the future output
;; sequence from the current state.

(defund comp-v-or$extract (st)
  (b* ((a0 (nth *comp-v-or$a0* st))
       (b0 (nth *comp-v-or$b0* st))
       (a1 (nth *comp-v-or$a1* st))
       (b1 (nth *comp-v-or$b1* st))
       (q2 (nth *comp-v-or$q2* st))
       (q3 (nth *comp-v-or$q3* st))

       (a-seq (append (extract-valid-data (list a0))
                      (queue2$extract q2)
                      (extract-valid-data (list a1))))
       (b-seq (append (extract-valid-data (list b0))
                      (queue3$extract q3)
                      (extract-valid-data (list b1)))))
    (comp-v-or$op-map (pairlis$ a-seq b-seq))))

(defthm comp-v-or$extract-not-empty
  (implies (and (comp-v-or$out-act inputs st data-size)
                (comp-v-or$valid-st st data-size))
           (< 0 (len (comp-v-or$extract st))))
  :hints (("Goal"
           :in-theory (e/d (comp-v-or$valid-st
                            comp-v-or$extract
                            comp-v-or$out-act)
                           ())))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund comp-v-or$inv (st)
    (b* ((a0 (nth *comp-v-or$a0* st))
         (b0 (nth *comp-v-or$b0* st))
         (a1 (nth *comp-v-or$a1* st))
         (b1 (nth *comp-v-or$b1* st))
         (q2 (nth *comp-v-or$q2* st))
         (q3 (nth *comp-v-or$q3* st))

         (a-seq (append (extract-valid-data (list a0 a1))
                        (queue2$extract q2)))
         (b-seq (append (extract-valid-data (list b0 b1))
                        (queue3$extract q3))))
      (equal (len a-seq) (len b-seq))))

  (local
   (defthm comp-v-or$q2-in-act-inactive
     (implies (equal (nth *link$s* (nth *comp-v-or$a0* st))
                     '(nil))
              (not (queue2$in-act (comp-v-or$q2-inputs inputs st data-size)
                                  (nth *comp-v-or$q2* st)
                                  data-size)))
     :hints (("Goal"
              :in-theory (enable comp-v-or$q2-inputs)))))

  (local
   (defthm comp-v-or$q3-in-act-inactive
     (implies (equal (nth *link$s* (nth *comp-v-or$b0* st))
                     '(nil))
              (not (queue3$in-act (comp-v-or$q3-inputs inputs st data-size)
                                  (nth *comp-v-or$q3* st)
                                  data-size)))
     :hints (("Goal"
              :in-theory (enable comp-v-or$q3-inputs)))))

  (local
   (defthm comp-v-or$q2-out-act-inactive
     (implies (equal (nth *link$s* (nth *comp-v-or$a1* st))
                     '(t))
              (not (queue2$out-act (comp-v-or$q2-inputs inputs st data-size)
                                   (nth *comp-v-or$q2* st)
                                   data-size)))
     :hints (("Goal"
              :in-theory (enable comp-v-or$q2-inputs)))))

  (local
   (defthm comp-v-or$q3-out-act-inactive
     (implies (equal (nth *link$s* (nth *comp-v-or$b1* st))
                     '(t))
              (not (queue3$out-act (comp-v-or$q3-inputs inputs st data-size)
                                   (nth *comp-v-or$q3* st)
                                   data-size)))
     :hints (("Goal"
              :in-theory (enable comp-v-or$q3-inputs)))))

  (defthm comp-v-or$inv-preserved
    (implies (and (comp-v-or$input-format inputs data-size)
                  (comp-v-or$valid-st st data-size)
                  (comp-v-or$inv st))
             (comp-v-or$inv (comp-v-or$step inputs st data-size)))
    :hints (("Goal"
             :use (comp-v-or$input-format=>q2$input-format
                   comp-v-or$input-format=>q3$input-format)
             :in-theory (e/d (f-sr
                              queue2$extracted-step
                              queue3$extracted-step
                              comp-v-or$valid-st
                              comp-v-or$inv
                              comp-v-or$step
                              comp-v-or$in-act
                              comp-v-or$out-act)
                             (comp-v-or$input-format=>q2$input-format
                              comp-v-or$input-format=>q3$input-format)))))
  )

;; The extracted next-state function for COMP-V-OR.  Note that this function
;; avoids exploring the internal computation of COMP-V-OR.

(defund comp-v-or$extracted-step (inputs st data-size)
  (b* ((a (comp-v-or$a inputs data-size))
       (b (comp-v-or$b inputs data-size))
       (data (v-or a b))
       (extracted-st (comp-v-or$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-v-or$out-act inputs st data-size) t)
      (cond
       ((equal (comp-v-or$in-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (comp-v-or$in-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(local
 (defthm comp-v-or$input-format-lemma-1
   (implies (comp-v-or$input-format inputs data-size)
            (booleanp (nth 0 inputs)))
   :hints (("Goal" :in-theory (enable comp-v-or$input-format)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm comp-v-or$input-format-lemma-2
   (implies (comp-v-or$input-format inputs data-size)
            (booleanp (nth 1 inputs)))
   :hints (("Goal" :in-theory (enable comp-v-or$input-format)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm comp-v-or$input-format-lemma-3
   (implies (and (comp-v-or$input-format inputs data-size)
                 (nth 0 inputs))
            (and (bvp (comp-v-or$a inputs data-size))
                 (bvp (comp-v-or$b inputs data-size))))
   :hints (("Goal" :in-theory (enable comp-v-or$input-format)))))

(encapsulate
  ()

  (local
   (defthm comp-v-or$q2-data-in-rewrite
     (b* ((a0 (nth *comp-v-or$a0* st))
          (a0.d (nth *link$d* a0)))
       (implies (and (bvp (strip-cars a0.d))
                     (equal (len a0.d) data-size))
                (equal (queue2$data-in
                        (comp-v-or$q2-inputs inputs st data-size)
                        data-size)
                       (strip-cars a0.d))))
     :hints (("Goal"
              :in-theory (enable queue2$data-in
                                 comp-v-or$q2-inputs)))))

  (local
   (defthm comp-v-or$q3-data-in-rewrite
     (b* ((b0 (nth *comp-v-or$b0* st))
          (b0.d (nth *link$d* b0)))
       (implies (and (bvp (strip-cars b0.d))
                     (equal (len b0.d) data-size))
                (equal (queue3$data-in
                        (comp-v-or$q3-inputs inputs st data-size)
                        data-size)
                       (strip-cars b0.d))))
     :hints (("Goal"
              :in-theory (enable queue3$data-in
                                 comp-v-or$q3-inputs)))))

  (local
   (defthm comp-v-or$extracted-step-correct-aux
     (and (equal (cons e (append (queue2$extract st)
                                 x))
                 (append (cons e (queue2$extract st))
                         x))
          (equal (cons e (append (queue3$extract st)
                                 x))
                 (append (cons e (queue3$extract st))
                         x)))))

  (defthm comp-v-or$extracted-step-correct
    (b* ((next-st (comp-v-or$step inputs st data-size)))
      (implies (and (comp-v-or$input-format inputs data-size)
                    (comp-v-or$valid-st st data-size)
                    (comp-v-or$inv st))
               (equal (comp-v-or$extract next-st)
                      (comp-v-or$extracted-step inputs st data-size))))
    :hints (("Goal"
             :use (comp-v-or$input-format=>q2$input-format
                   comp-v-or$input-format=>q3$input-format)
             :in-theory (e/d (f-sr
                              queue2$extracted-step
                              queue3$extracted-step
                              comp-v-or$extracted-step
                              comp-v-or$valid-st
                              comp-v-or$inv
                              comp-v-or$step
                              comp-v-or$in-act
                              comp-v-or$out-act
                              comp-v-or$extract)
                             (comp-v-or$input-format=>q2$input-format
                              comp-v-or$input-format=>q3$input-format
                              strip-cars
                              acl2::append-of-cons)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that comp-v-or$valid-st is an invariant.

(defthm comp-v-or$valid-st-preserved
  (implies (and (comp-v-or$input-format inputs data-size)
                (comp-v-or$valid-st st data-size))
           (comp-v-or$valid-st (comp-v-or$step inputs st data-size)
                               data-size))
  :hints (("Goal"
           :use (comp-v-or$input-format=>q2$input-format
                 comp-v-or$input-format=>q3$input-format)
           :in-theory (e/d (f-sr
                            joint-act
                            comp-v-or$valid-st
                            comp-v-or$step
                            comp-v-or$in-act
                            comp-v-or$out-act)
                           (comp-v-or$input-format=>q2$input-format
                            comp-v-or$input-format=>q3$input-format)))))

(defthm comp-v-or$extract-lemma
  (implies (and (comp-v-or$valid-st st data-size)
                (comp-v-or$inv st)
                (comp-v-or$out-act inputs st data-size))
           (equal (list (comp-v-or$data-out st))
                  (nthcdr (1- (len (comp-v-or$extract st)))
                          (comp-v-or$extract st))))
  :hints (("Goal"
           :in-theory (e/d (left-associativity-of-append
                            comp-v-or$valid-st
                            comp-v-or$inv
                            comp-v-or$extract
                            comp-v-or$out-act
                            comp-v-or$data-out)
                           (acl2::append-of-cons
                            associativity-of-append
                            append)))))

;; Extract the accepted input sequence

(seq-gen comp-v-or in in-act 0
         (cons (comp-v-or$a inputs data-size)
               (comp-v-or$b inputs data-size)))

;; Extract the valid output sequence

(seq-gen comp-v-or out out-act 1
         (comp-v-or$data-out st)
         :netlist-data (nthcdr 2 outputs))

;; The multi-step input-output relationship

(in-out-stream-lemma comp-v-or :op comp-v-or$op :inv t)
