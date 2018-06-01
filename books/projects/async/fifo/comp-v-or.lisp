;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; April 2018

(in-package "ADE")

(include-book "queue2")
(include-book "queue3")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of COMP-V-OR
;;; 2. Specify the Final State of COMP-V-OR After An N-Step Execution
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
(defconst *comp-v-or$st-len* 6)

(defun comp-v-or$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun comp-v-or$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (comp-v-or$data-ins-len data-width)
     *comp-v-or$go-num*))

;; DE module generator of COMP-V-OR

(module-generator
 comp-v-or* (data-width)
 (si 'comp-v-or data-width)
 (list* 'full-in 'empty-out-
        (append (sis 'a 0 data-width)
                (sis 'b 0 data-width)
                (sis 'go 0 *comp-v-or$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-width))
 '(a0 b0 a1 b1 q2 q3)
 (list
  ;; LINKS
  ;; A0
  (list 'a0
        (list* 'a0-status (sis 'a0-out 0 data-width))
        (si 'link data-width)
        (list* 'in-act 'q2-in-act (sis 'a0-in 0 data-width)))

  ;; B0
  (list 'b0
        (list* 'b0-status (sis 'b0-out 0 data-width))
        (si 'link data-width)
        (list* 'in-act 'q3-in-act (sis 'b0-in 0 data-width)))

  ;; A1
  (list 'a1
        (list* 'a1-status (sis 'a1-out 0 data-width))
        (si 'link data-width)
        (list* 'q2-out-act 'out-act (sis 'q2-data-out 0 data-width)))

  ;; B1
  (list 'b1
        (list* 'b1-status (sis 'b1-out 0 data-width))
        (si 'link data-width)
        (list* 'q3-out-act 'out-act (sis 'q3-data-out 0 data-width)))

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
                            *comp-v-or$prim-go-num*
                            *queue2$go-num*))))

  ;; 3-link queue Q3
  (list 'q3
        (list* 'q3-in-act 'q3-out-act
               (sis 'q3-data-out 0 data-width))
        (si 'queue3 data-width)
        (list* 'b0-status 'b1-status
               (append (sis 'b0-out 0 data-width)
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
        (sis 'a0-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'a 0 data-width))
  (list 'in-op1
        (sis 'b0-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'b 0 data-width))

  ;; Out
  (list 'out-cntl
        '(out-act)
        'joint-cntl
        (list 'ready-out 'empty-out- (si 'go 1)))
  (list 'out-op
        (sis 'data-out 0 data-width)
        (si 'v-or data-width)
        (append (sis 'a1-out 0 data-width)
                (sis 'b1-out 0 data-width))))

 :guard (natp data-width))

(make-event
 `(progn
    ,@(state-accessors-gen 'comp-v-or '(a0 b0 a1 b1 q2 q3) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; COMP-V-OR.

(defun comp-v-or$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (comp-v-or* data-width)
        (union$ (queue2$netlist data-width)
                (queue3$netlist data-width)
                (v-or$netlist data-width)
                :test 'equal)))

;; Recognizer for COMP-V-OR

(defund comp-v-or& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (and (equal (assoc (si 'comp-v-or data-width) netlist)
              (comp-v-or* data-width))
       (b* ((netlist (delete-to-eq (si 'comp-v-or data-width) netlist)))
         (and (link& netlist data-width)
              (joint-cntl& netlist)
              (v-buf& netlist data-width)
              (v-or& netlist data-width)
              (queue2& netlist data-width)
              (queue3& netlist data-width)))))

;; Sanity check

(local
 (defthmd check-comp-v-or$netlist-64
   (and (net-syntax-okp (comp-v-or$netlist 64))
        (net-arity-okp (comp-v-or$netlist 64))
        (comp-v-or& (comp-v-or$netlist 64) 64))))

;; Constraints on the state of COMP-V-OR

(defund comp-v-or$st-format (st data-width)
  (b* ((a0 (get-field *comp-v-or$a0* st))
       (b0 (get-field *comp-v-or$b0* st))
       (a1 (get-field *comp-v-or$a1* st))
       (b1 (get-field *comp-v-or$b1* st))
       (q2 (get-field *comp-v-or$q2* st))
       (q3 (get-field *comp-v-or$q3* st)))
    (and (link$st-format a0 data-width)
         (link$st-format b0 data-width)
         (link$st-format a1 data-width)
         (link$st-format b1 data-width)

         (queue2$st-format q2 data-width)
         (queue3$st-format q3 data-width))))

(defthm comp-v-or$st-format=>natp-data-width
  (implies (comp-v-or$st-format st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable comp-v-or$st-format)))
  :rule-classes :forward-chaining)

(defund comp-v-or$valid-st (st data-width)
  (b* ((a0 (get-field *comp-v-or$a0* st))
       (b0 (get-field *comp-v-or$b0* st))
       (a1 (get-field *comp-v-or$a1* st))
       (b1 (get-field *comp-v-or$b1* st))
       (q2 (get-field *comp-v-or$q2* st))
       (q3 (get-field *comp-v-or$q3* st)))
    (and (link$valid-st a0 data-width)
         (link$valid-st b0 data-width)
         (link$valid-st a1 data-width)
         (link$valid-st b1 data-width)

         (queue2$valid-st q2 data-width)
         (queue3$valid-st q3 data-width))))

(defthmd comp-v-or$valid-st=>natp-data-width
  (implies (comp-v-or$valid-st st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable comp-v-or$valid-st)))
  :rule-classes :forward-chaining)

;; Extract the input and output signals from COMP-V-OR

(progn
  ;; Extract the input operand A

  (defun comp-v-or$a (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 2 inputs)))

  (defthm len-comp-v-or$a
    (equal (len (comp-v-or$a inputs data-width))
           (nfix data-width)))

  (in-theory (disable comp-v-or$a))

  ;; Extract the input operand B

  (defun comp-v-or$b (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (b* ((width (mbe :logic (nfix data-width)
                     :exec  data-width)))
      (take width
            (nthcdr (+ 2 width) inputs))))

  (defthm len-comp-v-or$b
    (equal (len (comp-v-or$b inputs data-width))
           (nfix data-width)))

  (in-theory (disable comp-v-or$b))

  ;; Extract the inputs for the Q2 joint

  (defund comp-v-or$q2-inputs (inputs st data-width)
    (b* ((go-signals (nthcdr (comp-v-or$data-ins-len data-width) inputs))

         (q2-go-signals (take *queue2$go-num*
                              (nthcdr *comp-v-or$prim-go-num*
                                      go-signals)))

         (a0  (get-field *comp-v-or$a0* st))
         (a0.s (get-field *link$s* a0))
         (a0.d (get-field *link$d* a0))
         (a1 (get-field *comp-v-or$a1* st))
         (a1.s (get-field *link$s* a1)))

      (list* (f-buf (car a0.s)) (f-buf (car a1.s))
             (append (v-threefix (strip-cars a0.d))
                     q2-go-signals))))

  ;; Extract the inputs for the Q3 joint

  (defund comp-v-or$q3-inputs (inputs st data-width)
    (b* ((go-signals (nthcdr (comp-v-or$data-ins-len data-width) inputs))

         (q3-go-signals (take *queue3$go-num*
                              (nthcdr (+ *comp-v-or$prim-go-num*
                                         *queue2$go-num*)
                                      go-signals)))

         (b0  (get-field *comp-v-or$b0* st))
         (b0.s (get-field *link$s* b0))
         (b0.d (get-field *link$d* b0))
         (b1 (get-field *comp-v-or$b1* st))
         (b1.s (get-field *link$s* b1)))

      (list* (f-buf (car b0.s)) (f-buf (car b1.s))
             (append (v-threefix (strip-cars b0.d))
                     q3-go-signals))))

  ;; Extract the "in-act" signal

  (defund comp-v-or$in-act (inputs st data-width)
    (b* ((full-in (nth 0 inputs))
         (go-signals (nthcdr (comp-v-or$data-ins-len data-width) inputs))
         (go-in (nth 0 go-signals))
         (a0 (get-field *comp-v-or$a0* st))
         (a0.s (get-field *link$s* a0))
         (b0 (get-field *comp-v-or$b0* st))
         (b0.s (get-field *link$s* b0)))
      (joint-act full-in
                 (f-or (car a0.s) (car b0.s))
                 go-in)))

  ;; Extract the "out-act" signal

  (defund comp-v-or$out-act (inputs st data-width)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (comp-v-or$data-ins-len data-width) inputs))
         (go-out (nth 1 go-signals))

         (a1 (get-field *comp-v-or$a1* st))
         (a1.s (get-field *link$s* a1))
         (b1 (get-field *comp-v-or$b1* st))
         (b1.s (get-field *link$s* b1)))
      (joint-act (f-and (car a1.s) (car b1.s))
                 empty-out-
                 go-out)))

  ;; Extract the output data

  (defund comp-v-or$data-out (st)
    (fv-or (strip-cars (get-field *link$d*
                                  (get-field *comp-v-or$a1* st)))
           (strip-cars (get-field *link$d*
                                  (get-field *comp-v-or$b1* st)))))

  (defthm len-comp-v-or$data-out-1
    (implies (comp-v-or$st-format st data-width)
             (equal (len (comp-v-or$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable comp-v-or$st-format
                                       comp-v-or$data-out))))

  (defthm len-comp-v-or$data-out-2
    (implies (comp-v-or$valid-st st data-width)
             (equal (len (comp-v-or$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable comp-v-or$valid-st
                                       comp-v-or$data-out))))

  (defthm bvp-comp-v-or$data-out
    (implies (and (comp-v-or$valid-st st data-width)
                  (comp-v-or$out-act inputs st data-width))
             (bvp (comp-v-or$data-out st)))
    :hints (("Goal" :in-theory (enable comp-v-or$valid-st
                                       comp-v-or$st-format
                                       comp-v-or$out-act
                                       comp-v-or$data-out))))
  )

(not-primp-lemma comp-v-or) ;; Prove that COMP-V-OR is not a DE primitive.

;; The value lemma for COMP-V-OR

(defthmd comp-v-or$value
  (b* ((inputs (list* full-in empty-out- (append a b go-signals))))
    (implies (and (comp-v-or& netlist data-width)
                  (equal (len a) data-width)
                  (equal (len b) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-v-or$go-num*)
                  (comp-v-or$st-format st data-width))
             (equal (se (si 'comp-v-or data-width) inputs st netlist)
                    (list* (comp-v-or$in-act inputs st data-width)
                           (comp-v-or$out-act inputs st data-width)
                           (comp-v-or$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'comp-v-or data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            not-primp-comp-v-or
                            comp-v-or&
                            comp-v-or*$destructure
                            queue2$value
                            queue3$value
                            link$value
                            joint-cntl$value
                            v-buf$value
                            v-or$value
                            comp-v-or$st-format
                            comp-v-or$in-act
                            comp-v-or$out-act
                            comp-v-or$data-out)
                           ((comp-v-or*)
                            append
                            append-v-threefix
                            de-module-disabled-rules)))))

;; This function specifies the next state of COMP-V-OR.

(defun comp-v-or$step (inputs st data-width)
  (b* ((a (comp-v-or$a inputs data-width))
       (b (comp-v-or$b inputs data-width))

       (a0 (get-field *comp-v-or$a0* st))
       (b0 (get-field *comp-v-or$b0* st))
       (a1 (get-field *comp-v-or$a1* st))
       (b1 (get-field *comp-v-or$b1* st))
       (q2 (get-field *comp-v-or$q2* st))
       (q3 (get-field *comp-v-or$q3* st))

       (q2-inputs (comp-v-or$q2-inputs inputs st data-width))
       (q2-in-act (queue2$in-act q2-inputs q2 data-width))
       (q2-out-act (queue2$out-act q2-inputs q2 data-width))
       (q2-data-out (queue2$data-out q2))

       (q3-inputs (comp-v-or$q3-inputs inputs st data-width))
       (q3-in-act (queue3$in-act q3-inputs q3 data-width))
       (q3-out-act (queue3$out-act q3-inputs q3 data-width))
       (q3-data-out (queue3$data-out q3))

       (in-act (comp-v-or$in-act inputs st data-width))
       (out-act (comp-v-or$out-act inputs st data-width))

       (a0-inputs (list* in-act q2-in-act a))
       (b0-inputs (list* in-act q3-in-act b))
       (a1-inputs (list* q2-out-act out-act q2-data-out))
       (b1-inputs (list* q3-out-act out-act q3-data-out)))

    (list
     ;; A0
     (link$step a0-inputs a0 data-width)
     ;; B0
     (link$step b0-inputs b0 data-width)
     ;; A1
     (link$step a1-inputs a1 data-width)
     ;; B1
     (link$step b1-inputs b1 data-width)

     ;; Joint Q2
     (queue2$step q2-inputs q2 data-width)
     ;; Joint Q3
     (queue3$step q3-inputs q3 data-width))))

(defthm len-of-comp-v-or$step
  (equal (len (comp-v-or$step inputs st data-width))
         *comp-v-or$st-len*))

;; The state lemma for COMP-V-OR

(defthmd comp-v-or$state
  (b* ((inputs (list* full-in empty-out- (append a b go-signals))))
    (implies (and (comp-v-or& netlist data-width)
                  (true-listp a)
                  (equal (len a) data-width)
                  (true-listp b)
                  (equal (len b) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-v-or$go-num*)
                  (comp-v-or$st-format st data-width))
             (equal (de (si 'comp-v-or data-width) inputs st netlist)
                    (comp-v-or$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'comp-v-or data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            not-primp-comp-v-or
                            comp-v-or&
                            comp-v-or*$destructure
                            comp-v-or$st-format
                            comp-v-or$a
                            comp-v-or$b
                            comp-v-or$in-act
                            comp-v-or$out-act
                            comp-v-or$q2-inputs
                            comp-v-or$q3-inputs
                            queue2$value queue2$state
                            queue3$value queue3$state
                            link$value link$state
                            joint-cntl$value
                            v-buf$value
                            v-or$value)
                           ((comp-v-or*)
                            append
                            de-module-disabled-rules)))))

(in-theory (disable comp-v-or$step))

;; ======================================================================

;; 2. Specify the Final State of COMP-V-OR After An N-Step Execution

;; COMP-V-OR simulator

(progn
  (defun comp-v-or$map-to-links (st)
    (b* ((a0 (get-field *comp-v-or$a0* st))
         (b0 (get-field *comp-v-or$b0* st))
         (a1 (get-field *comp-v-or$a1* st))
         (b1 (get-field *comp-v-or$b1* st))
         (q2 (get-field *comp-v-or$q2* st))
         (q3 (get-field *comp-v-or$q3* st)))
      (append (map-to-links (list (list* 'a0 a0)
                                  (list* 'b0 b0)))
              (cons (cons 'Q2 (queue2$map-to-links q2))
                    (cons (cons 'Q3 (queue3$map-to-links q3))
                          (map-to-links (list (list* 'a1 a1)
                                              (list* 'b1 b1))))))))

  (defun comp-v-or$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (comp-v-or$map-to-links (car x))
            (comp-v-or$map-to-links-list (cdr x)))))

  (defund comp-v-or$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-v-or$ins-len data-width))
         ((mv inputs-lst state)
          (signal-vals-gen num-signals n state nil))
         ;;(- (cw "~x0~%" inputs-lst))
         (empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (q2 (list (list empty invalid-data)
                   (list empty invalid-data)))
         (q3 (list (list empty invalid-data)
                   (list empty invalid-data)
                   (list empty invalid-data)))
         (st (list (list empty invalid-data)
                   (list empty invalid-data)
                   (list empty invalid-data)
                   (list empty invalid-data)
                   q2 q3)))
      (mv (pretty-list
           (remove-dup-neighbors
            (comp-v-or$map-to-links-list
             (de-sim-list (si 'comp-v-or data-width)
                          inputs-lst
                          st
                          (comp-v-or$netlist data-width))))
           0)
          state)))
  )

;; Conditions on the inputs

(defund comp-v-or$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (a (comp-v-or$a inputs data-width))
       (b (comp-v-or$b inputs data-width))
       (go-signals (nthcdr (comp-v-or$data-ins-len data-width) inputs)))
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
   (implies (and (comp-v-or$input-format inputs data-width)
                 (comp-v-or$valid-st st data-width))
            (queue2$input-format
             (comp-v-or$q2-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (comp-v-or$input-format
                             queue2$input-format
                             queue2$data-in
                             comp-v-or$valid-st
                             comp-v-or$st-format
                             comp-v-or$q2-inputs)
                            (nthcdr
                             len
                             take-of-too-many))))))

(local
 (defthm comp-v-or$input-format=>q3$input-format
   (implies (and (comp-v-or$input-format inputs data-width)
                 (comp-v-or$valid-st st data-width))
            (queue3$input-format
             (comp-v-or$q3-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (comp-v-or$input-format
                             queue3$input-format
                             queue3$data-in
                             comp-v-or$valid-st
                             comp-v-or$st-format
                             comp-v-or$q3-inputs)
                            (nthcdr
                             len
                             take-of-too-many))))))

(simulate-lemma comp-v-or)

;; ======================================================================

;; 3. Single-Step-Update Property

;; Specify the functionality of COMP-V-OR over a data sequence

(defun comp-v-or$op-seq (seq)
  (if (atom seq)
      nil
    (cons (v-or (caar seq) (cdar seq))
          (comp-v-or$op-seq (cdr seq)))))

(defthm len-of-comp-v-or$op-seq
  (equal (len (comp-v-or$op-seq x))
         (len x)))

(defthm comp-v-or$op-seq-of-append
  (equal (comp-v-or$op-seq (append x y))
         (append (comp-v-or$op-seq x) (comp-v-or$op-seq y))))

;; The extraction function for COMP-V-OR that extracts the future output
;; sequence from the current state.

(defund comp-v-or$extract (st)
  (b* ((a0 (get-field *comp-v-or$a0* st))
       (b0 (get-field *comp-v-or$b0* st))
       (a1 (get-field *comp-v-or$a1* st))
       (b1 (get-field *comp-v-or$b1* st))
       (q2 (get-field *comp-v-or$q2* st))
       (q3 (get-field *comp-v-or$q3* st))

       (a-seq (append (extract-valid-data (list a0))
                      (queue2$extract q2)
                      (extract-valid-data (list a1))))
       (b-seq (append (extract-valid-data (list b0))
                      (queue3$extract q3)
                      (extract-valid-data (list b1)))))
    (comp-v-or$op-seq (pairlis$ a-seq b-seq))))

(defthm comp-v-or$extract-not-empty
  (implies (and (comp-v-or$out-act inputs st data-width)
                (comp-v-or$valid-st st data-width))
           (< 0 (len (comp-v-or$extract st))))
  :hints (("Goal"
           :in-theory (e/d (comp-v-or$valid-st
                            comp-v-or$extract
                            comp-v-or$out-act)
                           (nfix))))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund comp-v-or$inv (st)
    (b* ((a0 (get-field *comp-v-or$a0* st))
         (b0 (get-field *comp-v-or$b0* st))
         (a1 (get-field *comp-v-or$a1* st))
         (b1 (get-field *comp-v-or$b1* st))
         (q2 (get-field *comp-v-or$q2* st))
         (q3 (get-field *comp-v-or$q3* st))

         (a-seq (append (extract-valid-data (list a0))
                        (queue2$extract q2)
                        (extract-valid-data (list a1))))
         (b-seq (append (extract-valid-data (list b0))
                        (queue3$extract q3)
                        (extract-valid-data (list b1)))))
      (equal (len a-seq) (len b-seq))))

  (local
   (defthm booleanp-comp-v-or$q2-in-act
     (implies (and (or (equal (nth *link$s*
                                   (nth *comp-v-or$a0* st))
                              '(t))
                       (equal (nth *link$s*
                                   (nth *comp-v-or$a0* st))
                              '(nil)))
                   (queue2$valid-st (nth *comp-v-or$q2* st) data-width))
              (booleanp
               (queue2$in-act (comp-v-or$q2-inputs inputs st data-width)
                              (nth *comp-v-or$q2* st)
                              data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 comp-v-or$q2-inputs
                                 queue2$valid-st
                                 queue2$in-act)))
     :rule-classes :type-prescription))

  (local
   (defthm booleanp-comp-v-or$q3-in-act
     (implies (and (or (equal (nth *link$s*
                                   (nth *comp-v-or$b0* st))
                              '(t))
                       (equal (nth *link$s*
                                   (nth *comp-v-or$b0* st))
                              '(nil)))
                   (queue3$valid-st (nth *comp-v-or$q3* st) data-width))
              (booleanp
               (queue3$in-act (comp-v-or$q3-inputs inputs st data-width)
                              (nth *comp-v-or$q3* st)
                              data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 comp-v-or$q3-inputs
                                 queue3$valid-st
                                 queue3$in-act)))
     :rule-classes :type-prescription))

  (local
   (defthm comp-v-or$q2-in-act-nil
     (implies (equal (nth *link$s*
                          (nth *comp-v-or$a0* st))
                     '(nil))
              (not (queue2$in-act (comp-v-or$q2-inputs inputs st data-width)
                                  (nth *comp-v-or$q2* st)
                                  data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 comp-v-or$q2-inputs
                                 queue2$in-act)))))

  (local
   (defthm comp-v-or$q3-in-act-nil
     (implies (equal (nth *link$s*
                          (nth *comp-v-or$b0* st))
                     '(nil))
              (not (queue3$in-act (comp-v-or$q3-inputs inputs st data-width)
                                  (nth *comp-v-or$q3* st)
                                  data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 comp-v-or$q3-inputs
                                 queue3$in-act)))))

  (local
   (defthm booleanp-comp-v-or$q2-out-act
     (implies (and (or (equal (nth *link$s*
                                   (nth *comp-v-or$a1* st))
                              '(t))
                       (equal (nth *link$s*
                                   (nth *comp-v-or$a1* st))
                              '(nil)))
                   (queue2$valid-st (nth *comp-v-or$q2* st) data-width))
              (booleanp
               (queue2$out-act (comp-v-or$q2-inputs inputs st data-width)
                               (nth *comp-v-or$q2* st)
                               data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 comp-v-or$q2-inputs
                                 queue2$valid-st
                                 queue2$out-act)))
     :rule-classes :type-prescription))

  (local
   (defthm booleanp-comp-v-or$q3-out-act
     (implies (and (or (equal (nth *link$s*
                                   (nth *comp-v-or$b1* st))
                              '(t))
                       (equal (nth *link$s*
                                   (nth *comp-v-or$b1* st))
                              '(nil)))
                   (queue3$valid-st (nth *comp-v-or$q3* st) data-width))
              (booleanp
               (queue3$out-act (comp-v-or$q3-inputs inputs st data-width)
                               (nth *comp-v-or$q3* st)
                               data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 comp-v-or$q3-inputs
                                 queue3$valid-st
                                 queue3$out-act)))
     :rule-classes :type-prescription))

  (local
   (defthm comp-v-or$q2-out-act-nil
     (implies (equal (nth *link$s*
                          (nth *comp-v-or$a1* st))
                     '(t))
              (not (queue2$out-act (comp-v-or$q2-inputs inputs st data-width)
                                   (nth *comp-v-or$q2* st)
                                   data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 comp-v-or$q2-inputs
                                 queue2$out-act)))))

  (local
   (defthm comp-v-or$q3-out-act-nil
     (implies (equal (nth *link$s*
                          (nth *comp-v-or$b1* st))
                     '(t))
              (not (queue3$out-act (comp-v-or$q3-inputs inputs st data-width)
                                   (nth *comp-v-or$q3* st)
                                   data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 comp-v-or$q3-inputs
                                 queue3$out-act)))))

  (defthm comp-v-or$inv-preserved
    (implies (and (comp-v-or$input-format inputs data-width)
                  (comp-v-or$valid-st st data-width)
                  (comp-v-or$inv st))
             (comp-v-or$inv (comp-v-or$step inputs st data-width)))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              queue2$extracted-step
                              queue3$extracted-step
                              comp-v-or$input-format
                              comp-v-or$valid-st
                              comp-v-or$inv
                              comp-v-or$step
                              comp-v-or$in-act
                              comp-v-or$out-act
                              f-sr)
                             (if*
                              nfix
                              nthcdr
                              take-of-too-many
                              open-v-threefix)))))
  )

;; The extracted next-state function for COMP-V-OR.  Note that this function
;; avoids exploring the internal computation of COMP-V-OR.

(defund comp-v-or$extracted-step (inputs st data-width)
  (b* ((a (comp-v-or$a inputs data-width))
       (b (comp-v-or$b inputs data-width))
       (data (v-or a b))
       (extracted-st (comp-v-or$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-v-or$out-act inputs st data-width) t)
      (cond
       ((equal (comp-v-or$in-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (comp-v-or$in-act inputs st data-width) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm comp-v-or$q2-get-$data-in-rewrite
     (b* ((a0 (get-field *comp-v-or$a0* st))
          (a0.d (get-field *link$d* a0)))
       (implies (and (bvp (strip-cars a0.d))
                     (equal (len a0.d) data-width))
                (equal (queue2$data-in
                        (comp-v-or$q2-inputs inputs st data-width)
                        data-width)
                       (strip-cars a0.d))))
     :hints (("Goal"
              :in-theory (enable queue2$data-in
                                 comp-v-or$q2-inputs)))))

  (local
   (defthm comp-v-or$q3-get-$data-in-rewrite
     (b* ((b0 (get-field *comp-v-or$b0* st))
          (b0.d (get-field *link$d* b0)))
       (implies (and (bvp (strip-cars b0.d))
                     (equal (len b0.d) data-width))
                (equal (queue3$data-in
                        (comp-v-or$q3-inputs inputs st data-width)
                        data-width)
                       (strip-cars b0.d))))
     :hints (("Goal"
              :in-theory (enable queue3$data-in
                                 comp-v-or$q3-inputs)))))

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
   (defthm cdr-queue3$extract-lemma
     (implies
      (and (< 1 (len (queue3$extract st)))
           (queue3$valid-st st data-width)
           (equal n
                  (1- (len (cdr (queue3$extract st)))))
           (queue3$out-act inputs st data-width))
      (equal (append (take n (cdr (queue3$extract st)))
                     (list (queue3$data-out st)))
             (cdr (queue3$extract st))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue3$valid-st
                                        queue3$extract
                                        queue3$out-act
                                        queue3$data-out)))))

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
    (b* ((next-st (comp-v-or$step inputs st data-width)))
      (implies (and (comp-v-or$input-format inputs data-width)
                    (comp-v-or$valid-st st data-width)
                    (comp-v-or$inv st))
               (equal (comp-v-or$extract next-st)
                      (comp-v-or$extracted-step inputs st data-width))))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              queue2$extracted-step
                              queue3$extracted-step
                              comp-v-or$extracted-step
                              comp-v-or$input-format
                              comp-v-or$valid-st
                              comp-v-or$st-format
                              comp-v-or$inv
                              comp-v-or$step
                              comp-v-or$in-act
                              comp-v-or$out-act
                              comp-v-or$extract)
                             (nfix
                              nthcdr
                              len-nthcdr
                              if*
                              strip-cars
                              default-car
                              default-cdr
                              acl2::append-of-cons)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Extract the accepted input sequence

(defun comp-v-or$in-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (comp-v-or$in-act inputs st data-width) t)
          (append (comp-v-or$in-seq
                   (cdr inputs-lst)
                   (comp-v-or$step inputs st data-width)
                   data-width
                   (1- n))
                  (list
                   (cons (comp-v-or$a inputs data-width)
                         (comp-v-or$b inputs data-width))))
        (comp-v-or$in-seq (cdr inputs-lst)
                          (comp-v-or$step inputs st data-width)
                          data-width
                          (1- n))))))

;; Extract the valid output sequence

(defun comp-v-or$out-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (comp-v-or$out-act inputs st data-width) t)
          (append (comp-v-or$out-seq
                   (cdr inputs-lst)
                   (comp-v-or$step inputs st data-width)
                   data-width
                   (1- n))
                  (list (comp-v-or$data-out st)))
        (comp-v-or$out-seq (cdr inputs-lst)
                           (comp-v-or$step inputs st data-width)
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

  (defund comp-v-or$in-out-seq-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-v-or$ins-len data-width))
         ((mv inputs-lst state)
          (signal-vals-gen num-signals n state nil))
         (empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (q2 (list (list empty invalid-data)
                   (list empty invalid-data)))
         (q3 (list (list empty invalid-data)
                   (list empty invalid-data)
                   (list empty invalid-data)))
         (st (list (list empty invalid-data)
                   (list empty invalid-data)
                   (list empty invalid-data)
                   (list empty invalid-data)
                   q2 q3)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-2-lst
                     (comp-v-or$in-seq inputs-lst st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (comp-v-or$out-seq inputs-lst st data-width n)))))
       state)))
  )

;; Prove that comp-v-or$valid-st is an invariant.

(defthm comp-v-or$valid-st-preserved
  (implies (and (comp-v-or$input-format inputs data-width)
                (comp-v-or$valid-st st data-width))
           (comp-v-or$valid-st (comp-v-or$step inputs st data-width)
                               data-width))
  :hints (("Goal"
           :use ((:instance
                  queue2$valid-st-preserved
                  (inputs (comp-v-or$q2-inputs inputs st data-width))
                  (st (get-field *comp-v-or$q2* st)))
                 (:instance
                  queue3$valid-st-preserved
                  (inputs (comp-v-or$q3-inputs inputs st data-width))
                  (st (get-field *comp-v-or$q3* st))))
           :in-theory (e/d (get-field
                            comp-v-or$input-format
                            comp-v-or$valid-st
                            comp-v-or$st-format
                            comp-v-or$step
                            comp-v-or$in-act
                            comp-v-or$out-act
                            f-sr)
                           (queue2$valid-st-preserved
                            queue3$valid-st-preserved
                            if*
                            nfix
                            nthcdr
                            take-of-too-many
                            open-v-threefix)))))

(encapsulate
  ()

  (local
   (defthm take-of-comp-v-or$op-seq-of-pairlis$
     (implies (and (equal (len x) (len y))
                   (<= n (len x)))
              (equal (take n (comp-v-or$op-seq (pairlis$ x y)))
                     (comp-v-or$op-seq (pairlis$ (take n x)
                                             (take n y)))))))

  (local
   (defthm take-of-comp-v-or$op-seq-of-pairlis$-instance
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
      (equal (take n (comp-v-or$op-seq
                      (pairlis$
                       (append x1
                               (queue2$extract q2)
                               (list e1))
                       (append x2
                               (queue3$extract q3)
                               (list e2)))))
             (comp-v-or$op-seq
              (pairlis$
               (append x1
                       (queue2$extract q2))
               (append x2
                       (queue3$extract q3))))))))

  (local
   (defthm append-of-comp-v-or$op-seq-pairlis$-instance
     (implies (equal (len (append x (list e1)))
                     (len (append y (list e2))))
              (equal (append (comp-v-or$op-seq (pairlis$ x y))
                             (list (v-or e1 e2)))
                     (comp-v-or$op-seq (pairlis$ (append x (list e1))
                                             (append y (list e2))))))))

  (defthm comp-v-or$extract-lemma
    (implies (and (comp-v-or$valid-st st data-width)
                  (comp-v-or$inv st)
                  (equal n (1- (len (comp-v-or$extract st))))
                  (comp-v-or$out-act inputs st data-width))
             (equal (append (take n (comp-v-or$extract st))
                            (list (comp-v-or$data-out st)))
                    (comp-v-or$extract st)))
    :hints (("Goal"
             :in-theory (e/d (comp-v-or$valid-st
                              comp-v-or$st-format
                              comp-v-or$inv
                              comp-v-or$extract
                              comp-v-or$out-act
                              comp-v-or$data-out)
                             (pairlis$
                              append
                              acl2::append-of-cons
                              acl2::append-when-not-consp
                              pairlis$-append
                              acl2::len-of-append)))))
  )

(in-out-stream-lemma comp-v-or :op t :inv t)

