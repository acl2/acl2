;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2018

(in-package "ADE")

(include-book "comp-gcd-body")
(include-book "gcd-cond")
(include-book "../merge")

(local (include-book "gcd-alg"))
(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of COMP-GCD2
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of COMP-GCD2
;;
;; Construct the DE module generator COMP-GCD2 that computes the Greatest
;; Common Divisor of two natural numbers.  COMP-GCD2 contains submodule
;; COMP-GCD-BODY, which in turn contains the self-timed serial subtractor
;; SERIAL-SUB as a submodule.

(defconst *comp-gcd2$go-num* (+ *merge$go-num*
                                *gcd-cond$go-num*
                                *comp-gcd-body$go-num*))
(defconst *comp-gcd2$st-len* 5)

(defun comp-gcd2$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun comp-gcd2$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (comp-gcd2$data-ins-len data-width)
     *comp-gcd2$go-num*))

;; DE module generator of COMP-GCD2

(module-generator
 comp-gcd2* (data-width)
 ;; MODULE'S NAME
 (si 'comp-gcd2 data-width)
 ;; INPUTS
 ;; There are 3 types of inputs for a complex joint:
 ;; * full-in and empty-out- signals,
 ;; * input data,
 ;; * GO signals.
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 (* 2 data-width))
                                     (sis 'go 0 *comp-gcd2$go-num*)))
 ;; OUTPUTS
 ;; For a complex joint, in addition to outputing the data, we also report the
 ;; "act" signals from the joints at the module's input and output ports.
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-width))
 ;; INTERNAL STATE
 '(s l0 l1 l2 body)
 ;; OCCURRENCES
 ;; Our DE description of a self-timed module allows links and joints to appear
 ;; in any order in the module's occurrence list, except that LINKS MUST BE
 ;; DECLARED BEFORE JOINTS so that when the module is being evaluated, the "se"
 ;; function called in the first pass will extract the links' full/empty states
 ;; and data and provide these values as inputs for the corresponding joints;
 ;; the "de" function wil make the second pass to update the link's full/empty
 ;; states and data using the joints' output values calculated from the first
 ;; pass.
 (list
  ;; LINKS
  ;; S
  '(s (s-status s-out)
      link1
      (branch-act merge-act done-))

  ;; L0
  (list 'l0
        (list* 'l0-status (sis 'd0-out 0 (* 2 data-width)))
        (si 'link (* 2 data-width))
        (list* 'merge-act 'branch-act (sis 'd0-in 0 (* 2 data-width))))

  ;; L1
  (list 'l1
        (list* 'l1-status (sis 'd1-out 0 (* 2 data-width)))
        (si 'link (* 2 data-width))
        (list* 'branch-act1 'body-in-act (sis 'd1-in 0 (* 2 data-width))))

  ;; L2
  (list 'l2
        (list* 'l2-status (sis 'd2-out 0 (* 2 data-width)))
        (si 'link (* 2 data-width))
        (list* 'body-out-act 'merge-act1 (sis 'd2-in 0 (* 2 data-width))))

  ;; JOINTS
  ;; Merge-in
  '(me-ready-in0 (me-full-in0) b-and (full-in s-status))
  '(me-ready-in1 (me-full-in1) b-and (l2-status s-status))
  (list 'me
        (list* 'merge-act 'in-act 'merge-act1
               (sis 'd0-in 0 (* 2 data-width)))
        (si 'merge (* 2 data-width))
        (list* 'me-full-in0 'me-full-in1 'l0-status 's-out
               (append (sis 'data-in 0 (* 2 data-width))
                       (sis 'd2-out 0 (* 2 data-width))
                       (sis 'go 0 *merge$go-num*))))

  ;; Branch-out
  '(br-ready-out0 (br-empty-out0-) b-or (empty-out- s-status))
  '(br-ready-out1 (br-empty-out1-) b-or (l1-status s-status))
  (list 'branch-out
        (list* 'branch-act 'out-act 'branch-act1 'done-
               (append (sis 'data-out 0 data-width)
                       (sis 'd1-in 0 (* 2 data-width))))
        (si 'gcd-cond data-width)
        (list* 'l0-status 'br-empty-out0- 'br-empty-out1-
               (append (sis 'd0-out 0 (* 2 data-width))
                       (sis 'go 1 *gcd-cond$go-num*))))

  ;; Body
  (list 'body
        (list* 'body-in-act 'body-out-act
               (sis 'd2-in 0 (* 2 data-width)))
        (si 'comp-gcd-body data-width)
        (list* 'l1-status 'l2-status
               (append (sis 'd1-out 0 (* 2 data-width))
                       (sis 'go 2 *comp-gcd-body$go-num*)))))

 :guard (natp data-width))

(make-event
 `(progn
    ,@(state-accessors-gen 'comp-gcd2 '(s l0 l1 l2 body) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of COMP-GCD2.

(defun comp-gcd2$netlist (data-width cnt-width)
  (declare (xargs :guard (and (natp data-width)
                              (<= 2 data-width)
                              (natp cnt-width)
                              (<= 3 cnt-width))))
  (cons (comp-gcd2* data-width)
        (union$ (link1$netlist)
                (gcd-cond$netlist data-width)
                (comp-gcd-body$netlist data-width cnt-width)
                (merge$netlist (* 2 data-width))
                :test 'equal)))

;; Recognizer for COMP-GCD2

(defund comp-gcd2& (netlist data-width cnt-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width)
                              (<= 2 data-width)
                              (natp cnt-width)
                              (<= 3 cnt-width))))
  (and (equal (assoc (si 'comp-gcd2 data-width) netlist)
              (comp-gcd2* data-width))
       (b* ((netlist (delete-to-eq (si 'comp-gcd2 data-width) netlist)))
         (and (link1& netlist)
              (link& netlist (* 2 data-width))
              (gcd-cond& netlist data-width)
              (comp-gcd-body& netlist data-width cnt-width)
              (merge& netlist (* 2 data-width))))))

;; Sanity check

(local
 (defthmd check-comp-gcd2$netlist-64-7
   (and (net-syntax-okp (comp-gcd2$netlist 64 7))
        (net-arity-okp (comp-gcd2$netlist 64 7))
        (comp-gcd2& (comp-gcd2$netlist 64 7) 64 7))))

;; Constraints on the state of COMP-GCD2

(defund comp-gcd2$st-format (st data-width cnt-width)
  (b* ((l0 (get-field *comp-gcd2$l0* st))
       (l1 (get-field *comp-gcd2$l1* st))
       (l2 (get-field *comp-gcd2$l2* st))
       (body (get-field *comp-gcd2$body* st)))
    (and (<= 3 data-width)
         (link$st-format l0 (* 2 data-width))
         (link$st-format l1 (* 2 data-width))
         (link$st-format l2 (* 2 data-width))
         (comp-gcd-body$st-format body data-width cnt-width))))

(defthm comp-gcd2$st-format=>constraints
  (implies (comp-gcd2$st-format st data-width cnt-width)
           (and (natp data-width)
                (<= 3 data-width)
                (natp cnt-width)
                (<= 4 cnt-width)))
  :hints (("Goal" :in-theory (enable comp-gcd2$st-format)))
  :rule-classes :forward-chaining)

(defund comp-gcd2$valid-st (st data-width cnt-width)
  (b* ((s  (get-field *comp-gcd2$s* st))
       (l0 (get-field *comp-gcd2$l0* st))
       (l1 (get-field *comp-gcd2$l1* st))
       (l2 (get-field *comp-gcd2$l2* st))
       (body (get-field *comp-gcd2$body* st)))
    (and (<= 3 data-width)
         (link1$valid-st s)
         (link$valid-st l0 (* 2 data-width))
         (link$valid-st l1 (* 2 data-width))
         (link$valid-st l2 (* 2 data-width))
         (comp-gcd-body$valid-st body data-width cnt-width))))

(defthmd comp-gcd2$valid-st=>constraints
  (implies (comp-gcd2$valid-st st data-width cnt-width)
           (and (natp data-width)
                (<= 3 data-width)
                (natp cnt-width)
                (<= 4 cnt-width)))
  :hints (("Goal" :in-theory (enable comp-gcd-body$valid-st=>constraints
                                     comp-gcd2$valid-st)))
  :rule-classes :forward-chaining)

(defthmd comp-gcd2$valid-st=>st-format
  (implies (comp-gcd2$valid-st st data-width cnt-width)
           (comp-gcd2$st-format st data-width cnt-width))
  :hints (("Goal" :in-theory (e/d (comp-gcd-body$valid-st=>st-format
                                   comp-gcd2$st-format
                                   comp-gcd2$valid-st)
                                  ()))))

;; Extract the input and output signals for COMP-GCD2

(progn
  ;; Extract the input data

  (defun comp-gcd2$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (* 2 (mbe :logic (nfix data-width)
                    :exec  data-width))
          (nthcdr 2 inputs)))

  (defthm len-comp-gcd2$data-in
    (equal (len (comp-gcd2$data-in inputs data-width))
           (* 2 (nfix data-width))))

  (in-theory (disable comp-gcd2$data-in))

  ;; Extract the inputs for the merge-in joint

  (defund comp-gcd2$me-inputs (inputs st data-width)
    (b* ((full-in (nth 0 inputs))
         (data-in (comp-gcd2$data-in inputs data-width))
         (go-signals (nthcdr (comp-gcd2$data-ins-len data-width) inputs))

         (me-go-signals (take *merge$go-num* go-signals))

         (s (get-field *comp-gcd2$s* st))
         (s.s (get-field *link1$s* s))
         (s.d (get-field *link1$d* s))
         (l0 (get-field *comp-gcd2$l0* st))
         (l0.s (get-field *link$s* l0))
         (l2 (get-field *comp-gcd2$l2* st))
         (l2.s (get-field *link$s* l2))
         (l2.d (get-field *link$d* l2))

         (me-full-in0 (f-and full-in (car s.s)))
         (me-full-in1 (f-and (car l2.s) (car s.s))))

      (list* me-full-in0 me-full-in1 (car l0.s) (car s.d)
             (append data-in
                     (v-threefix (strip-cars l2.d))
                     me-go-signals))))

  ;; Extract the inputs for the branch-out joint

  (defund comp-gcd2$br-inputs (inputs st data-width)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (comp-gcd2$data-ins-len data-width) inputs))

         (br-go-signals (take *gcd-cond$go-num*
                              (nthcdr *merge$go-num* go-signals)))

         (s (get-field *comp-gcd2$s* st))
         (s.s (get-field *link1$s* s))
         (l0 (get-field *comp-gcd2$l0* st))
         (l0.s (get-field *link$s* l0))
         (l0.d (get-field *link$d* l0))
         (l1 (get-field *comp-gcd2$l1* st))
         (l1.s (get-field *link$s* l1))

         (br-empty-out0- (f-or empty-out- (car s.s)))
         (br-empty-out1- (f-or (car l1.s) (car s.s))))

      (list* (f-buf (car l0.s)) br-empty-out0- br-empty-out1-
             (append (v-threefix (strip-cars l0.d))
                     br-go-signals))))

  ;; Extract the inputs for the "body" joint

  (defund comp-gcd2$body-inputs (inputs st data-width)
    (b* ((go-signals (nthcdr (comp-gcd2$data-ins-len data-width) inputs))

         (body-go-signals (take *comp-gcd-body$go-num*
                                (nthcdr (+ *merge$go-num*
                                           *gcd-cond$go-num*)
                                        go-signals)))

         (l1 (get-field *comp-gcd2$l1* st))
         (l1.s (get-field *link$s* l1))
         (l1.d (get-field *link$d* l1))
         (l2 (get-field *comp-gcd2$l2* st))
         (l2.s (get-field *link$s* l2)))

      (list* (f-buf (car l1.s)) (f-buf (car l2.s))
             (append (v-threefix (strip-cars l1.d))
                     body-go-signals))))

  ;; Extract the "in-act" signal

  (defund comp-gcd2$in-act (inputs st data-width)
    (merge$act0 (comp-gcd2$me-inputs inputs st data-width)
                (* 2 data-width)))

  (defthm comp-gcd2$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (comp-gcd2$in-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable comp-gcd2$me-inputs
                                       comp-gcd2$in-act))))

  ;; Extract the "out-act" signal

  (defund comp-gcd2$out-act (inputs st data-width)
    (gcd-cond$act0 (comp-gcd2$br-inputs inputs st data-width)
                         data-width))

  (defthm comp-gcd2$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (comp-gcd2$out-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable comp-gcd2$br-inputs
                                       comp-gcd2$out-act))))

  ;; Extract the output data

  (defund comp-gcd2$data-out (inputs st data-width)
    (gcd-cond$data0-out (comp-gcd2$br-inputs inputs st data-width)
                              data-width))

  (defthm len-comp-gcd2$data-out-1
    (implies (comp-gcd2$st-format st data-width cnt-width)
             (equal (len (comp-gcd2$data-out inputs st data-width))
                    data-width))
    :hints (("Goal" :in-theory (enable comp-gcd2$st-format
                                       comp-gcd2$data-out))))

  (defthm len-comp-gcd2$data-out-2
    (implies (comp-gcd2$valid-st st data-width cnt-width)
             (equal (len (comp-gcd2$data-out inputs st data-width))
                    data-width))
    :hints (("Goal" :in-theory (enable comp-gcd-body$valid-st=>constraints
                                       comp-gcd2$valid-st
                                       comp-gcd2$data-out))))

  (defthm bvp-comp-gcd2$data-out
    (implies (and (comp-gcd2$valid-st st data-width cnt-width)
                  (comp-gcd2$out-act inputs st data-width))
             (bvp (comp-gcd2$data-out inputs st data-width)))
    :hints (("Goal" :in-theory (enable comp-gcd-body$valid-st=>constraints
                                       comp-gcd2$valid-st
                                       comp-gcd2$out-act
                                       comp-gcd2$data-out
                                       comp-gcd2$br-inputs
                                       gcd-cond$br-inputs
                                       gcd-cond$act0
                                       gcd-cond$data-in
                                       branch$act0))))

  (defun comp-gcd2$outputs (inputs st data-width)
    (list* (comp-gcd2$in-act inputs st data-width)
           (comp-gcd2$out-act inputs st data-width)
           (comp-gcd2$data-out inputs st data-width)))
  )

;; Prove that COMP-GCD2 is not a DE primitive.

(not-primp-lemma comp-gcd2)

;; The value lemma for COMP-GCD2

(defthmd comp-gcd2$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (comp-gcd2& netlist data-width cnt-width)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-width))
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-gcd2$go-num*)
                  (comp-gcd2$st-format st data-width cnt-width))
             (equal (se (si 'comp-gcd2 data-width) inputs st netlist)
                    (comp-gcd2$outputs inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'comp-gcd2 data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            nthcdr-of-pos-const-idx
                            comp-gcd2&
                            comp-gcd2*$destructure
                            merge$act0
                            merge$value
                            gcd-cond$value
                            comp-gcd-body$value
                            link1$value
                            link$value
                            comp-gcd2$st-format
                            comp-gcd2$in-act
                            comp-gcd2$out-act
                            comp-gcd2$data-out
                            comp-gcd2$br-inputs
                            comp-gcd2$me-inputs)
                           ((comp-gcd2*)
                            de-module-disabled-rules)))))

;; This function specifies the next state of COMP-GCD2.

(defun comp-gcd2$step (inputs st data-width cnt-width)
  (b* ((data-in (comp-gcd2$data-in inputs data-width))

       (s (get-field *comp-gcd2$s* st))
       (s.d (get-field *link1$d* s))
       (l0 (get-field *comp-gcd2$l0* st))
       (l1 (get-field *comp-gcd2$l1* st))
       (l2 (get-field *comp-gcd2$l2* st))
       (l2.d (get-field *link$d* l2))
       (body (get-field *comp-gcd2$body* st))

       (me-inputs (comp-gcd2$me-inputs inputs st data-width))
       (br-inputs (comp-gcd2$br-inputs inputs st data-width))
       (body-inputs (comp-gcd2$body-inputs inputs st data-width))

       (d1-in (gcd-cond$data1-out br-inputs data-width))
       (d2-in (comp-gcd-body$data-out body))

       (done- (gcd-cond$flag br-inputs data-width))
       (merge-act1 (merge$act1 me-inputs (* 2 data-width)))
       (merge-act (merge$act me-inputs (* 2 data-width)))
       (branch-act1 (gcd-cond$act1 br-inputs data-width))
       (branch-act (gcd-cond$act br-inputs data-width))
       (body-in-act (comp-gcd-body$in-act body-inputs body data-width))
       (body-out-act (comp-gcd-body$out-act body-inputs body data-width))

       (s-inputs (list branch-act merge-act done-))
       (l0-inputs (list* merge-act branch-act
                         (fv-if (car s.d) (strip-cars l2.d) data-in)))
       (l1-inputs (list* branch-act1 body-in-act d1-in))
       (l2-inputs (list* body-out-act merge-act1 d2-in)))
    (list
     ;; S
     (link1$step s-inputs s)
     ;; L0
     (link$step l0-inputs l0 (* 2 data-width))
     ;; L1
     (link$step l1-inputs l1 (* 2 data-width))
     ;; L2
     (link$step l2-inputs l2 (* 2 data-width))
     ;; Joint BODY
     (comp-gcd-body$step body-inputs body data-width cnt-width))))

(defthm len-of-comp-gcd2$step
  (equal (len (comp-gcd2$step inputs st data-width cnt-width))
         *comp-gcd2$st-len*))

;; The state lemma for COMP-GCD2

(defthmd comp-gcd2$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (comp-gcd2& netlist data-width cnt-width)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-width))
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-gcd2$go-num*)
                  (comp-gcd2$st-format st data-width cnt-width))
             (equal (de (si 'comp-gcd2 data-width) inputs st netlist)
                    (comp-gcd2$step inputs st data-width cnt-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'comp-gcd2 data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            nthcdr-of-pos-const-idx
                            comp-gcd2&
                            comp-gcd2*$destructure
                            merge$act
                            merge$act0
                            merge$act1
                            merge$value
                            comp-gcd2$st-format
                            comp-gcd2$data-in
                            comp-gcd2$br-inputs
                            comp-gcd2$me-inputs
                            comp-gcd2$body-inputs
                            gcd-cond$value
                            comp-gcd-body$value
                            comp-gcd-body$state
                            link1$value
                            link1$state
                            link$value
                            link$state)
                           ((comp-gcd2*)
                            de-module-disabled-rules)))))

(in-theory (disable comp-gcd2$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund comp-gcd2$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (comp-gcd2$data-in inputs data-width))
       (go-signals (nthcdr (comp-gcd2$data-ins-len data-width) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *comp-gcd2$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(local
 (defthm comp-gcd2$input-format=>body$input-format
   (implies (and (comp-gcd2$input-format inputs data-width)
                 (comp-gcd2$valid-st st data-width cnt-width))
            (comp-gcd-body$input-format
             (comp-gcd2$body-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (comp-gcd-body$input-format
                             comp-gcd-body$data-in
                             comp-gcd-body$valid-st=>constraints
                             comp-gcd2$input-format
                             comp-gcd2$valid-st
                             comp-gcd2$body-inputs)
                            ())))))

(defthm booleanp-comp-gcd2$in-act
  (implies (and (comp-gcd2$input-format inputs data-width)
                (comp-gcd2$valid-st st data-width cnt-width))
           (booleanp (comp-gcd2$in-act inputs st data-width)))
  :hints (("Goal" :in-theory (enable merge$act0
                                     comp-gcd2$input-format
                                     comp-gcd2$valid-st
                                     comp-gcd2$in-act
                                     comp-gcd2$me-inputs)))
  :rule-classes :type-prescription)

(defthm booleanp-comp-gcd2$out-act
  (implies (and (comp-gcd2$input-format inputs data-width)
                (comp-gcd2$valid-st st data-width cnt-width))
           (booleanp (comp-gcd2$out-act inputs st data-width)))
  :hints (("Goal" :in-theory (e/d (branch$act0
                                   gcd-cond$act0
                                   gcd-cond$br-inputs
                                   gcd-cond$flag
                                   gcd-cond$data-in
                                   comp-gcd2$input-format
                                   comp-gcd2$valid-st
                                   comp-gcd2$out-act
                                   comp-gcd2$br-inputs)
                                  (b-gates))))
  :rule-classes :type-prescription)

(simulate-lemma comp-gcd2 :sizes (data-width cnt-width))

;; ======================================================================

;; 3. Single-Step-Update Property

;; Specify the functionality of COMP-GCD2, i.e., compute the greatest common
;; divisor of two natural numbers (see comp-gcd2$op).  Prove the correctness of
;; comp-gcd2$op.

(encapsulate
  ()

  (local
   (defthm v-<-correct-instance
     (implies (and (natp data-width)
                   (equal (len x) (* 2 data-width))
                   (bvp x)
                   (v-< nil t
                        (rev (take data-width x))
                        (rev (nthcdr data-width x))))
              (< (v-to-nat (take data-width x))
                 (v-to-nat (nthcdr data-width x))))
     :hints (("Goal"
              :use (:instance v-<-correct-1
                              (a (take data-width x))
                              (b (nthcdr data-width x)))
              :in-theory (disable v-<-correct-1)))
     :rule-classes :linear))

  (local
   (defthm v-to-nat-of-v-zp
     (equal (v-zp x)
            (equal (v-to-nat x) 0))
     :hints (("Goal" :in-theory (enable v-zp v-nzp v-to-nat)))))

  (local
   (defun my-count (x)
     (nfix (+ (v-to-nat (take (/ (len x) 2) x))
              (v-to-nat (nthcdr (/ (len x) 2) x))))))

  (local
   (defun comp-gcd2$op (x)
     (declare
      (xargs :hints (("Goal"
                      :in-theory (e/d ()
                                      (v-not-take
                                       v-not-nthcdr))))
             :measure (my-count x)))
     (b* ((data-width (/ (len x) 2))
          (a (take data-width x))
          (b (nthcdr data-width x))
          (a-b (take data-width
                     (v-adder t a (v-not b))))
          (b-a (take data-width
                     (v-adder t b (v-not a))))
          (a<b (v-< nil t (rev a) (rev b))))
       (cond
        ((or (atom x)
             (zp data-width)
             (not (bvp x)))
         x)
        ((v-zp a) b)
        ((v-zp b) a)
        ((equal a b) a)
        (t (comp-gcd2$op
            (v-if a<b
                  (append a b-a)
                  (append a-b b))))))))

  (defun comp-gcd2$op (x)
    (declare (xargs :measure (:? x)))
    (b* ((data-width (/ (len x) 2))
         (a (take data-width x))
         (b (nthcdr data-width x))
         (a-b (take data-width
                    (v-adder t a (v-not b))))
         (b-a (take data-width
                    (v-adder t b (v-not a))))
         (a<b (v-< nil t (rev a) (rev b))))
      (cond
       ((or (atom x)
            (zp data-width)
            (not (bvp x)))
        x)
       ((v-zp a) b)
       ((v-zp b) a)
       ((equal a b) a)
       (t (comp-gcd2$op
           (v-if a<b
                 (append a b-a)
                 (append a-b b)))))))

  (defthm bvp-comp-gcd2$op
    (implies (and (natp (/ (len x) 2))
                  (bvp x))
             (bvp (comp-gcd2$op x))))

  (defthm len-comp-gcd2$op
    (implies (and (natp (/ (len x) 2))
                  (bvp x))
             (equal (len (comp-gcd2$op x))
                    (/ (len x) 2))))

  (local
   (defthm comp-gcd2$op-lemma-aux-1
     (implies (and (bv2p a b)
                   (not (v-< nil t (rev a) (rev b)))
                   (equal (v-to-nat a) 0))
              (equal a b))
     :hints (("Goal" :use (v-to-nat-equality
                           v-<-correct-2)))
     :rule-classes nil))

  (local
   (defthm comp-gcd2$op-lemma-aux-2
     (b* ((a (take data-width x))
          (b (nthcdr data-width x))
          (a-b (take data-width
                     (v-adder t a (v-not b))))
          (b-a (take data-width
                     (v-adder t b (v-not a))))
          (a<b (v-< nil t (rev a) (rev b))))
       (implies (and (natp data-width)
                     (equal data-width (/ (len x) 2))
                     (bvp x))
                (equal (comp-gcd2$op (v-if a<b
                                           (append a b-a)
                                           (append a-b b)))
                       (comp-gcd2$op x))))
     :hints (("Goal"
              :induct (comp-gcd2$op x)
              :in-theory (e/d ()
                              (v-to-nat-equality
                               v-not-take
                               v-not-nthcdr)))
             ("Subgoal *1/3"
              :use (:instance
                    v-to-nat-equality
                    (a (take data-width
                             (v-adder t (take data-width x)
                                      (v-not (nthcdr data-width x)))))
                    (b (take data-width x))))
             ("Subgoal *1/2"
              :use ((:instance
                     v-to-nat-equality
                     (a (take data-width
                              (v-adder t (nthcdr data-width x)
                                       (v-not (take data-width x)))))
                     (b (nthcdr data-width x)))
                    (:instance
                     comp-gcd2$op-lemma-aux-1
                     (a (take data-width x))
                     (b (nthcdr data-width x))))))))

  ;; Prove that comp-gcd2$op correctly computes the greatest common divisor

  (local
   (defthm v-to-nat-of-COMP-GCD2$OP-is-GCD-ALG
     (implies (and (equal data-width (/ (len x) 2))
                   (bvp x))
              (equal (v-to-nat (comp-gcd2$op x))
                     (gcd-alg (v-to-nat (take data-width x))
                              (v-to-nat (nthcdr data-width x)))))
     :hints (("Goal" :in-theory (e/d ()
                                     (v-not-take
                                      v-not-nthcdr))))))

  (in-theory (disable comp-gcd2$op))

  (defthmd comp-gcd2$op-commutative
    (implies (bv2p a b)
             (equal (comp-gcd2$op (append a b))
                    (comp-gcd2$op (append b a))))
    :hints (("Goal"
             :use (:instance v-to-nat-equality
                             (a (comp-gcd2$op (append a b)))
                             (b (comp-gcd2$op (append b a))))
             :in-theory (e/d (gcd-alg-commutative)
                             (v-to-nat-equality))))
    :rule-classes ((:rewrite :loop-stopper ((a b)))))

  (defthm comp-gcd2$op-lemma
    (implies (and (natp (/ (len x) 2))
                  (bvp x))
             (equal (comp-gcd2$op (comp-gcd-body$op x))
                    (comp-gcd2$op x)))
    :hints (("Goal"
             :use (:instance comp-gcd2$op-lemma-aux-2
                             (data-width (/ (len x) 2)))
             :in-theory (e/d (serial-sub$op
                              comp-gcd-body$op
                              comp-gcd2$op-commutative)
                             (comp-gcd2$op-lemma-aux-2)))))
  )

;; The operation of COMP-GCD2 over a data sequence

(defun comp-gcd2$op-map (x)
  (if (atom x)
      nil
    (cons (comp-gcd2$op (car x))
          (comp-gcd2$op-map (cdr x)))))

(defthm len-of-comp-gcd2$op-map
  (equal (len (comp-gcd2$op-map x))
         (len x)))

(defthm comp-gcd2$op-map-of-append
  (equal (comp-gcd2$op-map (append x y))
         (append (comp-gcd2$op-map x) (comp-gcd2$op-map y))))

;; The extraction function for COMP-GCD2 that extracts the future output sequence
;; from the current state.

(defund comp-gcd2$extract (st data-width)
  (b* ((l0 (get-field *comp-gcd2$l0* st))
       (l1 (get-field *comp-gcd2$l1* st))
       (l2 (get-field *comp-gcd2$l2* st))
       (body (get-field *comp-gcd2$body* st)))
    (comp-gcd2$op-map
     (append (extract-valid-data (list l1 l2 l0))
             (comp-gcd-body$extract body data-width)))))

(defthm comp-gcd2$extract-not-empty
  (implies (and (comp-gcd2$out-act inputs st data-width)
                (comp-gcd2$valid-st st data-width cnt-width))
           (< 0 (len (comp-gcd2$extract st data-width))))
  :hints (("Goal"
           :in-theory (e/d (branch$act0
                            gcd-cond$br-inputs
                            gcd-cond$act0
                            comp-gcd2$valid-st
                            comp-gcd2$extract
                            comp-gcd2$br-inputs
                            comp-gcd2$out-act)
                           (nfix))))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund comp-gcd2$inv (st data-width)
    (b* ((s (get-field *comp-gcd2$s* st))
         (s.s (get-field *link1$s* s))
         (s.d (get-field *link1$d* s))
         (body (get-field *comp-gcd2$body* st)))
      (and (comp-gcd-body$inv body data-width)
           (if (and (fullp s.s) (not (car s.d)))
               (= (len (comp-gcd2$extract st data-width))
                  0)
             (= (len (comp-gcd2$extract st data-width))
                1)))))

  (local
   (defthm comp-gcd2$input-format-lemma-1
     (implies (comp-gcd2$input-format inputs data-width)
              (booleanp (nth 0 inputs)))
     :hints (("Goal" :in-theory (enable comp-gcd2$input-format)))
     :rule-classes :type-prescription))

  (local
   (defthm comp-gcd2$input-format-lemma-2
     (implies (comp-gcd2$input-format inputs data-width)
              (booleanp (nth 1 inputs)))
     :hints (("Goal" :in-theory (enable comp-gcd2$input-format)))
     :rule-classes :type-prescription))

  (local
   (defthm comp-gcd2$input-format-lemma-3
     (implies (and (comp-gcd2$input-format inputs data-width)
                   (nth 0 inputs))
              (bvp (comp-gcd2$data-in inputs data-width)))
     :hints (("Goal" :in-theory (enable comp-gcd2$input-format)))))

  (local
   (defthm comp-gcd2$body-in-act-inactive
     (b* ((l1 (nth *comp-gcd2$l1* st))
          (l1.s (nth *link$s* l1))
          (body-inputs (comp-gcd2$body-inputs inputs st data-width))
          (body (nth *comp-gcd2$body* st)))
       (implies (emptyp l1.s)
                (not (comp-gcd-body$in-act body-inputs body data-width))))
     :hints (("Goal" :in-theory (enable get-field
                                        comp-gcd2$body-inputs)))))

  (defthm comp-gcd2$inv-preserved
    (implies (and (comp-gcd2$input-format inputs data-width)
                  (comp-gcd2$valid-st st data-width cnt-width)
                  (comp-gcd2$inv st data-width))
             (comp-gcd2$inv (comp-gcd2$step inputs st data-width cnt-width)
                            data-width))
    :hints (("Goal"
             :use comp-gcd2$input-format=>body$input-format
             :in-theory (e/d (get-field
                              f-sr
                              comp-gcd-body$extracted-step
                              comp-gcd2$valid-st
                              comp-gcd2$inv
                              comp-gcd2$step
                              comp-gcd2$extract
                              comp-gcd2$br-inputs
                              comp-gcd2$me-inputs
                              gcd-cond$data-in
                              gcd-cond$flag
                              gcd-cond$act
                              gcd-cond$act0
                              gcd-cond$act1
                              gcd-cond$br-inputs
                              branch$act0
                              branch$act1
                              merge$act
                              merge$act0
                              merge$act1)
                             (comp-gcd2$input-format=>body$input-format
                              b-nor3)))))
  )

;; The extracted next-state function for COMP-GCD2.  Note that this function
;; avoids exploring the internal computation of COMP-GCD2.

(defund comp-gcd2$extracted-step (inputs st data-width)
  (b* ((data (comp-gcd2$op (comp-gcd2$data-in inputs data-width)))
       (extracted-st (comp-gcd2$extract st data-width))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-gcd2$out-act inputs st data-width) t)
      (cond
       ((equal (comp-gcd2$in-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (comp-gcd2$in-act inputs st data-width) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

;; This property characterizes the one-step update on the future output
;; sequence given the current inputs and current state.  The trick here is to
;; apply the extraction function comp-gcd2$extract to the step function
;; comp-gcd2$step so that the one-step update on the future output sequence can
;; be expressed in terms of the comp-gcd2$extracted-step function, which
;; abstracts away the internal computation of COMP-GCD2.

(local
 (defthm comp-gcd2-aux
   (implies (equal (len (comp-gcd-body$extract st data-width))
                   0)
            (not (comp-gcd-body$extract st data-width)))
   :hints (("Goal" :in-theory (enable len-0-is-atom)))))

(encapsulate
  ()

  (local
   (defthm comp-gcd2$body-data-in-rewrite
     (b* ((l1 (nth *comp-gcd2$l1* st))
          (l1.d (nth *link$d* l1))
          (body-inputs (comp-gcd2$body-inputs inputs st data-width)))
       (implies (and (natp data-width)
                     (equal (len l1.d) (* 2 data-width)))
                (equal (comp-gcd-body$data-in body-inputs data-width)
                       (v-threefix (strip-cars l1.d)))))
     :hints (("Goal" :in-theory (enable get-field
                                        comp-gcd-body$data-in
                                        comp-gcd2$body-inputs)))))

  (defthm comp-gcd2$extracted-step-correct
    (b* ((next-st (comp-gcd2$step inputs st data-width cnt-width)))
      (implies (and (comp-gcd2$input-format inputs data-width)
                    (comp-gcd2$valid-st st data-width cnt-width)
                    (comp-gcd2$inv st data-width))
               (equal (comp-gcd2$extract next-st data-width)
                      (comp-gcd2$extracted-step inputs st data-width))))
    :hints (("Goal"
             :use comp-gcd2$input-format=>body$input-format
             :in-theory (e/d (get-field
                              f-sr
                              joint-act
                              fv-if-rewrite
                              comp-gcd-body$valid-st=>constraints
                              comp-gcd-body$extracted-step
                              comp-gcd2$extracted-step
                              comp-gcd2$valid-st
                              comp-gcd2$inv
                              comp-gcd2$step
                              comp-gcd2$in-act
                              comp-gcd2$out-act
                              comp-gcd2$br-inputs
                              comp-gcd2$me-inputs
                              comp-gcd2$extract
                              gcd-cond$data-in
                              gcd-cond$flag
                              gcd-cond$act
                              gcd-cond$act0
                              gcd-cond$act1
                              gcd-cond$data1-out
                              gcd-cond$br-inputs
                              branch$act0
                              branch$act1
                              merge$act
                              merge$act0
                              merge$act1)
                             (comp-gcd2$input-format=>body$input-format
                              v-if-works
                              b-nor3)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that comp-gcd2$valid-st is an invariant.

(encapsulate
  ()

  (local
   (defthm comp-gcd2$body-out-act-inactive
     (b* ((l2 (nth *comp-gcd2$l2* st))
          (l2.s (nth *link$s* l2))
          (body-inputs (comp-gcd2$body-inputs inputs st data-width))
          (body (nth *comp-gcd2$body* st)))
       (implies (fullp l2.s)
                (not (comp-gcd-body$out-act body-inputs body data-width))))
     :hints (("Goal" :in-theory (enable get-field
                                        comp-gcd2$body-inputs)))))

  (defthm comp-gcd2$valid-st-preserved
    (implies (and (comp-gcd2$input-format inputs data-width)
                  (comp-gcd2$valid-st st data-width cnt-width))
             (comp-gcd2$valid-st
              (comp-gcd2$step inputs st data-width cnt-width)
              data-width
              cnt-width))
    :hints (("Goal"
             :use comp-gcd2$input-format=>body$input-format
             :in-theory (e/d (get-field
                              f-sr
                              joint-act
                              comp-gcd-body$valid-st=>constraints
                              comp-gcd2$valid-st
                              comp-gcd2$step
                              comp-gcd2$br-inputs
                              comp-gcd2$me-inputs
                              gcd-cond$data-in
                              gcd-cond$flag
                              gcd-cond$act
                              gcd-cond$act0
                              gcd-cond$act1
                              gcd-cond$br-inputs
                              branch$act0
                              branch$act1
                              merge$act
                              merge$act0
                              merge$act1)
                             (comp-gcd2$input-format=>body$input-format
                              b-nor3)))))
  )

(defthm comp-gcd2$extract-lemma
  (implies (and (comp-gcd2$valid-st st data-width cnt-width)
                (comp-gcd2$inv st data-width)
                (comp-gcd2$out-act inputs st data-width))
           (equal (list (comp-gcd2$data-out inputs st data-width))
                  (nthcdr (1- (len (comp-gcd2$extract st data-width)))
                          (comp-gcd2$extract st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (branch$act0
                            gcd-cond$data-in
                            gcd-cond$br-inputs
                            gcd-cond$act0
                            gcd-cond$flag
                            gcd-cond$data0-out
                            comp-gcd-body$valid-st=>constraints
                            comp-gcd2$valid-st
                            comp-gcd2$inv
                            comp-gcd2$extract
                            comp-gcd2$op
                            comp-gcd2$br-inputs
                            comp-gcd2$out-act
                            comp-gcd2$data-out)
                           (v-if-works
                            nfix)))))

;; Extract the accepted input sequence

(seq-gen comp-gcd2 in in-act 0
         (comp-gcd2$data-in inputs data-width)
         :sizes (data-width cnt-width))

;; Extract the valid output sequence

(seq-gen comp-gcd2 out out-act 1
         (comp-gcd2$data-out inputs st data-width)
         :netlist-data (nthcdr 2 outputs)
         :sizes (data-width cnt-width))

;; The multi-step input-output relationship

(encapsulate
  ()

  (local
   (defthm comp-gcd2$dataflow-correct-aux
     (implies (equal (append x y1)
                     (append (comp-gcd2$op-map seq) y2))
              (equal (append x y1 z)
                     (append (comp-gcd2$op-map seq)
                             y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (acl2::associativity-of-append))))))

  (defthmd comp-gcd2$dataflow-correct
    (b* ((extracted-st (comp-gcd2$extract st data-width))
         (final-st (comp-gcd2$run
                    inputs-seq st data-width cnt-width n))
         (final-extracted-st (comp-gcd2$extract final-st data-width)))
      (implies
       (and (comp-gcd2$input-format-n inputs-seq data-width n)
            (comp-gcd2$valid-st st data-width cnt-width)
            (comp-gcd2$inv st data-width))
       (equal (append final-extracted-st
                      (comp-gcd2$out-seq
                       inputs-seq st data-width cnt-width n))
              (append (comp-gcd2$op-map
                       (comp-gcd2$in-seq
                        inputs-seq st data-width cnt-width n))
                      extracted-st))))
    :hints (("Goal"
             :in-theory (enable comp-gcd2$extracted-step))))

  (defthmd comp-gcd2$functionally-correct
    (b* ((extracted-st (comp-gcd2$extract st data-width))
         (final-st (de-n (si 'comp-gcd2 data-width)
                         inputs-seq st netlist n))
         (final-extracted-st (comp-gcd2$extract final-st data-width)))
      (implies
       (and (comp-gcd2& netlist data-width cnt-width)
            (comp-gcd2$input-format-n inputs-seq data-width n)
            (comp-gcd2$valid-st st data-width cnt-width)
            (comp-gcd2$inv st data-width))
       (equal (append final-extracted-st
                      (comp-gcd2$netlist-out-seq
                       inputs-seq st netlist data-width n))
              (append (comp-gcd2$op-map
                       (comp-gcd2$netlist-in-seq
                        inputs-seq st netlist data-width n))
                      extracted-st))))
    :hints (("Goal"
             :use comp-gcd2$dataflow-correct
             :in-theory (enable comp-gcd2$valid-st=>st-format
                                comp-gcd2$de-n))))
  )

