;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; February 2019

(in-package "ADE")

(include-book "comp-gcd-body2")
(include-book "gcd-cond")
(include-book "gcd-spec")
(include-book "../merge")

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
;; COMP-GCD-BODY2, which in turn contains the self-timed serial subtractor
;; SERIAL-SUB as a submodule.

(defconst *comp-gcd2$go-num* (+ *merge$go-num*
                                *gcd-cond$go-num*
                                *comp-gcd-body2$go-num*))
(defconst *comp-gcd2$st-len* 5)

(defun comp-gcd2$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (* 2 (mbe :logic (nfix data-size)
                 :exec  data-size))))

(defun comp-gcd2$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (comp-gcd2$data-ins-len data-size)
     *comp-gcd2$go-num*))

;; DE module generator of COMP-GCD2

(module-generator
 comp-gcd2* (data-size)
 ;; MODULE'S NAME
 (si 'comp-gcd2 data-size)
 ;; INPUTS
 ;; There are 3 types of inputs for a complex joint:
 ;; * full-in and empty-out- signals,
 ;; * input data,
 ;; * GO signals.
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 (* 2 data-size))
                                     (sis 'go 0 *comp-gcd2$go-num*)))
 ;; OUTPUTS
 ;; For a complex joint, in addition to outputing the data, we also report the
 ;; "act" signals from the joints at the module's input and output ports.
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-size))
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
        (list* 'l0-status (sis 'd0-out 0 (* 2 data-size)))
        (si 'link (* 2 data-size))
        (list* 'merge-act 'branch-act (sis 'd0-in 0 (* 2 data-size))))

  ;; L1
  (list 'l1
        (list* 'l1-status (sis 'd1-out 0 (* 2 data-size)))
        (si 'link (* 2 data-size))
        (list* 'branch-act1 'body-in-act (sis 'd1-in 0 (* 2 data-size))))

  ;; L2
  (list 'l2
        (list* 'l2-status (sis 'd2-out 0 (* 2 data-size)))
        (si 'link (* 2 data-size))
        (list* 'body-out-act 'merge-act1 (sis 'd2-in 0 (* 2 data-size))))

  ;; JOINTS
  ;; Merge-in
  '(me-ready-in0 (me-full-in0) b-and (full-in s-status))
  '(me-ready-in1 (me-full-in1) b-and (l2-status s-status))
  (list 'me
        (list* 'merge-act 'in-act 'merge-act1
               (sis 'd0-in 0 (* 2 data-size)))
        (si 'merge (* 2 data-size))
        (list* 'me-full-in0 'me-full-in1 'l0-status 's-out
               (append (sis 'data-in 0 (* 2 data-size))
                       (sis 'd2-out 0 (* 2 data-size))
                       (sis 'go 0 *merge$go-num*))))

  ;; Branch-out
  '(br-ready-out0 (br-empty-out0-) b-or (empty-out- s-status))
  '(br-ready-out1 (br-empty-out1-) b-or (l1-status s-status))
  (list 'branch-out
        (list* 'branch-act 'out-act 'branch-act1 'done-
               (append (sis 'data-out 0 data-size)
                       (sis 'd1-in 0 (* 2 data-size))))
        (si 'gcd-cond data-size)
        (list* 'l0-status 'br-empty-out0- 'br-empty-out1-
               (append (sis 'd0-out 0 (* 2 data-size))
                       (sis 'go 1 *gcd-cond$go-num*))))

  ;; Body
  (list 'body
        (list* 'body-in-act 'body-out-act
               (sis 'd2-in 0 (* 2 data-size)))
        (si 'comp-gcd-body2 data-size)
        (list* 'l1-status 'l2-status
               (append (sis 'd1-out 0 (* 2 data-size))
                       (sis 'go 2 *comp-gcd-body2$go-num*)))))

 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'comp-gcd2 '(s l0 l1 l2 body) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; COMP-GCD2.

(defund comp-gcd2$netlist (data-size cnt-size)
  (declare (xargs :guard (and (natp data-size)
                              (<= 2 data-size)
                              (natp cnt-size)
                              (<= 3 cnt-size))))
  (cons (comp-gcd2* data-size)
        (union$ (link1$netlist)
                (gcd-cond$netlist data-size)
                (comp-gcd-body2$netlist data-size cnt-size)
                (merge$netlist (* 2 data-size))
                :test 'equal)))

;; Recognizer for COMP-GCD2

(defund comp-gcd2& (netlist data-size cnt-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size)
                              (<= 2 data-size)
                              (natp cnt-size)
                              (<= 3 cnt-size))))
  (b* ((subnetlist (delete-to-eq (si 'comp-gcd2 data-size) netlist)))
    (and (equal (assoc (si 'comp-gcd2 data-size) netlist)
                (comp-gcd2* data-size))
         (link1& subnetlist)
         (link& subnetlist (* 2 data-size))
         (gcd-cond& subnetlist data-size)
         (comp-gcd-body2& subnetlist data-size cnt-size)
         (merge& subnetlist (* 2 data-size)))))

;; Sanity check

(local
 (defthmd check-comp-gcd2$netlist-64-7
   (and (net-syntax-okp (comp-gcd2$netlist 64 7))
        (net-arity-okp (comp-gcd2$netlist 64 7))
        (comp-gcd2& (comp-gcd2$netlist 64 7) 64 7))))

;; Constraints on the state of COMP-GCD2

(defund comp-gcd2$st-format (st data-size cnt-size)
  (b* ((l0 (get-field *comp-gcd2$l0* st))
       (l1 (get-field *comp-gcd2$l1* st))
       (l2 (get-field *comp-gcd2$l2* st))
       (body (get-field *comp-gcd2$body* st)))
    (and (<= 3 data-size)
         (link$st-format l0 (* 2 data-size))
         (link$st-format l1 (* 2 data-size))
         (link$st-format l2 (* 2 data-size))
         (comp-gcd-body2$st-format body data-size cnt-size))))

(defthm comp-gcd2$st-format=>constraint
  (implies (comp-gcd2$st-format st data-size cnt-size)
           (and (natp data-size)
                (<= 3 data-size)
                (natp cnt-size)
                (<= 4 cnt-size)))
  :hints (("Goal" :in-theory (enable comp-gcd2$st-format)))
  :rule-classes :forward-chaining)

(defund comp-gcd2$valid-st (st data-size cnt-size)
  (b* ((s  (get-field *comp-gcd2$s* st))
       (l0 (get-field *comp-gcd2$l0* st))
       (l1 (get-field *comp-gcd2$l1* st))
       (l2 (get-field *comp-gcd2$l2* st))
       (body (get-field *comp-gcd2$body* st)))
    (and (<= 3 data-size)
         (link1$valid-st s)
         (link$valid-st l0 (* 2 data-size))
         (link$valid-st l1 (* 2 data-size))
         (link$valid-st l2 (* 2 data-size))
         (comp-gcd-body2$valid-st body data-size cnt-size))))

(defthmd comp-gcd2$valid-st=>constraint
  (implies (comp-gcd2$valid-st st data-size cnt-size)
           (and (natp data-size)
                (<= 3 data-size)
                (natp cnt-size)
                (<= 4 cnt-size)))
  :hints (("Goal" :in-theory (enable comp-gcd-body2$valid-st=>constraint
                                     comp-gcd2$valid-st)))
  :rule-classes :forward-chaining)

(defthmd comp-gcd2$valid-st=>st-format
  (implies (comp-gcd2$valid-st st data-size cnt-size)
           (comp-gcd2$st-format st data-size cnt-size))
  :hints (("Goal" :in-theory (e/d (comp-gcd-body2$valid-st=>st-format
                                   comp-gcd2$st-format
                                   comp-gcd2$valid-st)
                                  ()))))

;; Extract the input and output signals for COMP-GCD2

(progn
  ;; Extract the input data

  (defun comp-gcd2$data-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (* 2 (mbe :logic (nfix data-size)
                    :exec  data-size))
          (nthcdr 2 inputs)))

  (defthm len-comp-gcd2$data-in
    (equal (len (comp-gcd2$data-in inputs data-size))
           (* 2 (nfix data-size))))

  (in-theory (disable comp-gcd2$data-in))

  ;; Extract the inputs for the merge-in joint

  (defund comp-gcd2$me-inputs (inputs st data-size)
    (b* ((full-in (nth 0 inputs))
         (data-in (comp-gcd2$data-in inputs data-size))
         (go-signals (nthcdr (comp-gcd2$data-ins-len data-size) inputs))

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

  (defund comp-gcd2$br-inputs (inputs st data-size)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (comp-gcd2$data-ins-len data-size) inputs))

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

  (defund comp-gcd2$body-inputs (inputs st data-size)
    (b* ((go-signals (nthcdr (comp-gcd2$data-ins-len data-size) inputs))

         (body-go-signals (take *comp-gcd-body2$go-num*
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

  (defund comp-gcd2$in-act (inputs st data-size)
    (merge$act0 (comp-gcd2$me-inputs inputs st data-size)
                (* 2 data-size)))

  (defthm comp-gcd2$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (comp-gcd2$in-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-gcd2$me-inputs
                                       comp-gcd2$in-act))))

  ;; Extract the "out-act" signal

  (defund comp-gcd2$out-act (inputs st data-size)
    (gcd-cond$act0 (comp-gcd2$br-inputs inputs st data-size)
                         data-size))

  (defthm comp-gcd2$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (comp-gcd2$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-gcd2$br-inputs
                                       comp-gcd2$out-act))))

  ;; Extract the output data

  (defund comp-gcd2$data-out (inputs st data-size)
    (gcd-cond$data0-out (comp-gcd2$br-inputs inputs st data-size)
                              data-size))

  (defthm len-comp-gcd2$data-out-1
    (implies (comp-gcd2$st-format st data-size cnt-size)
             (equal (len (comp-gcd2$data-out inputs st data-size))
                    data-size))
    :hints (("Goal" :in-theory (enable comp-gcd2$st-format
                                       comp-gcd2$data-out))))

  (defthm len-comp-gcd2$data-out-2
    (implies (comp-gcd2$valid-st st data-size cnt-size)
             (equal (len (comp-gcd2$data-out inputs st data-size))
                    data-size))
    :hints (("Goal" :in-theory (enable comp-gcd-body2$valid-st=>constraint
                                       comp-gcd2$valid-st
                                       comp-gcd2$data-out))))

  (defthm bvp-comp-gcd2$data-out
    (implies (and (comp-gcd2$valid-st st data-size cnt-size)
                  (comp-gcd2$out-act inputs st data-size))
             (bvp (comp-gcd2$data-out inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-gcd-body2$valid-st=>constraint
                                       comp-gcd2$valid-st
                                       comp-gcd2$out-act
                                       comp-gcd2$data-out
                                       comp-gcd2$br-inputs
                                       gcd-cond$br-inputs
                                       gcd-cond$act0
                                       gcd-cond$data-in
                                       branch$act0))))

  (defun comp-gcd2$outputs (inputs st data-size)
    (list* (comp-gcd2$in-act inputs st data-size)
           (comp-gcd2$out-act inputs st data-size)
           (comp-gcd2$data-out inputs st data-size)))
  )

;; The value lemma for COMP-GCD2

(defthm comp-gcd2$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (comp-gcd2& netlist data-size cnt-size)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-size))
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-gcd2$go-num*)
                  (comp-gcd2$st-format st data-size cnt-size))
             (equal (se (si 'comp-gcd2 data-size) inputs st netlist)
                    (comp-gcd2$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'comp-gcd2 data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            comp-gcd2&
                            comp-gcd2*$destructure
                            merge$act0
                            comp-gcd2$st-format
                            comp-gcd2$in-act
                            comp-gcd2$out-act
                            comp-gcd2$data-out
                            comp-gcd2$br-inputs
                            comp-gcd2$me-inputs)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of COMP-GCD2.

(defun comp-gcd2$step (inputs st data-size cnt-size)
  (b* ((data-in (comp-gcd2$data-in inputs data-size))

       (s (get-field *comp-gcd2$s* st))
       (s.d (get-field *link1$d* s))
       (l0 (get-field *comp-gcd2$l0* st))
       (l1 (get-field *comp-gcd2$l1* st))
       (l2 (get-field *comp-gcd2$l2* st))
       (l2.d (get-field *link$d* l2))
       (body (get-field *comp-gcd2$body* st))

       (me-inputs (comp-gcd2$me-inputs inputs st data-size))
       (br-inputs (comp-gcd2$br-inputs inputs st data-size))
       (body-inputs (comp-gcd2$body-inputs inputs st data-size))

       (d1-in (gcd-cond$data1-out br-inputs data-size))
       (d2-in (comp-gcd-body2$data-out body))

       (done- (gcd-cond$flag br-inputs data-size))
       (merge-act1 (merge$act1 me-inputs (* 2 data-size)))
       (merge-act (merge$act me-inputs (* 2 data-size)))
       (branch-act1 (gcd-cond$act1 br-inputs data-size))
       (branch-act (gcd-cond$act br-inputs data-size))
       (body-in-act (comp-gcd-body2$in-act body-inputs body data-size))
       (body-out-act (comp-gcd-body2$out-act body-inputs body data-size))

       (s-inputs (list branch-act merge-act done-))
       (l0-inputs (list* merge-act branch-act
                         (fv-if (car s.d) (strip-cars l2.d) data-in)))
       (l1-inputs (list* branch-act1 body-in-act d1-in))
       (l2-inputs (list* body-out-act merge-act1 d2-in)))
    (list
     ;; S
     (link1$step s-inputs s)
     ;; L0
     (link$step l0-inputs l0 (* 2 data-size))
     ;; L1
     (link$step l1-inputs l1 (* 2 data-size))
     ;; L2
     (link$step l2-inputs l2 (* 2 data-size))
     ;; Joint BODY
     (comp-gcd-body2$step body-inputs body data-size cnt-size))))

(defthm len-of-comp-gcd2$step
  (equal (len (comp-gcd2$step inputs st data-size cnt-size))
         *comp-gcd2$st-len*))

;; The state lemma for COMP-GCD2

(defthm comp-gcd2$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (comp-gcd2& netlist data-size cnt-size)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-size))
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-gcd2$go-num*)
                  (comp-gcd2$st-format st data-size cnt-size))
             (equal (de (si 'comp-gcd2 data-size) inputs st netlist)
                    (comp-gcd2$step inputs st data-size cnt-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'comp-gcd2 data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            comp-gcd2&
                            comp-gcd2*$destructure
                            merge$act
                            merge$act0
                            merge$act1
                            comp-gcd2$st-format
                            comp-gcd2$data-in
                            comp-gcd2$br-inputs
                            comp-gcd2$me-inputs
                            comp-gcd2$body-inputs)
                           (de-module-disabled-rules)))))

(in-theory (disable comp-gcd2$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund comp-gcd2$input-format (inputs data-size)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-size))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (comp-gcd2$data-in inputs data-size))
       (go-signals (nthcdr (comp-gcd2$data-ins-len data-size) inputs)))
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
   (implies (and (comp-gcd2$input-format inputs data-size)
                 (comp-gcd2$valid-st st data-size cnt-size))
            (comp-gcd-body2$input-format
             (comp-gcd2$body-inputs inputs st data-size)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (comp-gcd-body2$input-format
                             comp-gcd-body2$data-in
                             comp-gcd-body2$valid-st=>constraint
                             comp-gcd2$input-format
                             comp-gcd2$valid-st
                             comp-gcd2$body-inputs)
                            ())))))

(defthm booleanp-comp-gcd2$in-act
  (implies (and (comp-gcd2$input-format inputs data-size)
                (comp-gcd2$valid-st st data-size cnt-size))
           (booleanp (comp-gcd2$in-act inputs st data-size)))
  :hints (("Goal" :in-theory (enable merge$act0
                                     comp-gcd2$input-format
                                     comp-gcd2$valid-st
                                     comp-gcd2$in-act
                                     comp-gcd2$me-inputs)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-gcd2$out-act
  (implies (and (comp-gcd2$input-format inputs data-size)
                (comp-gcd2$valid-st st data-size cnt-size))
           (booleanp (comp-gcd2$out-act inputs st data-size)))
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
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma comp-gcd2 :sizes (data-size cnt-size))

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for COMP-GCD2 that extracts the future output
;; sequence from the current state.

(defund comp-gcd2$extract (st data-size)
  (b* ((l0 (get-field *comp-gcd2$l0* st))
       (l1 (get-field *comp-gcd2$l1* st))
       (l2 (get-field *comp-gcd2$l2* st))
       (body (get-field *comp-gcd2$body* st)))
    (gcd$op-map
     (append (extract-valid-data (list l0 l1 l2))
             (comp-gcd-body2$extract body data-size)))))

(defthm comp-gcd2$extract-not-empty
  (implies (and (comp-gcd2$out-act inputs st data-size)
                (comp-gcd2$valid-st st data-size cnt-size))
           (< 0 (len (comp-gcd2$extract st data-size))))
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
  (defund comp-gcd2$inv (st data-size)
    (b* ((s (get-field *comp-gcd2$s* st))
         (s.s (get-field *link1$s* s))
         (s.d (get-field *link1$d* s))
         (body (get-field *comp-gcd2$body* st)))
      (and (if (and (fullp s.s) (not (car s.d)))
               (= (len (comp-gcd2$extract st data-size))
                  0)
             (= (len (comp-gcd2$extract st data-size))
                1))
           (comp-gcd-body2$inv body data-size))))

  (local
   (defthm comp-gcd2$input-format-lemma-1
     (implies (comp-gcd2$input-format inputs data-size)
              (booleanp (nth 0 inputs)))
     :hints (("Goal" :in-theory (enable comp-gcd2$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm comp-gcd2$input-format-lemma-2
     (implies (comp-gcd2$input-format inputs data-size)
              (booleanp (nth 1 inputs)))
     :hints (("Goal" :in-theory (enable comp-gcd2$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm comp-gcd2$input-format-lemma-3
     (implies (and (comp-gcd2$input-format inputs data-size)
                   (nth 0 inputs))
              (bvp (comp-gcd2$data-in inputs data-size)))
     :hints (("Goal" :in-theory (enable comp-gcd2$input-format)))))

  (local
   (defthm comp-gcd2$body-in-act-inactive
     (b* ((l1 (nth *comp-gcd2$l1* st))
          (l1.s (nth *link$s* l1))
          (body-inputs (comp-gcd2$body-inputs inputs st data-size))
          (body (nth *comp-gcd2$body* st)))
       (implies (emptyp l1.s)
                (not (comp-gcd-body2$in-act body-inputs body data-size))))
     :hints (("Goal" :in-theory (enable get-field
                                        comp-gcd2$body-inputs)))))

  (defthm comp-gcd2$inv-preserved
    (implies (and (comp-gcd2$input-format inputs data-size)
                  (comp-gcd2$valid-st st data-size cnt-size)
                  (comp-gcd2$inv st data-size))
             (comp-gcd2$inv (comp-gcd2$step inputs st data-size cnt-size)
                            data-size))
    :hints (("Goal"
             :use comp-gcd2$input-format=>body$input-format
             :in-theory (e/d (get-field
                              f-sr
                              comp-gcd-body2$extracted-step
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

(defund comp-gcd2$extracted-step (inputs st data-size)
  (b* ((data (gcd$op (comp-gcd2$data-in inputs data-size)))
       (extracted-st (comp-gcd2$extract st data-size))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-gcd2$out-act inputs st data-size) t)
      (cond
       ((equal (comp-gcd2$in-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (comp-gcd2$in-act inputs st data-size) t)
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
   (implies (equal (len (comp-gcd-body2$extract st data-size))
                   0)
            (not (comp-gcd-body2$extract st data-size)))
   :hints (("Goal" :in-theory (enable len-0-is-atom)))))

(encapsulate
  ()

  (local
   (defthm comp-gcd2$body-data-in-rewrite
     (b* ((l1 (nth *comp-gcd2$l1* st))
          (l1.d (nth *link$d* l1))
          (body-inputs (comp-gcd2$body-inputs inputs st data-size)))
       (implies (and (natp data-size)
                     (equal (len l1.d) (* 2 data-size)))
                (equal (comp-gcd-body2$data-in body-inputs data-size)
                       (v-threefix (strip-cars l1.d)))))
     :hints (("Goal" :in-theory (enable get-field
                                        comp-gcd-body2$data-in
                                        comp-gcd2$body-inputs)))))

  (local
   (defthm gcd$op-of-comp-gcd-body2$op
     (implies (and (natp (/ (len x) 2))
                   (bvp x))
              (equal (gcd$op (comp-gcd-body2$op x))
                     (gcd$op x)))
     :hints (("Goal"
              :use (:instance gcd$op-lemma
                              (data-size (/ (len x) 2)))
              :in-theory (e/d (serial-sub$op
                               comp-gcd-body2$op
                               gcd$op-commutative)
                              (gcd$op-lemma))))))

  (defthm comp-gcd2$extracted-step-correct
    (b* ((next-st (comp-gcd2$step inputs st data-size cnt-size)))
      (implies (and (comp-gcd2$input-format inputs data-size)
                    (comp-gcd2$valid-st st data-size cnt-size)
                    (comp-gcd2$inv st data-size))
               (equal (comp-gcd2$extract next-st data-size)
                      (comp-gcd2$extracted-step inputs st data-size))))
    :hints (("Goal"
             :use comp-gcd2$input-format=>body$input-format
             :in-theory (e/d (get-field
                              f-sr
                              joint-act
                              fv-if-rewrite
                              comp-gcd-body2$valid-st=>constraint
                              comp-gcd-body2$extracted-step
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
          (body-inputs (comp-gcd2$body-inputs inputs st data-size))
          (body (nth *comp-gcd2$body* st)))
       (implies (fullp l2.s)
                (not (comp-gcd-body2$out-act body-inputs body data-size))))
     :hints (("Goal" :in-theory (enable get-field
                                        comp-gcd2$body-inputs)))))

  (defthm comp-gcd2$valid-st-preserved
    (implies (and (comp-gcd2$input-format inputs data-size)
                  (comp-gcd2$valid-st st data-size cnt-size))
             (comp-gcd2$valid-st
              (comp-gcd2$step inputs st data-size cnt-size)
              data-size
              cnt-size))
    :hints (("Goal"
             :use comp-gcd2$input-format=>body$input-format
             :in-theory (e/d (get-field
                              f-sr
                              joint-act
                              comp-gcd-body2$valid-st=>constraint
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
  (implies (and (comp-gcd2$valid-st st data-size cnt-size)
                (comp-gcd2$inv st data-size)
                (comp-gcd2$out-act inputs st data-size))
           (equal (list (comp-gcd2$data-out inputs st data-size))
                  (nthcdr (1- (len (comp-gcd2$extract st data-size)))
                          (comp-gcd2$extract st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (branch$act0
                            gcd-cond$data-in
                            gcd-cond$br-inputs
                            gcd-cond$act0
                            gcd-cond$flag
                            gcd-cond$data0-out
                            comp-gcd-body2$valid-st=>constraint
                            comp-gcd2$valid-st
                            comp-gcd2$inv
                            comp-gcd2$extract
                            gcd$op
                            comp-gcd2$br-inputs
                            comp-gcd2$out-act
                            comp-gcd2$data-out)
                           (v-if-works
                            nfix)))))

;; Extract the accepted input sequence

(seq-gen comp-gcd2 in in-act 0
         (comp-gcd2$data-in inputs data-size)
         :sizes (data-size cnt-size))

;; Extract the valid output sequence

(seq-gen comp-gcd2 out out-act 1
         (comp-gcd2$data-out inputs st data-size)
         :netlist-data (nthcdr 2 outputs)
         :sizes (data-size cnt-size))

;; The multi-step input-output relationship

(encapsulate
  ()

  (local
   (defthm comp-gcd2$dataflow-correct-aux
     (implies (equal (append x y1)
                     (append (gcd$op-map seq) y2))
              (equal (append x y1 z)
                     (append (gcd$op-map seq)
                             y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (associativity-of-append))))))

  (defthmd comp-gcd2$dataflow-correct
    (b* ((extracted-st (comp-gcd2$extract st data-size))
         (final-st (comp-gcd2$run
                    inputs-seq st data-size cnt-size n))
         (final-extracted-st (comp-gcd2$extract final-st data-size)))
      (implies
       (and (comp-gcd2$input-format-n inputs-seq data-size n)
            (comp-gcd2$valid-st st data-size cnt-size)
            (comp-gcd2$inv st data-size))
       (equal (append final-extracted-st
                      (comp-gcd2$out-seq
                       inputs-seq st data-size cnt-size n))
              (append (gcd$op-map
                       (comp-gcd2$in-seq
                        inputs-seq st data-size cnt-size n))
                      extracted-st))))
    :hints (("Goal"
             :in-theory (enable comp-gcd2$extracted-step))))

  (defthmd comp-gcd2$functionally-correct
    (b* ((extracted-st (comp-gcd2$extract st data-size))
         (final-st (de-n (si 'comp-gcd2 data-size)
                         inputs-seq st netlist n))
         (final-extracted-st (comp-gcd2$extract final-st data-size)))
      (implies
       (and (comp-gcd2& netlist data-size cnt-size)
            (comp-gcd2$input-format-n inputs-seq data-size n)
            (comp-gcd2$valid-st st data-size cnt-size)
            (comp-gcd2$inv st data-size))
       (equal (append final-extracted-st
                      (comp-gcd2$out-seq-netlist
                       inputs-seq st netlist data-size n))
              (append (gcd$op-map
                       (comp-gcd2$in-seq-netlist
                        inputs-seq st netlist data-size n))
                      extracted-st))))
    :hints (("Goal"
             :use comp-gcd2$dataflow-correct
             :in-theory (enable comp-gcd2$valid-st=>st-format
                                comp-gcd2$de-n))))
  )

