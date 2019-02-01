;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; December 2018

(in-package "ADE")

(include-book "gcd-body")
(include-book "gcd-cond")
(include-book "gcd-spec")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of GCD
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of GCD
;;
;; Construct a DE module generator that computes the Greatest Common Divisor
;; (GCD) of two natural numbers.  Prove the value and state lemmas for this
;; module generator.  We follow the link-joint model in building this
;; generator.

(defconst *gcd$go-num* (+ *merge$go-num*
                          *gcd-cond$go-num*
                          *gcd-body$go-num*))
(defconst *gcd$st-len* 4)

(defun gcd$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun gcd$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (gcd$data-ins-len data-width)
     *gcd$go-num*))

;; DE module generator of GCD

(module-generator
 gcd* (data-width)
 ;; MODULE'S NAME
 (si 'gcd data-width)
 ;; INPUTS
 ;; There are 3 types of inputs for a complex joint:
 ;; * full-in and empty-out- signals,
 ;; * input data,
 ;; * GO signals.
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 (* 2 data-width))
                                     (sis 'go 0 *gcd$go-num*)))
 ;; OUTPUTS
 ;; For a complex joint, in addition to outputing the data, we also report the
 ;; "act" signals from the joints at the module's input and output ports.
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-width))
 ;; INTERNAL STATE
 '(s l0 l1 l2)
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
        (list* 'branch-act1 'body-act (sis 'd1-in 0 (* 2 data-width))))

  ;; L2
  (list 'l2
        (list* 'l2-status (sis 'd2-out 0 (* 2 data-width)))
        (si 'link (* 2 data-width))
        (list* 'body-act 'merge-act1 (sis 'd2-in 0 (* 2 data-width))))

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
                       (sis 'go *merge$go-num* *gcd-cond$go-num*))))

  ;; Body
  (list 'body
        (list* 'body-act
               (sis 'd2-in 0 (* 2 data-width)))
        (si 'gcd-body data-width)
        (list* 'l1-status 'l2-status
               (append (sis 'd1-out 0 (* 2 data-width))
                       (sis 'go
                            (+ *merge$go-num*
                               *gcd-cond$go-num*)
                            *gcd-body$go-num*)))))

 (declare (xargs :guard (natp data-width))))

(make-event
 `(progn
    ,@(state-accessors-gen 'gcd '(s l0 l1 l2) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of GCD.

(defund gcd$netlist (data-width)
  (declare (xargs :guard (and (natp data-width)
                              (<= 2 data-width))))
  (cons (gcd* data-width)
        (union$ (link1$netlist)
                (link$netlist (* 2 data-width))
                (gcd-cond$netlist data-width)
                (gcd-body$netlist data-width)
                :test 'equal)))

;; Recognizer for GCD

(defund gcd& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width)
                              (<= 2 data-width))))
  (b* ((subnetlist (delete-to-eq (si 'gcd data-width) netlist)))
    (and (equal (assoc (si 'gcd data-width) netlist)
                (gcd* data-width))
         (link1& subnetlist)
         (link& subnetlist (* 2 data-width))
         (gcd-cond& subnetlist data-width)
         (gcd-body& subnetlist data-width)
         (merge& subnetlist (* 2 data-width)))))

;; Sanity check

(local
 (defthmd check-gcd$netlist-64
   (and (net-syntax-okp (gcd$netlist 64))
        (net-arity-okp (gcd$netlist 64))
        (gcd& (gcd$netlist 64) 64))))

;; Constraints on the state of GCD

(defund gcd$st-format (st data-width)
  (b* ((l0 (get-field *gcd$l0* st))
       (l1 (get-field *gcd$l1* st))
       (l2 (get-field *gcd$l2* st)))
    (and (natp data-width)
         (<= 3 data-width)
         (link$st-format l0 (* 2 data-width))
         (link$st-format l1 (* 2 data-width))
         (link$st-format l2 (* 2 data-width)))))

(defthm gcd$st-format=>constraint
  (implies (gcd$st-format st data-width)
           (and (natp data-width)
                (<= 3 data-width)))
  :hints (("Goal" :in-theory (enable gcd$st-format)))
  :rule-classes :forward-chaining)

(defund gcd$valid-st (st data-width)
  (b* ((s  (get-field *gcd$s* st))
       (l0 (get-field *gcd$l0* st))
       (l1 (get-field *gcd$l1* st))
       (l2 (get-field *gcd$l2* st)))
    (and (gcd$st-format st data-width)
         (link1$valid-st s)
         (link$valid-st l0 (* 2 data-width))
         (link$valid-st l1 (* 2 data-width))
         (link$valid-st l2 (* 2 data-width)))))

(defthmd gcd$valid-st=>constraint
  (implies (gcd$valid-st st data-width)
           (and (natp data-width)
                (<= 3 data-width)))
  :hints (("Goal" :in-theory (enable gcd$valid-st)))
  :rule-classes :forward-chaining)

(defthmd gcd$valid-st=>st-format
  (implies (gcd$valid-st st data-width)
           (gcd$st-format st data-width))
  :hints (("Goal" :in-theory (e/d (gcd$valid-st)
                                  ()))))

;; Extract the input and output signals for GCD

(progn
  ;; Extract the input data

  (defun gcd$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (* 2 (mbe :logic (nfix data-width)
                    :exec  data-width))
          (nthcdr 2 inputs)))

  (defthm len-gcd$data-in
    (equal (len (gcd$data-in inputs data-width))
           (* 2 (nfix data-width))))

  (in-theory (disable gcd$data-in))

  ;; Extract the inputs for the merge-in joint

  (defund gcd$me-inputs (inputs st data-width)
    (b* ((full-in (nth 0 inputs))
         (data-in (gcd$data-in inputs data-width))
         (go-signals (nthcdr (gcd$data-ins-len data-width) inputs))

         (me-go-signals (take *merge$go-num* go-signals))

         (s (get-field *gcd$s* st))
         (s.s (get-field *link1$s* s))
         (s.d (get-field *link1$d* s))
         (l0 (get-field *gcd$l0* st))
         (l0.s (get-field *link$s* l0))
         (l2 (get-field *gcd$l2* st))
         (l2.s (get-field *link$s* l2))
         (l2.d (get-field *link$d* l2))

         (me-full-in0 (f-and full-in (car s.s)))
         (me-full-in1 (f-and (car l2.s) (car s.s))))

      (list* me-full-in0 me-full-in1 (car l0.s) (car s.d)
             (append data-in
                     (v-threefix (strip-cars l2.d))
                     me-go-signals))))

  ;; Extract the inputs for the branch-out joint

  (defund gcd$br-inputs (inputs st data-width)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (gcd$data-ins-len data-width) inputs))

         (br-go-signals (take *gcd-cond$go-num*
                              (nthcdr *merge$go-num* go-signals)))

         (s (get-field *gcd$s* st))
         (s.s (get-field *link1$s* s))
         (l0 (get-field *gcd$l0* st))
         (l0.s (get-field *link$s* l0))
         (l0.d (get-field *link$d* l0))
         (l1 (get-field *gcd$l1* st))
         (l1.s (get-field *link$s* l1))

         (br-empty-out0- (f-or empty-out- (car s.s)))
         (br-empty-out1- (f-or (car l1.s) (car s.s))))

      (list* (f-buf (car l0.s)) br-empty-out0- br-empty-out1-
             (append (v-threefix (strip-cars l0.d))
                     br-go-signals))))

  ;; Extract the inputs for the "body" joint

  (defund gcd$body-inputs (inputs st data-width)
    (b* ((go-signals (nthcdr (gcd$data-ins-len data-width) inputs))

         (body-go-signals (take *gcd-body$go-num*
                                (nthcdr (+ *merge$go-num*
                                           *gcd-cond$go-num*)
                                        go-signals)))

         (l1 (get-field *gcd$l1* st))
         (l1.s (get-field *link$s* l1))
         (l1.d (get-field *link$d* l1))
         (l2 (get-field *gcd$l2* st))
         (l2.s (get-field *link$s* l2)))

      (list* (f-buf (car l1.s)) (f-buf (car l2.s))
             (append (v-threefix (strip-cars l1.d))
                     body-go-signals))))

  ;; Extract the "in-act" signal

  (defund gcd$in-act (inputs st data-width)
    (merge$act0 (gcd$me-inputs inputs st data-width)
                (* 2 data-width)))

  (defthm gcd$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (gcd$in-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable gcd$me-inputs
                                       gcd$in-act))))

  ;; Extract the "out-act" signal

  (defund gcd$out-act (inputs st data-width)
    (gcd-cond$act0 (gcd$br-inputs inputs st data-width)
                   data-width))

  (defthm gcd$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (gcd$out-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable gcd$br-inputs
                                       gcd$out-act))))

  ;; Extract the output data

  (defund gcd$data-out (inputs st data-width)
    (gcd-cond$data0-out (gcd$br-inputs inputs st data-width)
                        data-width))

  (defthm len-gcd$data-out-1
    (implies (gcd$st-format st data-width)
             (equal (len (gcd$data-out inputs st data-width))
                    data-width))
    :hints (("Goal" :in-theory (enable gcd$st-format
                                       gcd$data-out))))

  (defthm len-gcd$data-out-2
    (implies (gcd$valid-st st data-width)
             (equal (len (gcd$data-out inputs st data-width))
                    data-width))
    :hints (("Goal" :in-theory (enable gcd$valid-st
                                       gcd$data-out))))

  (defthm bvp-gcd$data-out
    (implies (and (gcd$valid-st st data-width)
                  (gcd$out-act inputs st data-width))
             (bvp (gcd$data-out inputs st data-width)))
    :hints (("Goal" :in-theory (enable gcd$valid-st
                                       gcd$out-act
                                       gcd$data-out
                                       gcd$br-inputs
                                       gcd-cond$br-inputs
                                       gcd-cond$act0
                                       gcd-cond$data-in
                                       branch$act0))))

  (defun gcd$outputs (inputs st data-width)
    (list* (gcd$in-act inputs st data-width)
           (gcd$out-act inputs st data-width)
           (gcd$data-out inputs st data-width)))
  )

;; The value lemma for GCD

(defthm gcd$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (gcd& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-width))
                  (true-listp go-signals)
                  (equal (len go-signals) *gcd$go-num*)
                  (gcd$st-format st data-width))
             (equal (se (si 'gcd data-width) inputs st netlist)
                    (gcd$outputs inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'gcd data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            gcd&
                            gcd*$destructure
                            gcd$data-in
                            merge$act0
                            gcd$st-format
                            gcd$in-act
                            gcd$out-act
                            gcd$data-out
                            gcd$br-inputs
                            gcd$me-inputs)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of GCD.

(defun gcd$step (inputs st data-width)
  (b* ((data-in (gcd$data-in inputs data-width))

       (s (get-field *gcd$s* st))
       (s.d (get-field *link1$d* s))
       (l0 (get-field *gcd$l0* st))
       (l1 (get-field *gcd$l1* st))
       (l2 (get-field *gcd$l2* st))
       (l2.d (get-field *link$d* l2))

       (me-inputs (gcd$me-inputs inputs st data-width))
       (br-inputs (gcd$br-inputs inputs st data-width))
       (body-inputs (gcd$body-inputs inputs st data-width))

       (d1-in (gcd-cond$data1-out br-inputs data-width))
       (d2-in (gcd-body$data-out body-inputs data-width))

       (done- (gcd-cond$flag br-inputs data-width))
       (merge-act1 (merge$act1 me-inputs (* 2 data-width)))
       (merge-act (merge$act me-inputs (* 2 data-width)))
       (branch-act1 (gcd-cond$act1 br-inputs data-width))
       (branch-act (gcd-cond$act br-inputs data-width))
       (body-act (gcd-body$act body-inputs data-width))

       (s-inputs (list branch-act merge-act done-))
       (l0-inputs (list* merge-act branch-act
                         (fv-if (car s.d) (strip-cars l2.d) data-in)))
       (l1-inputs (list* branch-act1 body-act d1-in))
       (l2-inputs (list* body-act merge-act1 d2-in)))
    (list
     ;; S
     (link1$step s-inputs s)
     ;; L0
     (link$step l0-inputs l0 (* 2 data-width))
     ;; L1
     (link$step l1-inputs l1 (* 2 data-width))
     ;; L2
     (link$step l2-inputs l2 (* 2 data-width)))))

(defthm len-of-gcd$step
  (equal (len (gcd$step inputs st data-width))
         *gcd$st-len*))

;; The state lemma for GCD

(defthm gcd$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (gcd& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-width))
                  (true-listp go-signals)
                  (equal (len go-signals) *gcd$go-num*)
                  (gcd$st-format st data-width))
             (equal (de (si 'gcd data-width) inputs st netlist)
                    (gcd$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'gcd data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            gcd&
                            gcd*$destructure
                            merge$act
                            merge$act0
                            merge$act1
                            gcd$st-format
                            gcd$data-in
                            gcd$data-out
                            gcd$br-inputs
                            gcd$me-inputs
                            gcd$body-inputs)
                           (de-module-disabled-rules)))))

(in-theory (disable gcd$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund gcd$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (gcd$data-in inputs data-width))
       (go-signals (nthcdr (gcd$data-ins-len data-width) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *gcd$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(defthm booleanp-gcd$in-act
  (implies (and (gcd$input-format inputs data-width)
                (gcd$valid-st st data-width))
           (booleanp (gcd$in-act inputs st data-width)))
  :hints (("Goal" :in-theory (enable merge$act0
                                     gcd$input-format
                                     gcd$valid-st
                                     gcd$in-act
                                     gcd$me-inputs)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-gcd$out-act
  (implies (and (gcd$input-format inputs data-width)
                (gcd$valid-st st data-width))
           (booleanp (gcd$out-act inputs st data-width)))
  :hints (("Goal" :in-theory (enable branch$act0
                                     gcd-cond$act0
                                     gcd-cond$br-inputs
                                     gcd-cond$flag
                                     gcd-cond$data-in
                                     gcd$input-format
                                     gcd$valid-st
                                     gcd$out-act
                                     gcd$br-inputs)))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma gcd)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for GCD that extracts the future output sequence
;; from the current state.

(defund gcd$extract (st)
  (b* ((l0 (get-field *gcd$l0* st))
       (l1 (get-field *gcd$l1* st))
       (l2 (get-field *gcd$l2* st)))
    (gcd$op-map
     (extract-valid-data (list l1 l2 l0)))))

(defthm gcd$extract-not-empty
  (implies (and (gcd$out-act inputs st data-width)
                (gcd$valid-st st data-width))
           (< 0 (len (gcd$extract st))))
  :hints (("Goal"
           :in-theory (e/d (branch$act0
                            gcd-cond$br-inputs
                            gcd-cond$act0
                            gcd$valid-st
                            gcd$extract
                            gcd$br-inputs
                            gcd$out-act)
                           ())))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund gcd$inv (st)
    (b* ((s (get-field *gcd$s* st))
         (s.s (get-field *link1$s* s))
         (s.d (get-field *link1$d* s)))
      (if (and (fullp s.s) (not (car s.d)))
          (= (len (gcd$extract st))
             0)
        (= (len (gcd$extract st))
           1))))

  (local
   (defthm gcd$input-format-lemma-1
     (implies (gcd$input-format inputs data-width)
              (booleanp (nth 0 inputs)))
     :hints (("Goal" :in-theory (enable gcd$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm gcd$input-format-lemma-2
     (implies (gcd$input-format inputs data-width)
              (booleanp (nth 1 inputs)))
     :hints (("Goal" :in-theory (enable gcd$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm gcd$input-format-lemma-3
     (implies (and (gcd$input-format inputs data-width)
                   (nth 0 inputs))
              (bvp (gcd$data-in inputs data-width)))
     :hints (("Goal" :in-theory (enable gcd$input-format)))))

  (local
   (defthm booleanp-gcd$body-act
     (b* ((body-inputs (gcd$body-inputs inputs st data-width))
          (l1 (nth *gcd$l1* st))
          (l1.d (nth *link$d* l1)))
       (implies (or (equal (nth *link$s*
                                (nth *gcd$l1* st))
                           '(nil))
                    (and (equal (nth *link$s*
                                     (nth *gcd$l1* st))
                                '(t))
                         (equal (nth *link$s*
                                     (nth *gcd$l2* st))
                                '(nil))
                         (equal (len l1.d) (* 2 data-width))
                         (bvp (strip-cars l1.d))))
                (booleanp (gcd-body$act body-inputs data-width))))
     :hints (("Goal" :in-theory (enable get-field
                                        merge$act0
                                        merge$act1
                                        merge$act
                                        gcd-body$data-in
                                        gcd-body$me-inputs
                                        gcd-body$act
                                        gcd-body$a<b
                                        gcd$body-inputs)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm gcd$body-act-inactive
     (b* ((body-inputs (gcd$body-inputs inputs st data-width)))
       (implies (or (equal (nth *link$s*
                                (nth *gcd$l1* st))
                           '(nil))
                    (equal (nth *link$s*
                                (nth *gcd$l2* st))
                           '(t)))
                (not (gcd-body$act body-inputs data-width))))
     :hints (("Goal" :in-theory (enable get-field
                                        gcd$body-inputs)))))

  (defthm gcd$inv-preserved
    (implies (and (gcd$input-format inputs data-width)
                  (gcd$valid-st st data-width)
                  (gcd$inv st))
             (gcd$inv (gcd$step inputs st data-width)))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              gcd$valid-st
                              gcd$st-format
                              gcd$inv
                              gcd$step
                              gcd$extract
                              gcd$br-inputs
                              gcd$me-inputs
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
                             (b-nor3)))))
  )

;; The extracted next-state function for GCD.  Note that this function avoids
;; exploring the internal computation of GCD.

(defund gcd$extracted-step (inputs st data-width)
  (b* ((data (gcd$op (gcd$data-in inputs data-width)))
       (extracted-st (gcd$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (gcd$out-act inputs st data-width) t)
      (cond
       ((equal (gcd$in-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (gcd$in-act inputs st data-width) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

;; This property characterizes the one-step update on the future output
;; sequence given the current inputs and current state.  The trick here is to
;; apply the extraction function gcd$extract to the step function gcd$step so
;; that the one-step update on the future output sequence can be expressed in
;; terms of the gcd$extracted-step function, which abstracts away the internal
;; computation of GCD.

(progn
  (local
   (defthm gcd-body$data-out-expand
     (b* ((body-inputs (gcd$body-inputs inputs st data-width))
          (l1 (nth *gcd$l1* st))
          (l1.d (nth *link$d* l1)))
       (implies
        (and (natp data-width)
             (equal (len l1.d) (* 2 data-width))
             (bvp (strip-cars l1.d)))
        (equal (gcd-body$data-out body-inputs data-width)
               (v-if (v-< nil t
                          (rev (take data-width (strip-cars l1.d)))
                          (rev (nthcdr data-width (strip-cars l1.d))))
                     (append
                      (take data-width (strip-cars l1.d))
                      (take data-width
                            (v-adder
                             t
                             (nthcdr data-width (strip-cars l1.d))
                             (v-not (take data-width (strip-cars l1.d))))))
                     (append
                      (take data-width
                            (v-adder
                             t
                             (take data-width (strip-cars l1.d))
                             (v-not (nthcdr data-width (strip-cars l1.d)))))
                      (nthcdr data-width (strip-cars l1.d)))))))
     :hints (("Goal"
              :in-theory (enable get-field
                                 gcd-body$data-in
                                 gcd-body$a<b
                                 gcd-body$data-out
                                 gcd-body$data0-out
                                 gcd-body$data1-out
                                 gcd$body-inputs)))))

  (defthm gcd$extracted-step-correct
    (b* ((next-st (gcd$step inputs st data-width)))
      (implies (and (gcd$input-format inputs data-width)
                    (gcd$valid-st st data-width)
                    (gcd$inv st))
               (equal (gcd$extract next-st)
                      (gcd$extracted-step inputs st data-width))))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              joint-act
                              gcd$extracted-step
                              gcd$valid-st
                              gcd$st-format
                              gcd$inv
                              gcd$step
                              gcd$in-act
                              gcd$out-act
                              gcd$data-out
                              gcd$br-inputs
                              gcd$me-inputs
                              gcd$extract
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
                             (b-nor3
                              v-if-works
                              v-not-take
                              v-not-nthcdr)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that gcd$valid-st is an invariant.

(defthm gcd$valid-st-preserved
  (implies (and (gcd$input-format inputs data-width)
                (gcd$valid-st st data-width))
           (gcd$valid-st (gcd$step inputs st data-width)
                         data-width))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            f-sr
                            joint-act
                            gcd$valid-st
                            gcd$st-format
                            gcd$step
                            gcd$br-inputs
                            gcd$me-inputs
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
                           (b-nor3)))))

(defthm gcd$extract-lemma
  (implies (and (gcd$valid-st st data-width)
                (gcd$out-act inputs st data-width))
           (equal (list (gcd$data-out inputs st data-width))
                  (nthcdr (1- (len (gcd$extract st)))
                          (gcd$extract st))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (branch$act0
                            gcd-cond$data-in
                            gcd-cond$br-inputs
                            gcd-cond$act0
                            gcd-cond$flag
                            gcd-cond$data0-out
                            gcd$valid-st
                            gcd$extract
                            gcd$op
                            gcd$br-inputs
                            gcd$out-act
                            gcd$data-out)
                           (v-if-works)))))

;; Extract the accepted input sequence

(seq-gen gcd in in-act 0
         (gcd$data-in inputs data-width))

;; Extract the valid output sequence

(seq-gen gcd out out-act 1
         (gcd$data-out inputs st data-width)
         :netlist-data (nthcdr 2 outputs))

;; The multi-step input-output relationship

(in-out-stream-lemma gcd :op gcd$op :inv t)

