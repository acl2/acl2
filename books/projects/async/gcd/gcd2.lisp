;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "gcd-body2")
(include-book "gcd-cond")
(include-book "gcd-spec")
(include-book "../merge")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of GCD2
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of GCD2
;;
;; Construct the DE module generator GCD2 that computes the Greatest Common
;; Divisor of two natural numbers.  GCD2 contains submodule GCD-BODY2, which in
;; turn contains the ripple-carry subtractor RIPPLE-SUB as a submodule.

(defconst *gcd2$go-num* (+ *merge$go-num*
                           *gcd-cond$go-num*
                           *gcd-body2$go-num*))

(defun gcd2$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (* 2 (mbe :logic (nfix data-size)
                 :exec  data-size))))

(defun gcd2$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (gcd2$data-ins-len data-size)
     *gcd2$go-num*))

;; DE module generator of GCD2

(module-generator
 gcd2* (data-size)
 ;; MODULE'S NAME
 (si 'gcd2 data-size)
 ;; INPUTS
 ;; There are 3 types of inputs for a complex joint:
 ;; * full-in and empty-out- signals,
 ;; * input data,
 ;; * GO signals.
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 (* 2 data-size))
                                     (sis 'go 0 *gcd2$go-num*)))
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
        (si 'gcd-body2 data-size)
        (list* 'l1-status 'l2-status
               (append (sis 'd1-out 0 (* 2 data-size))
                       (sis 'go 2 *gcd-body2$go-num*)))))

 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'gcd2 '(s l0 l1 l2 body) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; GCD2.

(defund gcd2$netlist (data-size)
  (declare (xargs :guard (and (natp data-size)
                              (<= 2 data-size))))
  (cons (gcd2* data-size)
        (union$ (link1$netlist)
                (gcd-cond$netlist data-size)
                (gcd-body2$netlist data-size)
                (merge$netlist (* 2 data-size))
                :test 'equal)))

;; Recognizer for GCD2

(defund gcd2& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size)
                              (<= 2 data-size))))
  (b* ((subnetlist (delete-to-eq (si 'gcd2 data-size) netlist)))
    (and (equal (assoc (si 'gcd2 data-size) netlist)
                (gcd2* data-size))
         (link1& subnetlist)
         (link& subnetlist (* 2 data-size))
         (gcd-cond& subnetlist data-size)
         (gcd-body2& subnetlist data-size)
         (merge& subnetlist (* 2 data-size)))))

;; Sanity check

(local
 (defthmd check-gcd2$netlist-64
   (and (net-syntax-okp (gcd2$netlist 64))
        (net-arity-okp (gcd2$netlist 64))
        (gcd2& (gcd2$netlist 64) 64))))

;; Constraints on the state of GCD2

(defund gcd2$st-format (st data-size)
  (b* ((l0 (nth *gcd2$l0* st))
       (l1 (nth *gcd2$l1* st))
       (l2 (nth *gcd2$l2* st))
       (body (nth *gcd2$body* st)))
    (and (<= 3 data-size)
         (link$st-format l0 (* 2 data-size))
         (link$st-format l1 (* 2 data-size))
         (link$st-format l2 (* 2 data-size))
         (gcd-body2$st-format body data-size))))

(defthm gcd2$st-format=>constraint
  (implies (gcd2$st-format st data-size)
           (and (natp data-size)
                (<= 3 data-size)))
  :hints (("Goal" :in-theory (enable gcd2$st-format)))
  :rule-classes :forward-chaining)

(defund gcd2$valid-st (st data-size)
  (b* ((s  (nth *gcd2$s* st))
       (l0 (nth *gcd2$l0* st))
       (l1 (nth *gcd2$l1* st))
       (l2 (nth *gcd2$l2* st))
       (body (nth *gcd2$body* st)))
    (and (<= 3 data-size)
         (link1$valid-st s)
         (link$valid-st l0 (* 2 data-size))
         (link$valid-st l1 (* 2 data-size))
         (link$valid-st l2 (* 2 data-size))
         (gcd-body2$valid-st body data-size))))

(defthmd gcd2$valid-st=>constraint
  (implies (gcd2$valid-st st data-size)
           (and (natp data-size)
                (<= 3 data-size)))
  :hints (("Goal" :in-theory (enable gcd-body2$valid-st=>constraint
                                     gcd2$valid-st)))
  :rule-classes :forward-chaining)

(defthmd gcd2$valid-st=>st-format
  (implies (gcd2$valid-st st data-size)
           (gcd2$st-format st data-size))
  :hints (("Goal" :in-theory (e/d (gcd-body2$valid-st=>st-format
                                   gcd2$st-format
                                   gcd2$valid-st)
                                  ()))))

;; Extract the input and output signals for GCD2

(progn
  ;; Extract the input data

  (defun gcd2$data-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (* 2 (mbe :logic (nfix data-size)
                    :exec  data-size))
          (nthcdr 2 inputs)))

  (defthm len-gcd2$data-in
    (equal (len (gcd2$data-in inputs data-size))
           (* 2 (nfix data-size))))

  (in-theory (disable gcd2$data-in))

  ;; Extract the inputs for the merge-in joint

  (defund gcd2$me-inputs (inputs st data-size)
    (b* ((full-in (nth 0 inputs))
         (data-in (gcd2$data-in inputs data-size))
         (go-signals (nthcdr (gcd2$data-ins-len data-size) inputs))

         (me-go-signals (take *merge$go-num* go-signals))

         (s (nth *gcd2$s* st))
         (s.s (nth *link1$s* s))
         (s.d (nth *link1$d* s))
         (l0 (nth *gcd2$l0* st))
         (l0.s (nth *link$s* l0))
         (l2 (nth *gcd2$l2* st))
         (l2.s (nth *link$s* l2))
         (l2.d (nth *link$d* l2))

         (me-full-in0 (f-and full-in (car s.s)))
         (me-full-in1 (f-and (car l2.s) (car s.s))))

      (list* me-full-in0 me-full-in1 (car l0.s) (car s.d)
             (append data-in
                     (v-threefix (strip-cars l2.d))
                     me-go-signals))))

  ;; Extract the inputs for the branch-out joint

  (defund gcd2$br-inputs (inputs st data-size)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (gcd2$data-ins-len data-size) inputs))

         (br-go-signals (take *gcd-cond$go-num*
                              (nthcdr *merge$go-num* go-signals)))

         (s (nth *gcd2$s* st))
         (s.s (nth *link1$s* s))
         (l0 (nth *gcd2$l0* st))
         (l0.s (nth *link$s* l0))
         (l0.d (nth *link$d* l0))
         (l1 (nth *gcd2$l1* st))
         (l1.s (nth *link$s* l1))

         (br-empty-out0- (f-or empty-out- (car s.s)))
         (br-empty-out1- (f-or (car l1.s) (car s.s))))

      (list* (f-buf (car l0.s)) br-empty-out0- br-empty-out1-
             (append (v-threefix (strip-cars l0.d))
                     br-go-signals))))

  ;; Extract the inputs for the "body" joint

  (defund gcd2$body-inputs (inputs st data-size)
    (b* ((go-signals (nthcdr (gcd2$data-ins-len data-size) inputs))

         (body-go-signals (take *gcd-body2$go-num*
                                (nthcdr (+ *merge$go-num*
                                           *gcd-cond$go-num*)
                                        go-signals)))

         (l1 (nth *gcd2$l1* st))
         (l1.s (nth *link$s* l1))
         (l1.d (nth *link$d* l1))
         (l2 (nth *gcd2$l2* st))
         (l2.s (nth *link$s* l2)))

      (list* (f-buf (car l1.s)) (f-buf (car l2.s))
             (append (v-threefix (strip-cars l1.d))
                     body-go-signals))))

  ;; Extract the "in-act" signal

  (defund gcd2$in-act (inputs st data-size)
    (merge$act0 (gcd2$me-inputs inputs st data-size)
                (* 2 data-size)))

  (defthm gcd2$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (gcd2$in-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable gcd2$me-inputs
                                       gcd2$in-act))))

  ;; Extract the "out-act" signal

  (defund gcd2$out-act (inputs st data-size)
    (gcd-cond$act0 (gcd2$br-inputs inputs st data-size)
                   data-size))

  (defthm gcd2$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (gcd2$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable gcd2$br-inputs
                                       gcd2$out-act))))

  ;; Extract the output data

  (defund gcd2$data-out (inputs st data-size)
    (gcd-cond$data0-out (gcd2$br-inputs inputs st data-size)
                        data-size))

  (defthm len-gcd2$data-out-1
    (implies (gcd2$st-format st data-size)
             (equal (len (gcd2$data-out inputs st data-size))
                    data-size))
    :hints (("Goal" :in-theory (enable gcd2$st-format
                                       gcd2$data-out))))

  (defthm len-gcd2$data-out-2
    (implies (gcd2$valid-st st data-size)
             (equal (len (gcd2$data-out inputs st data-size))
                    data-size))
    :hints (("Goal" :in-theory (enable gcd-body2$valid-st=>constraint
                                       gcd2$valid-st
                                       gcd2$data-out))))

  (defthm bvp-gcd2$data-out
    (implies (and (gcd2$valid-st st data-size)
                  (gcd2$out-act inputs st data-size))
             (bvp (gcd2$data-out inputs st data-size)))
    :hints (("Goal" :in-theory (enable gcd-body2$valid-st=>constraint
                                       gcd2$valid-st
                                       gcd2$out-act
                                       gcd2$data-out
                                       gcd2$br-inputs
                                       gcd-cond$br-inputs
                                       gcd-cond$act0
                                       gcd-cond$data-in
                                       branch$act0))))

  (defun gcd2$outputs (inputs st data-size)
    (list* (gcd2$in-act inputs st data-size)
           (gcd2$out-act inputs st data-size)
           (gcd2$data-out inputs st data-size)))
  )

;; The value lemma for GCD2

(defthm gcd2$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (gcd2& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-size))
                  (true-listp go-signals)
                  (equal (len go-signals) *gcd2$go-num*)
                  (gcd2$st-format st data-size))
             (equal (se (si 'gcd2 data-size) inputs st netlist)
                    (gcd2$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'gcd2 data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            gcd2&
                            gcd2*$destructure
                            merge$act0
                            gcd2$st-format
                            gcd2$in-act
                            gcd2$out-act
                            gcd2$data-out
                            gcd2$br-inputs
                            gcd2$me-inputs)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of GCD2.

(defun gcd2$step (inputs st data-size)
  (b* ((data-in (gcd2$data-in inputs data-size))

       (s (nth *gcd2$s* st))
       (s.d (nth *link1$d* s))
       (l0 (nth *gcd2$l0* st))
       (l1 (nth *gcd2$l1* st))
       (l2 (nth *gcd2$l2* st))
       (l2.d (nth *link$d* l2))
       (body (nth *gcd2$body* st))

       (me-inputs (gcd2$me-inputs inputs st data-size))
       (br-inputs (gcd2$br-inputs inputs st data-size))
       (body-inputs (gcd2$body-inputs inputs st data-size))

       (d1-in (gcd-cond$data1-out br-inputs data-size))
       (d2-in (gcd-body2$data-out body))

       (done- (gcd-cond$flag br-inputs data-size))
       (merge-act1 (merge$act1 me-inputs (* 2 data-size)))
       (merge-act (merge$act me-inputs (* 2 data-size)))
       (branch-act1 (gcd-cond$act1 br-inputs data-size))
       (branch-act (gcd-cond$act br-inputs data-size))
       (body-in-act (gcd-body2$in-act body-inputs body data-size))
       (body-out-act (gcd-body2$out-act body-inputs body data-size))

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
     (gcd-body2$step body-inputs body data-size))))

;; The state lemma for GCD2

(defthm gcd2$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (gcd2& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-size))
                  (true-listp go-signals)
                  (equal (len go-signals) *gcd2$go-num*)
                  (gcd2$st-format st data-size))
             (equal (de (si 'gcd2 data-size) inputs st netlist)
                    (gcd2$step inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'gcd2 data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            gcd2&
                            gcd2*$destructure
                            merge$act
                            merge$act0
                            merge$act1
                            gcd2$st-format
                            gcd2$data-in
                            gcd2$br-inputs
                            gcd2$me-inputs
                            gcd2$body-inputs)
                           (de-module-disabled-rules)))))

(in-theory (disable gcd2$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund gcd2$input-format (inputs data-size)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-size))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (gcd2$data-in inputs data-size))
       (go-signals (nthcdr (gcd2$data-ins-len data-size) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *gcd2$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(local
 (defthm gcd2$input-format=>body$input-format
   (implies (and (gcd2$input-format inputs data-size)
                 (gcd2$valid-st st data-size))
            (gcd-body2$input-format
             (gcd2$body-inputs inputs st data-size)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (gcd-body2$input-format
                             gcd-body2$data-in
                             gcd-body2$valid-st=>constraint
                             gcd2$input-format
                             gcd2$valid-st
                             gcd2$body-inputs)
                            ())))))

(defthm booleanp-gcd2$in-act
  (implies (and (gcd2$input-format inputs data-size)
                (gcd2$valid-st st data-size))
           (booleanp (gcd2$in-act inputs st data-size)))
  :hints (("Goal" :in-theory (enable merge$act0
                                     gcd2$input-format
                                     gcd2$valid-st
                                     gcd2$in-act
                                     gcd2$me-inputs)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-gcd2$out-act
  (implies (and (gcd2$input-format inputs data-size)
                (gcd2$valid-st st data-size))
           (booleanp (gcd2$out-act inputs st data-size)))
  :hints (("Goal" :in-theory (e/d (branch$act0
                                   gcd-cond$act0
                                   gcd-cond$br-inputs
                                   gcd-cond$flag
                                   gcd-cond$data-in
                                   gcd2$input-format
                                   gcd2$valid-st
                                   gcd2$out-act
                                   gcd2$br-inputs)
                                  (b-gates))))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma gcd2)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for GCD2 that extracts the future output
;; sequence from the current state.

(defund gcd2$extract (st data-size)
  (b* ((l0 (nth *gcd2$l0* st))
       (l1 (nth *gcd2$l1* st))
       (l2 (nth *gcd2$l2* st))
       (body (nth *gcd2$body* st)))
    (gcd$op-map
     (append (extract-valid-data (list l0 l1 l2))
             (gcd-body2$extract body data-size)))))

(defthm gcd2$extract-not-empty
  (implies (and (gcd2$out-act inputs st data-size)
                (gcd2$valid-st st data-size))
           (< 0 (len (gcd2$extract st data-size))))
  :hints (("Goal"
           :in-theory (e/d (branch$act0
                            gcd-cond$br-inputs
                            gcd-cond$act0
                            gcd2$valid-st
                            gcd2$extract
                            gcd2$br-inputs
                            gcd2$out-act)
                           (nfix))))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund gcd2$inv (st data-size)
    (b* ((s (nth *gcd2$s* st))
         (s.s (nth *link1$s* s))
         (s.d (nth *link1$d* s))
         (body (nth *gcd2$body* st)))
      (and (if (and (fullp s.s) (not (car s.d)))
               (= (len (gcd2$extract st data-size))
                  0)
             (= (len (gcd2$extract st data-size))
                1))
           (gcd-body2$inv body))))

  (local
   (defthm gcd2$input-format-lemma-1
     (implies (gcd2$input-format inputs data-size)
              (booleanp (nth 0 inputs)))
     :hints (("Goal" :in-theory (enable gcd2$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm gcd2$input-format-lemma-2
     (implies (gcd2$input-format inputs data-size)
              (booleanp (nth 1 inputs)))
     :hints (("Goal" :in-theory (enable gcd2$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm gcd2$input-format-lemma-3
     (implies (and (gcd2$input-format inputs data-size)
                   (nth 0 inputs))
              (bvp (gcd2$data-in inputs data-size)))
     :hints (("Goal" :in-theory (enable gcd2$input-format)))))

  (local
   (defthm gcd2$body-in-act-inactive
     (b* ((l1 (nth *gcd2$l1* st))
          (l1.s (nth *link$s* l1))
          (body-inputs (gcd2$body-inputs inputs st data-size))
          (body (nth *gcd2$body* st)))
       (implies (emptyp l1.s)
                (not (gcd-body2$in-act body-inputs body data-size))))
     :hints (("Goal" :in-theory (enable gcd2$body-inputs)))))

  (defthm gcd2$inv-preserved
    (implies (and (gcd2$input-format inputs data-size)
                  (gcd2$valid-st st data-size)
                  (gcd2$inv st data-size))
             (gcd2$inv (gcd2$step inputs st data-size)
                           data-size))
    :hints (("Goal"
             :use gcd2$input-format=>body$input-format
             :in-theory (e/d (f-sr
                              gcd-body2$extracted-step
                              gcd2$valid-st
                              gcd2$inv
                              gcd2$step
                              gcd2$extract
                              gcd2$br-inputs
                              gcd2$me-inputs
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
                             (gcd2$input-format=>body$input-format
                              b-nor3)))))
  )

;; The extracted next-state function for GCD2.  Note that this function
;; avoids exploring the internal computation of GCD2.

(defund gcd2$extracted-step (inputs st data-size)
  (b* ((data (gcd$op (gcd2$data-in inputs data-size)))
       (extracted-st (gcd2$extract st data-size))
       (n (1- (len extracted-st))))
    (cond
     ((equal (gcd2$out-act inputs st data-size) t)
      (cond
       ((equal (gcd2$in-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (gcd2$in-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

;; This property characterizes the one-step update on the future output
;; sequence given the current inputs and current state.  The trick here is to
;; apply the extraction function gcd2$extract to the step function
;; gcd2$step so that the one-step update on the future output sequence can
;; be expressed in terms of the gcd2$extracted-step function, which
;; abstracts away the internal computation of GCD2.

(local
 (defthm gcd2-aux
   (implies (equal (len (gcd-body2$extract st data-size))
                   0)
            (not (gcd-body2$extract st data-size)))
   :hints (("Goal" :in-theory (enable len-0-is-atom)))))

(encapsulate
  ()

  (local
   (defthm gcd2$body-data-in-rewrite
     (b* ((l1 (nth *gcd2$l1* st))
          (l1.d (nth *link$d* l1))
          (body-inputs (gcd2$body-inputs inputs st data-size)))
       (implies (and (natp data-size)
                     (equal (len l1.d) (* 2 data-size)))
                (equal (gcd-body2$data-in body-inputs data-size)
                       (v-threefix (strip-cars l1.d)))))
     :hints (("Goal" :in-theory (enable gcd-body2$data-in
                                        gcd2$body-inputs)))))

  (local
   (defthm gcd$op-of-gcd-body2$op
     (implies (and (natp (/ (len x) 2))
                   (bvp x))
              (equal (gcd$op (gcd-body2$op x))
                     (gcd$op x)))
     :hints (("Goal"
              :use (:instance gcd$op-lemma
                              (data-size (/ (len x) 2)))
              :in-theory (e/d (gcd-body2$op
                               gcd$op-commutative)
                              (gcd$op-lemma))))))

  (defthm gcd2$extracted-step-correct
    (b* ((next-st (gcd2$step inputs st data-size)))
      (implies (and (gcd2$input-format inputs data-size)
                    (gcd2$valid-st st data-size)
                    (gcd2$inv st data-size))
               (equal (gcd2$extract next-st data-size)
                      (gcd2$extracted-step inputs st data-size))))
    :hints (("Goal"
             :use gcd2$input-format=>body$input-format
             :in-theory (e/d (f-sr
                              joint-act
                              fv-if-rewrite
                              gcd-body2$valid-st=>constraint
                              gcd-body2$extracted-step
                              gcd2$extracted-step
                              gcd2$valid-st
                              gcd2$inv
                              gcd2$step
                              gcd2$in-act
                              gcd2$out-act
                              gcd2$br-inputs
                              gcd2$me-inputs
                              gcd2$extract
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
                             (gcd2$input-format=>body$input-format
                              v-if-works
                              b-nor3)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that gcd2$valid-st is an invariant.

(encapsulate
  ()

  (local
   (defthm gcd2$body-out-act-inactive
     (b* ((l2 (nth *gcd2$l2* st))
          (l2.s (nth *link$s* l2))
          (body-inputs (gcd2$body-inputs inputs st data-size))
          (body (nth *gcd2$body* st)))
       (implies (fullp l2.s)
                (not (gcd-body2$out-act body-inputs body data-size))))
     :hints (("Goal" :in-theory (enable gcd2$body-inputs)))))

  (defthm gcd2$valid-st-preserved
    (implies (and (gcd2$input-format inputs data-size)
                  (gcd2$valid-st st data-size))
             (gcd2$valid-st
              (gcd2$step inputs st data-size)
              data-size))
    :hints (("Goal"
             :use gcd2$input-format=>body$input-format
             :in-theory (e/d (f-sr
                              joint-act
                              gcd-body2$valid-st=>constraint
                              gcd2$valid-st
                              gcd2$step
                              gcd2$br-inputs
                              gcd2$me-inputs
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
                             (gcd2$input-format=>body$input-format
                              b-nor3)))))
  )

(defthm gcd2$extract-lemma
  (implies (and (gcd2$valid-st st data-size)
                (gcd2$inv st data-size)
                (gcd2$out-act inputs st data-size))
           (equal (list (gcd2$data-out inputs st data-size))
                  (nthcdr (1- (len (gcd2$extract st data-size)))
                          (gcd2$extract st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (branch$act0
                            gcd-cond$data-in
                            gcd-cond$br-inputs
                            gcd-cond$act0
                            gcd-cond$flag
                            gcd-cond$data0-out
                            gcd-body2$valid-st=>constraint
                            gcd2$valid-st
                            gcd2$inv
                            gcd2$extract
                            gcd$op
                            gcd2$br-inputs
                            gcd2$out-act
                            gcd2$data-out)
                           (v-if-works
                            nfix)))))

;; Extract the accepted input sequence

(seq-gen gcd2 in in-act 0
         (gcd2$data-in inputs data-size))

;; Extract the valid output sequence

(seq-gen gcd2 out out-act 1
         (gcd2$data-out inputs st data-size)
         :netlist-data (nthcdr 2 outputs))

;; The multi-step input-output relationship

(encapsulate
  ()

  (local
   (defthm gcd2$dataflow-correct-aux
     (implies (equal (append x y1)
                     (append (gcd$op-map seq) y2))
              (equal (append x y1 z)
                     (append (gcd$op-map seq)
                             y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (associativity-of-append))))))

  (defthmd gcd2$dataflow-correct
    (b* ((extracted-st (gcd2$extract st data-size))
         (final-st (gcd2$run
                    inputs-seq st data-size n))
         (final-extracted-st (gcd2$extract final-st data-size)))
      (implies
       (and (gcd2$input-format-n inputs-seq data-size n)
            (gcd2$valid-st st data-size)
            (gcd2$inv st data-size))
       (equal (append final-extracted-st
                      (gcd2$out-seq
                       inputs-seq st data-size n))
              (append (gcd$op-map
                       (gcd2$in-seq
                        inputs-seq st data-size n))
                      extracted-st))))
    :hints (("Goal"
             :in-theory (enable gcd2$extracted-step))))

  (defthmd gcd2$functionally-correct
    (b* ((extracted-st (gcd2$extract st data-size))
         (final-st (de-n (si 'gcd2 data-size)
                         inputs-seq st netlist n))
         (final-extracted-st (gcd2$extract final-st data-size)))
      (implies
       (and (gcd2& netlist data-size)
            (gcd2$input-format-n inputs-seq data-size n)
            (gcd2$valid-st st data-size)
            (gcd2$inv st data-size))
       (equal (append final-extracted-st
                      (gcd2$out-seq-netlist
                       inputs-seq st netlist data-size n))
              (append (gcd$op-map
                       (gcd2$in-seq-netlist
                        inputs-seq st netlist data-size n))
                      extracted-st))))
    :hints (("Goal"
             :use gcd2$dataflow-correct
             :in-theory (enable gcd2$valid-st=>st-format
                                gcd2$de-n))))
  )

