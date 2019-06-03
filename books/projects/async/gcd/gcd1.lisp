;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "gcd-body1")
(include-book "gcd-cond")
(include-book "gcd-spec")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of GCD1
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of GCD1
;;
;; Construct a DE module generator that computes the Greatest Common Divisor
;; (GCD1) of two natural numbers.  Prove the value and state lemmas for this
;; module generator.  We follow the link-joint model in building this
;; generator.

(defconst *gcd1$go-num* (+ *merge$go-num*
                          *gcd-cond$go-num*
                          *gcd-body1$go-num*))

(defun gcd1$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (* 2 (mbe :logic (nfix data-size)
                 :exec  data-size))))

(defun gcd1$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (gcd1$data-ins-len data-size)
     *gcd1$go-num*))

;; DE module generator of GCD1

(module-generator
 gcd1* (data-size)
 ;; MODULE'S NAME
 (si 'gcd1 data-size)
 ;; INPUTS
 ;; There are 3 types of inputs for a complex joint:
 ;; * full-in and empty-out- signals,
 ;; * input data,
 ;; * GO signals.
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 (* 2 data-size))
                                     (sis 'go 0 *gcd1$go-num*)))
 ;; OUTPUTS
 ;; For a complex joint, in addition to outputing the data, we also report the
 ;; "act" signals from the joints at the module's input and output ports.
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-size))
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
        (list* 'l0-status (sis 'd0-out 0 (* 2 data-size)))
        (si 'link (* 2 data-size))
        (list* 'merge-act 'branch-act (sis 'd0-in 0 (* 2 data-size))))

  ;; L1
  (list 'l1
        (list* 'l1-status (sis 'd1-out 0 (* 2 data-size)))
        (si 'link (* 2 data-size))
        (list* 'branch-act1 'body-act (sis 'd1-in 0 (* 2 data-size))))

  ;; L2
  (list 'l2
        (list* 'l2-status (sis 'd2-out 0 (* 2 data-size)))
        (si 'link (* 2 data-size))
        (list* 'body-act 'merge-act1 (sis 'd2-in 0 (* 2 data-size))))

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
                       (sis 'go *merge$go-num* *gcd-cond$go-num*))))

  ;; Body
  (list 'body
        (list* 'body-act
               (sis 'd2-in 0 (* 2 data-size)))
        (si 'gcd-body1 data-size)
        (list* 'l1-status 'l2-status
               (append (sis 'd1-out 0 (* 2 data-size))
                       (sis 'go
                            (+ *merge$go-num*
                               *gcd-cond$go-num*)
                            *gcd-body1$go-num*)))))

 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'gcd1 '(s l0 l1 l2) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of GCD1.

(defund gcd1$netlist (data-size)
  (declare (xargs :guard (and (natp data-size)
                              (<= 2 data-size))))
  (cons (gcd1* data-size)
        (union$ (link1$netlist)
                (link$netlist (* 2 data-size))
                (gcd-cond$netlist data-size)
                (gcd-body1$netlist data-size)
                :test 'equal)))

;; Recognizer for GCD1

(defund gcd1& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size)
                              (<= 2 data-size))))
  (b* ((subnetlist (delete-to-eq (si 'gcd1 data-size) netlist)))
    (and (equal (assoc (si 'gcd1 data-size) netlist)
                (gcd1* data-size))
         (link1& subnetlist)
         (link& subnetlist (* 2 data-size))
         (gcd-cond& subnetlist data-size)
         (gcd-body1& subnetlist data-size)
         (merge& subnetlist (* 2 data-size)))))

;; Sanity check

(local
 (defthmd check-gcd1$netlist-64
   (and (net-syntax-okp (gcd1$netlist 64))
        (net-arity-okp (gcd1$netlist 64))
        (gcd1& (gcd1$netlist 64) 64))))

;; Constraints on the state of GCD1

(defund gcd1$st-format (st data-size)
  (b* ((l0 (nth *gcd1$l0* st))
       (l1 (nth *gcd1$l1* st))
       (l2 (nth *gcd1$l2* st)))
    (and (natp data-size)
         (<= 3 data-size)
         (link$st-format l0 (* 2 data-size))
         (link$st-format l1 (* 2 data-size))
         (link$st-format l2 (* 2 data-size)))))

(defthm gcd1$st-format=>constraint
  (implies (gcd1$st-format st data-size)
           (and (natp data-size)
                (<= 3 data-size)))
  :hints (("Goal" :in-theory (enable gcd1$st-format)))
  :rule-classes :forward-chaining)

(defund gcd1$valid-st (st data-size)
  (b* ((s  (nth *gcd1$s* st))
       (l0 (nth *gcd1$l0* st))
       (l1 (nth *gcd1$l1* st))
       (l2 (nth *gcd1$l2* st)))
    (and (gcd1$st-format st data-size)
         (link1$valid-st s)
         (link$valid-st l0 (* 2 data-size))
         (link$valid-st l1 (* 2 data-size))
         (link$valid-st l2 (* 2 data-size)))))

(defthmd gcd1$valid-st=>constraint
  (implies (gcd1$valid-st st data-size)
           (and (natp data-size)
                (<= 3 data-size)))
  :hints (("Goal" :in-theory (enable gcd1$valid-st)))
  :rule-classes :forward-chaining)

(defthmd gcd1$valid-st=>st-format
  (implies (gcd1$valid-st st data-size)
           (gcd1$st-format st data-size))
  :hints (("Goal" :in-theory (e/d (gcd1$valid-st)
                                  ()))))

;; Extract the input and output signals for GCD1

(progn
  ;; Extract the input data

  (defun gcd1$data-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (* 2 (mbe :logic (nfix data-size)
                    :exec  data-size))
          (nthcdr 2 inputs)))

  (defthm len-gcd1$data-in
    (equal (len (gcd1$data-in inputs data-size))
           (* 2 (nfix data-size))))

  (in-theory (disable gcd1$data-in))

  ;; Extract the inputs for the merge-in joint

  (defund gcd1$me-inputs (inputs st data-size)
    (b* ((full-in (nth 0 inputs))
         (data-in (gcd1$data-in inputs data-size))
         (go-signals (nthcdr (gcd1$data-ins-len data-size) inputs))

         (me-go-signals (take *merge$go-num* go-signals))

         (s (nth *gcd1$s* st))
         (s.s (nth *link1$s* s))
         (s.d (nth *link1$d* s))
         (l0 (nth *gcd1$l0* st))
         (l0.s (nth *link$s* l0))
         (l2 (nth *gcd1$l2* st))
         (l2.s (nth *link$s* l2))
         (l2.d (nth *link$d* l2))

         (me-full-in0 (f-and full-in (car s.s)))
         (me-full-in1 (f-and (car l2.s) (car s.s))))

      (list* me-full-in0 me-full-in1 (car l0.s) (car s.d)
             (append data-in
                     (v-threefix (strip-cars l2.d))
                     me-go-signals))))

  ;; Extract the inputs for the branch-out joint

  (defund gcd1$br-inputs (inputs st data-size)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (gcd1$data-ins-len data-size) inputs))

         (br-go-signals (take *gcd-cond$go-num*
                              (nthcdr *merge$go-num* go-signals)))

         (s (nth *gcd1$s* st))
         (s.s (nth *link1$s* s))
         (l0 (nth *gcd1$l0* st))
         (l0.s (nth *link$s* l0))
         (l0.d (nth *link$d* l0))
         (l1 (nth *gcd1$l1* st))
         (l1.s (nth *link$s* l1))

         (br-empty-out0- (f-or empty-out- (car s.s)))
         (br-empty-out1- (f-or (car l1.s) (car s.s))))

      (list* (f-buf (car l0.s)) br-empty-out0- br-empty-out1-
             (append (v-threefix (strip-cars l0.d))
                     br-go-signals))))

  ;; Extract the inputs for the "body" joint

  (defund gcd1$body-inputs (inputs st data-size)
    (b* ((go-signals (nthcdr (gcd1$data-ins-len data-size) inputs))

         (body-go-signals (take *gcd-body1$go-num*
                                (nthcdr (+ *merge$go-num*
                                           *gcd-cond$go-num*)
                                        go-signals)))

         (l1 (nth *gcd1$l1* st))
         (l1.s (nth *link$s* l1))
         (l1.d (nth *link$d* l1))
         (l2 (nth *gcd1$l2* st))
         (l2.s (nth *link$s* l2)))

      (list* (f-buf (car l1.s)) (f-buf (car l2.s))
             (append (v-threefix (strip-cars l1.d))
                     body-go-signals))))

  ;; Extract the "in-act" signal

  (defund gcd1$in-act (inputs st data-size)
    (merge$act0 (gcd1$me-inputs inputs st data-size)
                (* 2 data-size)))

  (defthm gcd1$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (gcd1$in-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable gcd1$me-inputs
                                       gcd1$in-act))))

  ;; Extract the "out-act" signal

  (defund gcd1$out-act (inputs st data-size)
    (gcd-cond$act0 (gcd1$br-inputs inputs st data-size)
                   data-size))

  (defthm gcd1$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (gcd1$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable gcd1$br-inputs
                                       gcd1$out-act))))

  ;; Extract the output data

  (defund gcd1$data-out (inputs st data-size)
    (gcd-cond$data0-out (gcd1$br-inputs inputs st data-size)
                        data-size))

  (defthm len-gcd1$data-out-1
    (implies (gcd1$st-format st data-size)
             (equal (len (gcd1$data-out inputs st data-size))
                    data-size))
    :hints (("Goal" :in-theory (enable gcd1$st-format
                                       gcd1$data-out))))

  (defthm len-gcd1$data-out-2
    (implies (gcd1$valid-st st data-size)
             (equal (len (gcd1$data-out inputs st data-size))
                    data-size))
    :hints (("Goal" :in-theory (enable gcd1$valid-st
                                       gcd1$data-out))))

  (defthm bvp-gcd1$data-out
    (implies (and (gcd1$valid-st st data-size)
                  (gcd1$out-act inputs st data-size))
             (bvp (gcd1$data-out inputs st data-size)))
    :hints (("Goal" :in-theory (enable gcd1$valid-st
                                       gcd1$out-act
                                       gcd1$data-out
                                       gcd1$br-inputs
                                       gcd-cond$br-inputs
                                       gcd-cond$act0
                                       gcd-cond$data-in
                                       branch$act0))))

  (defun gcd1$outputs (inputs st data-size)
    (list* (gcd1$in-act inputs st data-size)
           (gcd1$out-act inputs st data-size)
           (gcd1$data-out inputs st data-size)))
  )

;; The value lemma for GCD1

(defthm gcd1$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (gcd1& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-size))
                  (true-listp go-signals)
                  (equal (len go-signals) *gcd1$go-num*)
                  (gcd1$st-format st data-size))
             (equal (se (si 'gcd1 data-size) inputs st netlist)
                    (gcd1$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'gcd1 data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            gcd1&
                            gcd1*$destructure
                            gcd1$data-in
                            merge$act0
                            gcd1$st-format
                            gcd1$in-act
                            gcd1$out-act
                            gcd1$data-out
                            gcd1$br-inputs
                            gcd1$me-inputs)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of GCD1.

(defun gcd1$step (inputs st data-size)
  (b* ((data-in (gcd1$data-in inputs data-size))

       (s (nth *gcd1$s* st))
       (s.d (nth *link1$d* s))
       (l0 (nth *gcd1$l0* st))
       (l1 (nth *gcd1$l1* st))
       (l2 (nth *gcd1$l2* st))
       (l2.d (nth *link$d* l2))

       (me-inputs (gcd1$me-inputs inputs st data-size))
       (br-inputs (gcd1$br-inputs inputs st data-size))
       (body-inputs (gcd1$body-inputs inputs st data-size))

       (d1-in (gcd-cond$data1-out br-inputs data-size))
       (d2-in (gcd-body1$data-out body-inputs data-size))

       (done- (gcd-cond$flag br-inputs data-size))
       (merge-act1 (merge$act1 me-inputs (* 2 data-size)))
       (merge-act (merge$act me-inputs (* 2 data-size)))
       (branch-act1 (gcd-cond$act1 br-inputs data-size))
       (branch-act (gcd-cond$act br-inputs data-size))
       (body-act (gcd-body1$act body-inputs data-size))

       (s-inputs (list branch-act merge-act done-))
       (l0-inputs (list* merge-act branch-act
                         (fv-if (car s.d) (strip-cars l2.d) data-in)))
       (l1-inputs (list* branch-act1 body-act d1-in))
       (l2-inputs (list* body-act merge-act1 d2-in)))
    (list
     ;; S
     (link1$step s-inputs s)
     ;; L0
     (link$step l0-inputs l0 (* 2 data-size))
     ;; L1
     (link$step l1-inputs l1 (* 2 data-size))
     ;; L2
     (link$step l2-inputs l2 (* 2 data-size)))))

;; The state lemma for GCD1

(defthm gcd1$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (gcd1& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-size))
                  (true-listp go-signals)
                  (equal (len go-signals) *gcd1$go-num*)
                  (gcd1$st-format st data-size))
             (equal (de (si 'gcd1 data-size) inputs st netlist)
                    (gcd1$step inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'gcd1 data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            gcd1&
                            gcd1*$destructure
                            merge$act
                            merge$act0
                            merge$act1
                            gcd1$st-format
                            gcd1$data-in
                            gcd1$data-out
                            gcd1$br-inputs
                            gcd1$me-inputs
                            gcd1$body-inputs)
                           (de-module-disabled-rules)))))

(in-theory (disable gcd1$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund gcd1$input-format (inputs data-size)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-size))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (gcd1$data-in inputs data-size))
       (go-signals (nthcdr (gcd1$data-ins-len data-size) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *gcd1$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(defthm booleanp-gcd1$in-act
  (implies (and (gcd1$input-format inputs data-size)
                (gcd1$valid-st st data-size))
           (booleanp (gcd1$in-act inputs st data-size)))
  :hints (("Goal" :in-theory (enable merge$act0
                                     gcd1$input-format
                                     gcd1$valid-st
                                     gcd1$in-act
                                     gcd1$me-inputs)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-gcd1$out-act
  (implies (and (gcd1$input-format inputs data-size)
                (gcd1$valid-st st data-size))
           (booleanp (gcd1$out-act inputs st data-size)))
  :hints (("Goal" :in-theory (enable branch$act0
                                     gcd-cond$act0
                                     gcd-cond$br-inputs
                                     gcd-cond$flag
                                     gcd-cond$data-in
                                     gcd1$input-format
                                     gcd1$valid-st
                                     gcd1$out-act
                                     gcd1$br-inputs)))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma gcd1)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for GCD1 that extracts the future output sequence
;; from the current state.

(defund gcd1$extract (st)
  (b* ((l0 (nth *gcd1$l0* st))
       (l1 (nth *gcd1$l1* st))
       (l2 (nth *gcd1$l2* st)))
    (gcd$op-map
     (extract-valid-data (list l1 l2 l0)))))

(defthm gcd1$extract-not-empty
  (implies (and (gcd1$out-act inputs st data-size)
                (gcd1$valid-st st data-size))
           (< 0 (len (gcd1$extract st))))
  :hints (("Goal"
           :in-theory (e/d (branch$act0
                            gcd-cond$br-inputs
                            gcd-cond$act0
                            gcd1$valid-st
                            gcd1$extract
                            gcd1$br-inputs
                            gcd1$out-act)
                           ())))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund gcd1$inv (st)
    (b* ((s (nth *gcd1$s* st))
         (s.s (nth *link1$s* s))
         (s.d (nth *link1$d* s)))
      (if (and (fullp s.s) (not (car s.d)))
          (= (len (gcd1$extract st))
             0)
        (= (len (gcd1$extract st))
           1))))

  (local
   (defthm gcd1$input-format-lemma-1
     (implies (gcd1$input-format inputs data-size)
              (booleanp (nth 0 inputs)))
     :hints (("Goal" :in-theory (enable gcd1$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm gcd1$input-format-lemma-2
     (implies (gcd1$input-format inputs data-size)
              (booleanp (nth 1 inputs)))
     :hints (("Goal" :in-theory (enable gcd1$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm gcd1$input-format-lemma-3
     (implies (and (gcd1$input-format inputs data-size)
                   (nth 0 inputs))
              (bvp (gcd1$data-in inputs data-size)))
     :hints (("Goal" :in-theory (enable gcd1$input-format)))))

  (local
   (defthm booleanp-gcd1$body-act
     (b* ((body-inputs (gcd1$body-inputs inputs st data-size))
          (l1 (nth *gcd1$l1* st))
          (l1.d (nth *link$d* l1)))
       (implies (or (equal (nth *link$s*
                                (nth *gcd1$l1* st))
                           '(nil))
                    (and (equal (nth *link$s*
                                     (nth *gcd1$l1* st))
                                '(t))
                         (equal (nth *link$s*
                                     (nth *gcd1$l2* st))
                                '(nil))
                         (equal (len l1.d) (* 2 data-size))
                         (bvp (strip-cars l1.d))))
                (booleanp (gcd-body1$act body-inputs data-size))))
     :hints (("Goal" :in-theory (enable merge$act0
                                        merge$act1
                                        merge$act
                                        gcd-body1$data-in
                                        gcd-body1$me-inputs
                                        gcd-body1$act
                                        gcd-body1$a<b
                                        gcd1$body-inputs)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm gcd1$body-act-inactive
     (b* ((body-inputs (gcd1$body-inputs inputs st data-size)))
       (implies (or (equal (nth *link$s*
                                (nth *gcd1$l1* st))
                           '(nil))
                    (equal (nth *link$s*
                                (nth *gcd1$l2* st))
                           '(t)))
                (not (gcd-body1$act body-inputs data-size))))
     :hints (("Goal" :in-theory (enable gcd1$body-inputs)))))

  (defthm gcd1$inv-preserved
    (implies (and (gcd1$input-format inputs data-size)
                  (gcd1$valid-st st data-size)
                  (gcd1$inv st))
             (gcd1$inv (gcd1$step inputs st data-size)))
    :hints (("Goal"
             :in-theory (e/d (f-sr
                              gcd1$valid-st
                              gcd1$st-format
                              gcd1$inv
                              gcd1$step
                              gcd1$extract
                              gcd1$br-inputs
                              gcd1$me-inputs
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

;; The extracted next-state function for GCD1.  Note that this function avoids
;; exploring the internal computation of GCD1.

(defund gcd1$extracted-step (inputs st data-size)
  (b* ((data (gcd$op (gcd1$data-in inputs data-size)))
       (extracted-st (gcd1$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (gcd1$out-act inputs st data-size) t)
      (cond
       ((equal (gcd1$in-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (gcd1$in-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

;; This property characterizes the one-step update on the future output
;; sequence given the current inputs and current state.  The trick here is to
;; apply the extraction function gcd1$extract to the step function gcd1$step so
;; that the one-step update on the future output sequence can be expressed in
;; terms of the gcd1$extracted-step function, which abstracts away the internal
;; computation of GCD1.

(progn
  (local
   (defthm gcd-body1$data-out-expand
     (b* ((body-inputs (gcd1$body-inputs inputs st data-size))
          (l1 (nth *gcd1$l1* st))
          (l1.d (nth *link$d* l1)))
       (implies
        (and (natp data-size)
             (equal (len l1.d) (* 2 data-size))
             (bvp (strip-cars l1.d)))
        (equal (gcd-body1$data-out body-inputs data-size)
               (v-if (v-< nil t
                          (rev (take data-size (strip-cars l1.d)))
                          (rev (nthcdr data-size (strip-cars l1.d))))
                     (append
                      (v-adder-output
                       t
                       (nthcdr data-size (strip-cars l1.d))
                       (v-not (take data-size (strip-cars l1.d))))
                      (take data-size (strip-cars l1.d)))
                     (append
                      (v-adder-output
                       t
                       (take data-size (strip-cars l1.d))
                       (v-not (nthcdr data-size (strip-cars l1.d))))
                      (nthcdr data-size (strip-cars l1.d)))))))
     :hints (("Goal"
              :in-theory (enable gcd-body1$data-in
                                 gcd-body1$a<b
                                 gcd-body1$data-out
                                 gcd-body1$data0-out
                                 gcd-body1$data1-out
                                 gcd1$body-inputs)))))

  (defthm gcd1$extracted-step-correct
    (b* ((next-st (gcd1$step inputs st data-size)))
      (implies (and (gcd1$input-format inputs data-size)
                    (gcd1$valid-st st data-size)
                    (gcd1$inv st))
               (equal (gcd1$extract next-st)
                      (gcd1$extracted-step inputs st data-size))))
    :hints (("Goal"
             :in-theory (e/d (f-sr
                              joint-act
                              gcd1$extracted-step
                              gcd1$valid-st
                              gcd1$st-format
                              gcd1$inv
                              gcd1$step
                              gcd1$in-act
                              gcd1$out-act
                              gcd1$data-out
                              gcd1$br-inputs
                              gcd1$me-inputs
                              gcd1$extract
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

;; Prove that gcd1$valid-st is an invariant.

(defthm gcd1$valid-st-preserved
  (implies (and (gcd1$input-format inputs data-size)
                (gcd1$valid-st st data-size))
           (gcd1$valid-st (gcd1$step inputs st data-size)
                         data-size))
  :hints (("Goal"
           :in-theory (e/d (f-sr
                            joint-act
                            gcd1$valid-st
                            gcd1$st-format
                            gcd1$step
                            gcd1$br-inputs
                            gcd1$me-inputs
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

(defthm gcd1$extract-lemma
  (implies (and (gcd1$valid-st st data-size)
                (gcd1$out-act inputs st data-size))
           (equal (list (gcd1$data-out inputs st data-size))
                  (nthcdr (1- (len (gcd1$extract st)))
                          (gcd1$extract st))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (branch$act0
                            gcd-cond$data-in
                            gcd-cond$br-inputs
                            gcd-cond$act0
                            gcd-cond$flag
                            gcd-cond$data0-out
                            gcd1$valid-st
                            gcd1$extract
                            gcd$op
                            gcd1$br-inputs
                            gcd1$out-act
                            gcd1$data-out)
                           (v-if-works)))))

;; Extract the accepted input sequence

(seq-gen gcd1 in in-act 0
         (gcd1$data-in inputs data-size))

;; Extract the valid output sequence

(seq-gen gcd1 out out-act 1
         (gcd1$data-out inputs st data-size)
         :netlist-data (nthcdr 2 outputs))

;; The multi-step input-output relationship

(in-out-stream-lemma gcd1 :op gcd$op :inv t)

