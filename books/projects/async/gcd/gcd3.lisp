;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "gcd-body3")
(include-book "gcd-cond")
(include-book "gcd-spec")
(include-book "../merge")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of GCD3
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of GCD3
;;
;; Construct the DE module generator GCD3 that computes the Greatest Common
;; Divisor of two natural numbers.  GCD3 contains submodule GCD-BODY3, which in
;; turn contains the self-timed serial subtractor SERIAL-SUB as a submodule.

(defconst *gcd3$go-num* (+ *merge$go-num*
                           *gcd-cond$go-num*
                           *gcd-body3$go-num*))

(defun gcd3$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (* 2 (mbe :logic (nfix data-size)
                 :exec  data-size))))

(defun gcd3$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (gcd3$data-ins-len data-size)
     *gcd3$go-num*))

;; DE module generator of GCD3

(module-generator
 gcd3* (data-size)
 ;; MODULE'S NAME
 (si 'gcd3 data-size)
 ;; INPUTS
 ;; There are 3 types of inputs for a complex joint:
 ;; * full-in and empty-out- signals,
 ;; * input data,
 ;; * GO signals.
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 (* 2 data-size))
                                     (sis 'go 0 *gcd3$go-num*)))
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
        (si 'gcd-body3 data-size)
        (list* 'l1-status 'l2-status
               (append (sis 'd1-out 0 (* 2 data-size))
                       (sis 'go 2 *gcd-body3$go-num*)))))

 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'gcd3 '(s l0 l1 l2 body) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; GCD3.

(defund gcd3$netlist (data-size cnt-size)
  (declare (xargs :guard (and (natp data-size)
                              (<= 2 data-size)
                              (natp cnt-size)
                              (<= 3 cnt-size))))
  (cons (gcd3* data-size)
        (union$ (link1$netlist)
                (gcd-cond$netlist data-size)
                (gcd-body3$netlist data-size cnt-size)
                (merge$netlist (* 2 data-size))
                :test 'equal)))

;; Recognizer for GCD3

(defund gcd3& (netlist data-size cnt-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size)
                              (<= 2 data-size)
                              (natp cnt-size)
                              (<= 3 cnt-size))))
  (b* ((subnetlist (delete-to-eq (si 'gcd3 data-size) netlist)))
    (and (equal (assoc (si 'gcd3 data-size) netlist)
                (gcd3* data-size))
         (link1& subnetlist)
         (link& subnetlist (* 2 data-size))
         (gcd-cond& subnetlist data-size)
         (gcd-body3& subnetlist data-size cnt-size)
         (merge& subnetlist (* 2 data-size)))))

;; Sanity check

(local
 (defthmd check-gcd3$netlist-64-7
   (and (net-syntax-okp (gcd3$netlist 64 7))
        (net-arity-okp (gcd3$netlist 64 7))
        (gcd3& (gcd3$netlist 64 7) 64 7))))

;; Constraints on the state of GCD3

(defund gcd3$st-format (st data-size cnt-size)
  (b* ((l0 (nth *gcd3$l0* st))
       (l1 (nth *gcd3$l1* st))
       (l2 (nth *gcd3$l2* st))
       (body (nth *gcd3$body* st)))
    (and (<= 3 data-size)
         (link$st-format l0 (* 2 data-size))
         (link$st-format l1 (* 2 data-size))
         (link$st-format l2 (* 2 data-size))
         (gcd-body3$st-format body data-size cnt-size))))

(defthm gcd3$st-format=>constraint
  (implies (gcd3$st-format st data-size cnt-size)
           (and (natp data-size)
                (<= 3 data-size)
                (natp cnt-size)
                (<= 4 cnt-size)))
  :hints (("Goal" :in-theory (enable gcd3$st-format)))
  :rule-classes :forward-chaining)

(defund gcd3$valid-st (st data-size cnt-size)
  (b* ((s  (nth *gcd3$s* st))
       (l0 (nth *gcd3$l0* st))
       (l1 (nth *gcd3$l1* st))
       (l2 (nth *gcd3$l2* st))
       (body (nth *gcd3$body* st)))
    (and (<= 3 data-size)
         (link1$valid-st s)
         (link$valid-st l0 (* 2 data-size))
         (link$valid-st l1 (* 2 data-size))
         (link$valid-st l2 (* 2 data-size))
         (gcd-body3$valid-st body data-size cnt-size))))

(defthmd gcd3$valid-st=>constraint
  (implies (gcd3$valid-st st data-size cnt-size)
           (and (natp data-size)
                (<= 3 data-size)
                (natp cnt-size)
                (<= 4 cnt-size)))
  :hints (("Goal" :in-theory (enable gcd-body3$valid-st=>constraint
                                     gcd3$valid-st)))
  :rule-classes :forward-chaining)

(defthmd gcd3$valid-st=>st-format
  (implies (gcd3$valid-st st data-size cnt-size)
           (gcd3$st-format st data-size cnt-size))
  :hints (("Goal" :in-theory (e/d (gcd-body3$valid-st=>st-format
                                   gcd3$st-format
                                   gcd3$valid-st)
                                  ()))))

;; Extract the input and output signals for GCD3

(progn
  ;; Extract the input data

  (defun gcd3$data-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (* 2 (mbe :logic (nfix data-size)
                    :exec  data-size))
          (nthcdr 2 inputs)))

  (defthm len-gcd3$data-in
    (equal (len (gcd3$data-in inputs data-size))
           (* 2 (nfix data-size))))

  (in-theory (disable gcd3$data-in))

  ;; Extract the inputs for the merge-in joint

  (defund gcd3$me-inputs (inputs st data-size)
    (b* ((full-in (nth 0 inputs))
         (data-in (gcd3$data-in inputs data-size))
         (go-signals (nthcdr (gcd3$data-ins-len data-size) inputs))

         (me-go-signals (take *merge$go-num* go-signals))

         (s (nth *gcd3$s* st))
         (s.s (nth *link1$s* s))
         (s.d (nth *link1$d* s))
         (l0 (nth *gcd3$l0* st))
         (l0.s (nth *link$s* l0))
         (l2 (nth *gcd3$l2* st))
         (l2.s (nth *link$s* l2))
         (l2.d (nth *link$d* l2))

         (me-full-in0 (f-and full-in (car s.s)))
         (me-full-in1 (f-and (car l2.s) (car s.s))))

      (list* me-full-in0 me-full-in1 (car l0.s) (car s.d)
             (append data-in
                     (v-threefix (strip-cars l2.d))
                     me-go-signals))))

  ;; Extract the inputs for the branch-out joint

  (defund gcd3$br-inputs (inputs st data-size)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (gcd3$data-ins-len data-size) inputs))

         (br-go-signals (take *gcd-cond$go-num*
                              (nthcdr *merge$go-num* go-signals)))

         (s (nth *gcd3$s* st))
         (s.s (nth *link1$s* s))
         (l0 (nth *gcd3$l0* st))
         (l0.s (nth *link$s* l0))
         (l0.d (nth *link$d* l0))
         (l1 (nth *gcd3$l1* st))
         (l1.s (nth *link$s* l1))

         (br-empty-out0- (f-or empty-out- (car s.s)))
         (br-empty-out1- (f-or (car l1.s) (car s.s))))

      (list* (f-buf (car l0.s)) br-empty-out0- br-empty-out1-
             (append (v-threefix (strip-cars l0.d))
                     br-go-signals))))

  ;; Extract the inputs for the "body" joint

  (defund gcd3$body-inputs (inputs st data-size)
    (b* ((go-signals (nthcdr (gcd3$data-ins-len data-size) inputs))

         (body-go-signals (take *gcd-body3$go-num*
                                (nthcdr (+ *merge$go-num*
                                           *gcd-cond$go-num*)
                                        go-signals)))

         (l1 (nth *gcd3$l1* st))
         (l1.s (nth *link$s* l1))
         (l1.d (nth *link$d* l1))
         (l2 (nth *gcd3$l2* st))
         (l2.s (nth *link$s* l2)))

      (list* (f-buf (car l1.s)) (f-buf (car l2.s))
             (append (v-threefix (strip-cars l1.d))
                     body-go-signals))))

  ;; Extract the "in-act" signal

  (defund gcd3$in-act (inputs st data-size)
    (merge$act0 (gcd3$me-inputs inputs st data-size)
                (* 2 data-size)))

  (defthm gcd3$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (gcd3$in-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable gcd3$me-inputs
                                       gcd3$in-act))))

  ;; Extract the "out-act" signal

  (defund gcd3$out-act (inputs st data-size)
    (gcd-cond$act0 (gcd3$br-inputs inputs st data-size)
                         data-size))

  (defthm gcd3$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (gcd3$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable gcd3$br-inputs
                                       gcd3$out-act))))

  ;; Extract the output data

  (defund gcd3$data-out (inputs st data-size)
    (gcd-cond$data0-out (gcd3$br-inputs inputs st data-size)
                              data-size))

  (defthm len-gcd3$data-out-1
    (implies (gcd3$st-format st data-size cnt-size)
             (equal (len (gcd3$data-out inputs st data-size))
                    data-size))
    :hints (("Goal" :in-theory (enable gcd3$st-format
                                       gcd3$data-out))))

  (defthm len-gcd3$data-out-2
    (implies (gcd3$valid-st st data-size cnt-size)
             (equal (len (gcd3$data-out inputs st data-size))
                    data-size))
    :hints (("Goal" :in-theory (enable gcd-body3$valid-st=>constraint
                                       gcd3$valid-st
                                       gcd3$data-out))))

  (defthm bvp-gcd3$data-out
    (implies (and (gcd3$valid-st st data-size cnt-size)
                  (gcd3$out-act inputs st data-size))
             (bvp (gcd3$data-out inputs st data-size)))
    :hints (("Goal" :in-theory (enable gcd-body3$valid-st=>constraint
                                       gcd3$valid-st
                                       gcd3$out-act
                                       gcd3$data-out
                                       gcd3$br-inputs
                                       gcd-cond$br-inputs
                                       gcd-cond$act0
                                       gcd-cond$data-in
                                       branch$act0))))

  (defun gcd3$outputs (inputs st data-size)
    (list* (gcd3$in-act inputs st data-size)
           (gcd3$out-act inputs st data-size)
           (gcd3$data-out inputs st data-size)))
  )

;; The value lemma for GCD3

(defthm gcd3$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (gcd3& netlist data-size cnt-size)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-size))
                  (true-listp go-signals)
                  (equal (len go-signals) *gcd3$go-num*)
                  (gcd3$st-format st data-size cnt-size))
             (equal (se (si 'gcd3 data-size) inputs st netlist)
                    (gcd3$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'gcd3 data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            gcd3&
                            gcd3*$destructure
                            merge$act0
                            gcd3$st-format
                            gcd3$in-act
                            gcd3$out-act
                            gcd3$data-out
                            gcd3$br-inputs
                            gcd3$me-inputs)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of GCD3.

(defun gcd3$step (inputs st data-size cnt-size)
  (b* ((data-in (gcd3$data-in inputs data-size))

       (s (nth *gcd3$s* st))
       (s.d (nth *link1$d* s))
       (l0 (nth *gcd3$l0* st))
       (l1 (nth *gcd3$l1* st))
       (l2 (nth *gcd3$l2* st))
       (l2.d (nth *link$d* l2))
       (body (nth *gcd3$body* st))

       (me-inputs (gcd3$me-inputs inputs st data-size))
       (br-inputs (gcd3$br-inputs inputs st data-size))
       (body-inputs (gcd3$body-inputs inputs st data-size))

       (d1-in (gcd-cond$data1-out br-inputs data-size))
       (d2-in (gcd-body3$data-out body))

       (done- (gcd-cond$flag br-inputs data-size))
       (merge-act1 (merge$act1 me-inputs (* 2 data-size)))
       (merge-act (merge$act me-inputs (* 2 data-size)))
       (branch-act1 (gcd-cond$act1 br-inputs data-size))
       (branch-act (gcd-cond$act br-inputs data-size))
       (body-in-act (gcd-body3$in-act body-inputs body data-size))
       (body-out-act (gcd-body3$out-act body-inputs body data-size))

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
     (gcd-body3$step body-inputs body data-size cnt-size))))

;; The state lemma for GCD3

(defthm gcd3$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (gcd3& netlist data-size cnt-size)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-size))
                  (true-listp go-signals)
                  (equal (len go-signals) *gcd3$go-num*)
                  (gcd3$st-format st data-size cnt-size))
             (equal (de (si 'gcd3 data-size) inputs st netlist)
                    (gcd3$step inputs st data-size cnt-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'gcd3 data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            gcd3&
                            gcd3*$destructure
                            merge$act
                            merge$act0
                            merge$act1
                            gcd3$st-format
                            gcd3$data-in
                            gcd3$br-inputs
                            gcd3$me-inputs
                            gcd3$body-inputs)
                           (de-module-disabled-rules)))))

(in-theory (disable gcd3$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund gcd3$input-format (inputs data-size)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-size))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (gcd3$data-in inputs data-size))
       (go-signals (nthcdr (gcd3$data-ins-len data-size) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *gcd3$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(local
 (defthm gcd3$input-format=>body$input-format
   (implies (and (gcd3$input-format inputs data-size)
                 (gcd3$valid-st st data-size cnt-size))
            (gcd-body3$input-format
             (gcd3$body-inputs inputs st data-size)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (gcd-body3$input-format
                             gcd-body3$data-in
                             gcd-body3$valid-st=>constraint
                             gcd3$input-format
                             gcd3$valid-st
                             gcd3$body-inputs)
                            ())))))

(defthm booleanp-gcd3$in-act
  (implies (and (gcd3$input-format inputs data-size)
                (gcd3$valid-st st data-size cnt-size))
           (booleanp (gcd3$in-act inputs st data-size)))
  :hints (("Goal" :in-theory (enable merge$act0
                                     gcd3$input-format
                                     gcd3$valid-st
                                     gcd3$in-act
                                     gcd3$me-inputs)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-gcd3$out-act
  (implies (and (gcd3$input-format inputs data-size)
                (gcd3$valid-st st data-size cnt-size))
           (booleanp (gcd3$out-act inputs st data-size)))
  :hints (("Goal" :in-theory (e/d (branch$act0
                                   gcd-cond$act0
                                   gcd-cond$br-inputs
                                   gcd-cond$flag
                                   gcd-cond$data-in
                                   gcd3$input-format
                                   gcd3$valid-st
                                   gcd3$out-act
                                   gcd3$br-inputs)
                                  (b-gates))))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma gcd3 :sizes (data-size cnt-size))

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for GCD3 that extracts the future output
;; sequence from the current state.

(defund gcd3$extract (st data-size)
  (b* ((l0 (nth *gcd3$l0* st))
       (l1 (nth *gcd3$l1* st))
       (l2 (nth *gcd3$l2* st))
       (body (nth *gcd3$body* st)))
    (gcd$op-map
     (append (extract-valid-data (list l0 l1 l2))
             (gcd-body3$extract body data-size)))))

(defthm gcd3$extract-not-empty
  (implies (and (gcd3$out-act inputs st data-size)
                (gcd3$valid-st st data-size cnt-size))
           (< 0 (len (gcd3$extract st data-size))))
  :hints (("Goal"
           :in-theory (e/d (branch$act0
                            gcd-cond$br-inputs
                            gcd-cond$act0
                            gcd3$valid-st
                            gcd3$extract
                            gcd3$br-inputs
                            gcd3$out-act)
                           (nfix))))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund gcd3$inv (st data-size)
    (b* ((s (nth *gcd3$s* st))
         (s.s (nth *link1$s* s))
         (s.d (nth *link1$d* s))
         (body (nth *gcd3$body* st)))
      (and (if (and (fullp s.s) (not (car s.d)))
               (= (len (gcd3$extract st data-size))
                  0)
             (= (len (gcd3$extract st data-size))
                1))
           (gcd-body3$inv body data-size))))

  (local
   (defthm gcd3$input-format-lemma-1
     (implies (gcd3$input-format inputs data-size)
              (booleanp (nth 0 inputs)))
     :hints (("Goal" :in-theory (enable gcd3$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm gcd3$input-format-lemma-2
     (implies (gcd3$input-format inputs data-size)
              (booleanp (nth 1 inputs)))
     :hints (("Goal" :in-theory (enable gcd3$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm gcd3$input-format-lemma-3
     (implies (and (gcd3$input-format inputs data-size)
                   (nth 0 inputs))
              (bvp (gcd3$data-in inputs data-size)))
     :hints (("Goal" :in-theory (enable gcd3$input-format)))))

  (local
   (defthm gcd3$body-in-act-inactive
     (b* ((l1 (nth *gcd3$l1* st))
          (l1.s (nth *link$s* l1))
          (body-inputs (gcd3$body-inputs inputs st data-size))
          (body (nth *gcd3$body* st)))
       (implies (emptyp l1.s)
                (not (gcd-body3$in-act body-inputs body data-size))))
     :hints (("Goal" :in-theory (enable gcd3$body-inputs)))))

  (defthm gcd3$inv-preserved
    (implies (and (gcd3$input-format inputs data-size)
                  (gcd3$valid-st st data-size cnt-size)
                  (gcd3$inv st data-size))
             (gcd3$inv (gcd3$step inputs st data-size cnt-size)
                            data-size))
    :hints (("Goal"
             :use gcd3$input-format=>body$input-format
             :in-theory (e/d (f-sr
                              gcd-body3$extracted-step
                              gcd3$valid-st
                              gcd3$inv
                              gcd3$step
                              gcd3$extract
                              gcd3$br-inputs
                              gcd3$me-inputs
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
                             (gcd3$input-format=>body$input-format
                              b-nor3)))))
  )

;; The extracted next-state function for GCD3.  Note that this function
;; avoids exploring the internal computation of GCD3.

(defund gcd3$extracted-step (inputs st data-size)
  (b* ((data (gcd$op (gcd3$data-in inputs data-size)))
       (extracted-st (gcd3$extract st data-size))
       (n (1- (len extracted-st))))
    (cond
     ((equal (gcd3$out-act inputs st data-size) t)
      (cond
       ((equal (gcd3$in-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (gcd3$in-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

;; This property characterizes the one-step update on the future output
;; sequence given the current inputs and current state.  The trick here is to
;; apply the extraction function gcd3$extract to the step function
;; gcd3$step so that the one-step update on the future output sequence can
;; be expressed in terms of the gcd3$extracted-step function, which
;; abstracts away the internal computation of GCD3.

(local
 (defthm gcd3-aux
   (implies (equal (len (gcd-body3$extract st data-size))
                   0)
            (not (gcd-body3$extract st data-size)))
   :hints (("Goal" :in-theory (enable len-0-is-atom)))))

(encapsulate
  ()

  (local
   (defthm gcd3$body-data-in-rewrite
     (b* ((l1 (nth *gcd3$l1* st))
          (l1.d (nth *link$d* l1))
          (body-inputs (gcd3$body-inputs inputs st data-size)))
       (implies (and (natp data-size)
                     (equal (len l1.d) (* 2 data-size)))
                (equal (gcd-body3$data-in body-inputs data-size)
                       (v-threefix (strip-cars l1.d)))))
     :hints (("Goal" :in-theory (enable gcd-body3$data-in
                                        gcd3$body-inputs)))))

  (local
   (defthm gcd$op-of-gcd-body3$op
     (implies (and (natp (/ (len x) 2))
                   (bvp x))
              (equal (gcd$op (gcd-body3$op x))
                     (gcd$op x)))
     :hints (("Goal"
              :use (:instance gcd$op-lemma
                              (data-size (/ (len x) 2)))
              :in-theory (e/d (serial-sub$op
                               gcd-body3$op
                               gcd$op-commutative)
                              (gcd$op-lemma))))))

  (defthm gcd3$extracted-step-correct
    (b* ((next-st (gcd3$step inputs st data-size cnt-size)))
      (implies (and (gcd3$input-format inputs data-size)
                    (gcd3$valid-st st data-size cnt-size)
                    (gcd3$inv st data-size))
               (equal (gcd3$extract next-st data-size)
                      (gcd3$extracted-step inputs st data-size))))
    :hints (("Goal"
             :use gcd3$input-format=>body$input-format
             :in-theory (e/d (f-sr
                              joint-act
                              fv-if-rewrite
                              gcd-body3$valid-st=>constraint
                              gcd-body3$extracted-step
                              gcd3$extracted-step
                              gcd3$valid-st
                              gcd3$inv
                              gcd3$step
                              gcd3$in-act
                              gcd3$out-act
                              gcd3$br-inputs
                              gcd3$me-inputs
                              gcd3$extract
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
                             (gcd3$input-format=>body$input-format
                              v-if-works
                              b-nor3)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that gcd3$valid-st is an invariant.

(encapsulate
  ()

  (local
   (defthm gcd3$body-out-act-inactive
     (b* ((l2 (nth *gcd3$l2* st))
          (l2.s (nth *link$s* l2))
          (body-inputs (gcd3$body-inputs inputs st data-size))
          (body (nth *gcd3$body* st)))
       (implies (fullp l2.s)
                (not (gcd-body3$out-act body-inputs body data-size))))
     :hints (("Goal" :in-theory (enable gcd3$body-inputs)))))

  (defthm gcd3$valid-st-preserved
    (implies (and (gcd3$input-format inputs data-size)
                  (gcd3$valid-st st data-size cnt-size))
             (gcd3$valid-st
              (gcd3$step inputs st data-size cnt-size)
              data-size
              cnt-size))
    :hints (("Goal"
             :use gcd3$input-format=>body$input-format
             :in-theory (e/d (f-sr
                              joint-act
                              gcd-body3$valid-st=>constraint
                              gcd3$valid-st
                              gcd3$step
                              gcd3$br-inputs
                              gcd3$me-inputs
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
                             (gcd3$input-format=>body$input-format
                              b-nor3)))))
  )

(defthm gcd3$extract-lemma
  (implies (and (gcd3$valid-st st data-size cnt-size)
                (gcd3$inv st data-size)
                (gcd3$out-act inputs st data-size))
           (equal (list (gcd3$data-out inputs st data-size))
                  (nthcdr (1- (len (gcd3$extract st data-size)))
                          (gcd3$extract st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (branch$act0
                            gcd-cond$data-in
                            gcd-cond$br-inputs
                            gcd-cond$act0
                            gcd-cond$flag
                            gcd-cond$data0-out
                            gcd-body3$valid-st=>constraint
                            gcd3$valid-st
                            gcd3$inv
                            gcd3$extract
                            gcd$op
                            gcd3$br-inputs
                            gcd3$out-act
                            gcd3$data-out)
                           (v-if-works
                            nfix)))))

;; Extract the accepted input sequence

(seq-gen gcd3 in in-act 0
         (gcd3$data-in inputs data-size)
         :sizes (data-size cnt-size))

;; Extract the valid output sequence

(seq-gen gcd3 out out-act 1
         (gcd3$data-out inputs st data-size)
         :netlist-data (nthcdr 2 outputs)
         :sizes (data-size cnt-size))

;; The multi-step input-output relationship

(encapsulate
  ()

  (local
   (defthm gcd3$dataflow-correct-aux
     (implies (equal (append x y1)
                     (append (gcd$op-map seq) y2))
              (equal (append x y1 z)
                     (append (gcd$op-map seq)
                             y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (associativity-of-append))))))

  (defthmd gcd3$dataflow-correct
    (b* ((extracted-st (gcd3$extract st data-size))
         (final-st (gcd3$run
                    inputs-seq st data-size cnt-size n))
         (final-extracted-st (gcd3$extract final-st data-size)))
      (implies
       (and (gcd3$input-format-n inputs-seq data-size n)
            (gcd3$valid-st st data-size cnt-size)
            (gcd3$inv st data-size))
       (equal (append final-extracted-st
                      (gcd3$out-seq
                       inputs-seq st data-size cnt-size n))
              (append (gcd$op-map
                       (gcd3$in-seq
                        inputs-seq st data-size cnt-size n))
                      extracted-st))))
    :hints (("Goal"
             :in-theory (enable gcd3$extracted-step))))

  (defthmd gcd3$functionally-correct
    (b* ((extracted-st (gcd3$extract st data-size))
         (final-st (de-n (si 'gcd3 data-size)
                         inputs-seq st netlist n))
         (final-extracted-st (gcd3$extract final-st data-size)))
      (implies
       (and (gcd3& netlist data-size cnt-size)
            (gcd3$input-format-n inputs-seq data-size n)
            (gcd3$valid-st st data-size cnt-size)
            (gcd3$inv st data-size))
       (equal (append final-extracted-st
                      (gcd3$out-seq-netlist
                       inputs-seq st netlist data-size n))
              (append (gcd$op-map
                       (gcd3$in-seq-netlist
                        inputs-seq st netlist data-size n))
                      extracted-st))))
    :hints (("Goal"
             :use gcd3$dataflow-correct
             :in-theory (enable gcd3$valid-st=>st-format
                                gcd3$de-n))))
  )

