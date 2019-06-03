;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "comp-gcd-cond")
(include-book "gcd-body1")
(include-book "gcd-spec")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of COMP-GCD
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of COMP-GCD
;;
;; Construct a DE module generator that computes the Greatest Common Divisor
;; (COMP-GCD) of two natural numbers.  Prove the value and state lemmas for
;; this module generator.  We follow the link-joint model in building this
;; generator.

(defconst *comp-gcd$go-num* (+ *merge$go-num*
                                *comp-gcd-cond$go-num*
                                *gcd-body1$go-num*))

(defun comp-gcd$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (* 2 (mbe :logic (nfix data-size)
                 :exec  data-size))))

(defun comp-gcd$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (comp-gcd$data-ins-len data-size)
     *comp-gcd$go-num*))

;; DE module generator of COMP-GCD

(module-generator
 comp-gcd* (data-size)
 (si 'comp-gcd data-size)
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 (* 2 data-size))
                                     (sis 'go 0 *comp-gcd$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-size))
 '(s l0 l1 l2 br)
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
        (list* 'merge-act 'cond-in-act (sis 'd0-in 0 (* 2 data-size))))

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
  (list 'br
        (list* 'cond-in-act 'branch-act 'out-act 'branch-act1 'done-
               (append (sis 'data-out 0 data-size)
                       (sis 'd1-in 0 (* 2 data-size))))
        (si 'comp-gcd-cond data-size)
        (list* 'l0-status 'br-empty-out0- 'br-empty-out1-
               (append (sis 'd0-out 0 (* 2 data-size))
                       (sis 'go
                            *merge$go-num*
                            *comp-gcd-cond$go-num*))))

  ;; Body
  (list 'body
        (list* 'body-act
               (sis 'd2-in 0 (* 2 data-size)))
        (si 'gcd-body1 data-size)
        (list* 'l1-status 'l2-status
               (append (sis 'd1-out 0 (* 2 data-size))
                       (sis 'go
                            (+ *merge$go-num*
                               *comp-gcd-cond$go-num*)
                            *gcd-body1$go-num*)))))

 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'comp-gcd '(s l0 l1 l2 br) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; COMP-GCD.

(defund comp-gcd$netlist (data-size)
  (declare (xargs :guard (and (natp data-size)
                              (<= 2 data-size))))
  (cons (comp-gcd* data-size)
        (union$ (link1$netlist)
                (link$netlist (* 2 data-size))
                (comp-gcd-cond$netlist data-size)
                (gcd-body1$netlist data-size)
                :test 'equal)))

;; Recognizer for COMP-GCD

(defund comp-gcd& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size)
                              (<= 2 data-size))))
  (b* ((subnetlist (delete-to-eq (si 'comp-gcd data-size) netlist)))
    (and (equal (assoc (si 'comp-gcd data-size) netlist)
                (comp-gcd* data-size))
         (link1& subnetlist)
         (link& subnetlist (* 2 data-size))
         (comp-gcd-cond& subnetlist data-size)
         (gcd-body1& subnetlist data-size)
         (merge& subnetlist (* 2 data-size)))))

;; Sanity check

(local
 (defthmd check-comp-gcd$netlist-64
   (and (net-syntax-okp (comp-gcd$netlist 64))
        (net-arity-okp (comp-gcd$netlist 64))
        (comp-gcd& (comp-gcd$netlist 64) 64))))

;; Constraints on the state of COMP-GCD

(defund comp-gcd$st-format (st data-size)
  (b* ((l0 (nth *comp-gcd$l0* st))
       (l1 (nth *comp-gcd$l1* st))
       (l2 (nth *comp-gcd$l2* st))
       (br (nth *comp-gcd$br* st)))
    (and (link$st-format l0 (* 2 data-size))
         (link$st-format l1 (* 2 data-size))
         (link$st-format l2 (* 2 data-size))

         (comp-gcd-cond$st-format br data-size))))

(defthm comp-gcd$st-format=>constraint
  (implies (comp-gcd$st-format st data-size)
           (and (natp data-size)
                (<= 3 data-size)))
  :hints (("Goal"
           :in-theory (enable comp-gcd$st-format)))
  :rule-classes :forward-chaining)

(defund comp-gcd$valid-st (st data-size)
  (b* ((s (nth *comp-gcd$s* st))
       (l0 (nth *comp-gcd$l0* st))
       (l1 (nth *comp-gcd$l1* st))
       (l2 (nth *comp-gcd$l2* st))
       (br (nth *comp-gcd$br* st)))
    (and (link1$valid-st s)
         (link$valid-st l0 (* 2 data-size))
         (link$valid-st l1 (* 2 data-size))
         (link$valid-st l2 (* 2 data-size))

         (comp-gcd-cond$valid-st br data-size))))

(defthmd comp-gcd$valid-st=>constraint
  (implies (comp-gcd$valid-st st data-size)
           (and (natp data-size)
                (<= 3 data-size)))
  :hints (("Goal"
           :in-theory (enable comp-gcd-cond$valid-st=>constraint
                              comp-gcd$valid-st)))
  :rule-classes :forward-chaining)

(defthmd comp-gcd$valid-st=>st-format
  (implies (comp-gcd$valid-st st data-size)
           (comp-gcd$st-format st data-size))
  :hints (("Goal" :in-theory (e/d (comp-gcd-cond$valid-st=>st-format
                                   comp-gcd$st-format
                                   comp-gcd$valid-st)
                                  (link$st-format)))))

;; Extract the input and output signals for COMP-GCD

(progn
  ;; Extract the input data

  (defun comp-gcd$data-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (* 2 (mbe :logic (nfix data-size)
                    :exec  data-size))
          (nthcdr 2 inputs)))

  (defthm len-comp-gcd$data-in
    (equal (len (comp-gcd$data-in inputs data-size))
           (* 2 (nfix data-size))))

  (in-theory (disable comp-gcd$data-in))

  ;; Extract the inputs for the merge-in joint

  (defund comp-gcd$me-inputs (inputs st data-size)
    (b* ((full-in (nth 0 inputs))
         (data-in (comp-gcd$data-in inputs data-size))
         (go-signals (nthcdr (comp-gcd$data-ins-len data-size) inputs))

         (me-go-signals (take *merge$go-num* go-signals))

         (s (nth *comp-gcd$s* st))
         (s.s (nth *link1$s* s))
         (s.d (nth *link1$d* s))
         (l0 (nth *comp-gcd$l0* st))
         (l0.s (nth *link$s* l0))
         (l2 (nth *comp-gcd$l2* st))
         (l2.s (nth *link$s* l2))
         (l2.d (nth *link$d* l2))

         (me-full-in0 (f-and full-in (car s.s)))
         (me-full-in1 (f-and (car l2.s) (car s.s))))

      (list* me-full-in0 me-full-in1 (car l0.s) (car s.d)
             (append data-in
                     (v-threefix (strip-cars l2.d))
                     me-go-signals))))

  ;; Extract the inputs for the branch-out joint

  (defund comp-gcd$br-inputs (inputs st data-size)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (comp-gcd$data-ins-len data-size) inputs))

         (br-go-signals (take *comp-gcd-cond$go-num*
                              (nthcdr *merge$go-num* go-signals)))

         (s (nth *comp-gcd$s* st))
         (s.s (nth *link1$s* s))
         (l0 (nth *comp-gcd$l0* st))
         (l0.s (nth *link$s* l0))
         (l0.d (nth *link$d* l0))
         (l1 (nth *comp-gcd$l1* st))
         (l1.s (nth *link$s* l1))

         (br-empty-out0- (f-or empty-out- (car s.s)))
         (br-empty-out1- (f-or (car l1.s) (car s.s))))

      (list* (f-buf (car l0.s)) br-empty-out0- br-empty-out1-
             (append (v-threefix (strip-cars l0.d))
                     br-go-signals))))

  ;; Extract the inputs for the "body" joint

  (defund comp-gcd$body-inputs (inputs st data-size)
    (b* ((go-signals (nthcdr (comp-gcd$data-ins-len data-size) inputs))

         (body-go-signals (take *gcd-body1$go-num*
                                (nthcdr (+ *merge$go-num*
                                           *comp-gcd-cond$go-num*)
                                        go-signals)))

         (l1 (nth *comp-gcd$l1* st))
         (l1.s (nth *link$s* l1))
         (l1.d (nth *link$d* l1))
         (l2 (nth *comp-gcd$l2* st))
         (l2.s (nth *link$s* l2)))

      (list* (f-buf (car l1.s)) (f-buf (car l2.s))
             (append (v-threefix (strip-cars l1.d))
                     body-go-signals))))

  ;; Extract the "in-act" signal

  (defund comp-gcd$in-act (inputs st data-size)
    (merge$act0 (comp-gcd$me-inputs inputs st data-size)
                (* 2 data-size)))

  (defthm comp-gcd$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (comp-gcd$in-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-gcd$me-inputs
                                       comp-gcd$in-act))))

  ;; Extract the "out-act" signal

  (defund comp-gcd$out-act (inputs st data-size)
    (comp-gcd-cond$out-act0 (comp-gcd$br-inputs inputs st data-size)
                            (nth *comp-gcd$br* st)
                            data-size))

  (defthm comp-gcd$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (comp-gcd$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-gcd$br-inputs
                                       comp-gcd$out-act))))

  ;; Extract the output data

  (defund comp-gcd$data-out (inputs st data-size)
    (comp-gcd-cond$data0-out (comp-gcd$br-inputs inputs st data-size)
                             (nth *comp-gcd$br* st)
                             data-size))

  (defthm len-comp-gcd$data-out-1
    (implies (comp-gcd$st-format st data-size)
             (equal (len (comp-gcd$data-out inputs st data-size))
                    data-size))
    :hints (("Goal" :in-theory (enable comp-gcd$st-format
                                       comp-gcd$data-out))))

  (defthm len-comp-gcd$data-out-2
    (implies (comp-gcd$valid-st st data-size)
             (equal (len (comp-gcd$data-out inputs st data-size))
                    data-size))
    :hints (("Goal" :in-theory (enable comp-gcd$valid-st
                                       comp-gcd$data-out))))

  (defthm bvp-comp-gcd$data-out
    (implies (and (comp-gcd$valid-st st data-size)
                  (comp-gcd$out-act inputs st data-size))
             (bvp (comp-gcd$data-out inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-gcd$valid-st
                                       comp-gcd$out-act
                                       comp-gcd$data-out))))

  (defun comp-gcd$outputs (inputs st data-size)
    (list* (comp-gcd$in-act inputs st data-size)
           (comp-gcd$out-act inputs st data-size)
           (comp-gcd$data-out inputs st data-size)))
  )

;; The value lemma for COMP-GCD

(defthm comp-gcd$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (comp-gcd& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-size))
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-gcd$go-num*)
                  (comp-gcd$st-format st data-size))
             (equal (se (si 'comp-gcd data-size) inputs st netlist)
                    (comp-gcd$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'comp-gcd data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            comp-gcd-cond$st-format=>constraint
                            comp-gcd&
                            comp-gcd*$destructure
                            comp-gcd$data-in
                            merge$act0
                            comp-gcd$st-format
                            comp-gcd$in-act
                            comp-gcd$out-act
                            comp-gcd$data-out
                            comp-gcd$br-inputs
                            comp-gcd$me-inputs)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of COMP-GCD.

(defun comp-gcd$step (inputs st data-size)
  (b* ((data-in (comp-gcd$data-in inputs data-size))

       (s (nth *comp-gcd$s* st))
       (s.d (nth *link1$d* s))
       (l0 (nth *comp-gcd$l0* st))
       (l1 (nth *comp-gcd$l1* st))
       (l2 (nth *comp-gcd$l2* st))
       (l2.d (nth *link$d* l2))
       (br (nth *comp-gcd$br* st))

       (me-inputs (comp-gcd$me-inputs inputs st data-size))
       (br-inputs (comp-gcd$br-inputs inputs st data-size))
       (body-inputs (comp-gcd$body-inputs inputs st data-size))

       (d1-in (comp-gcd-cond$data1-out br-inputs br data-size))
       (d2-in (gcd-body1$data-out body-inputs data-size))

       (done- (comp-gcd-cond$flag br-inputs br data-size))
       (merge-act1 (merge$act1 me-inputs (* 2 data-size)))
       (merge-act (merge$act me-inputs (* 2 data-size)))
       (cond-in-act (comp-gcd-cond$in-act br-inputs br data-size))
       (branch-act1 (comp-gcd-cond$out-act1 br-inputs br data-size))
       (branch-act (comp-gcd-cond$out-act br-inputs br data-size))
       (body-act (gcd-body1$act body-inputs data-size))

       (s-inputs (list branch-act merge-act done-))
       (l0-inputs (list* merge-act cond-in-act
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
     (link$step l2-inputs l2 (* 2 data-size))

     ;; COMP-GCD-COND
     (comp-gcd-cond$step br-inputs br data-size))))

;; The state lemma for COMP-GCD

(defthm comp-gcd$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (comp-gcd& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-size))
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-gcd$go-num*)
                  (comp-gcd$st-format st data-size))
             (equal (de (si 'comp-gcd data-size) inputs st netlist)
                    (comp-gcd$step inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'comp-gcd data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            comp-gcd-cond$st-format=>constraint
                            comp-gcd&
                            comp-gcd*$destructure
                            merge$act
                            merge$act0
                            merge$act1
                            merge$value
                            comp-gcd$st-format
                            comp-gcd$data-in
                            comp-gcd$br-inputs
                            comp-gcd$me-inputs
                            comp-gcd$body-inputs)
                           (de-module-disabled-rules)))))

(in-theory (disable comp-gcd$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund comp-gcd$input-format (inputs data-size)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-size))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (comp-gcd$data-in inputs data-size))
       (go-signals (nthcdr (comp-gcd$data-ins-len data-size) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *comp-gcd$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(local
 (defthm comp-gcd$input-format=>br$input-format
   (implies (and (comp-gcd$input-format inputs data-size)
                 (comp-gcd$valid-st st data-size))
            (comp-gcd-cond$input-format
             (comp-gcd$br-inputs inputs st data-size)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (comp-gcd-cond$valid-st=>constraint
                             comp-gcd$input-format
                             comp-gcd-cond$input-format
                             comp-gcd-cond$data-in
                             comp-gcd$valid-st
                             comp-gcd$br-inputs)
                            ())))))

(defthm booleanp-comp-gcd$in-act
  (implies (and (comp-gcd$input-format inputs data-size)
                (comp-gcd$valid-st st data-size))
           (booleanp (comp-gcd$in-act inputs st data-size)))
  :hints (("Goal" :in-theory (enable merge$act0
                                     comp-gcd$input-format
                                     comp-gcd$valid-st
                                     comp-gcd$in-act
                                     comp-gcd$me-inputs)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-gcd$out-act
  (implies (and (comp-gcd$input-format inputs data-size)
                (comp-gcd$valid-st st data-size))
           (booleanp (comp-gcd$out-act inputs st data-size)))
  :hints (("Goal"
           :use comp-gcd$input-format=>br$input-format
           :in-theory (e/d (comp-gcd$valid-st
                            comp-gcd$out-act)
                           (comp-gcd$input-format=>br$input-format))))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma comp-gcd)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for COMP-GCD that extracts the future output
;; sequence from the current state.

(defund comp-gcd$extract (st)
  (b* ((l0 (nth *comp-gcd$l0* st))
       (l1 (nth *comp-gcd$l1* st))
       (l2 (nth *comp-gcd$l2* st))
       (br (nth *comp-gcd$br* st)))
    (gcd$op-map
     (append (extract-valid-data (list l1 l2 l0))
             (comp-gcd-cond$extract br)))))

(defthm comp-gcd$extract-not-empty
  (implies (and (comp-gcd$out-act inputs st data-size)
                (comp-gcd$valid-st st data-size))
           (< 0 (len (comp-gcd$extract st))))
  :hints (("Goal"
           :in-theory (e/d (comp-gcd$valid-st
                            comp-gcd$extract
                            comp-gcd$out-act)
                           ())))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund comp-gcd$inv (st)
    (b* ((s (nth *comp-gcd$s* st))
         (s.s (nth *link1$s* s))
         (s.d (nth *link1$d* s))
         (br (nth *comp-gcd$br* st)))
      (and (comp-gcd-cond$inv br)
           (if (and (fullp s.s) (not (car s.d)))
               (= (len (comp-gcd$extract st))
                  0)
             (= (len (comp-gcd$extract st))
                1)))))

  (local
   (defthm comp-gcd$input-format-lemma-1
     (implies (comp-gcd$input-format inputs data-size)
              (booleanp (nth 0 inputs)))
     :hints (("Goal" :in-theory (enable comp-gcd$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm comp-gcd$input-format-lemma-2
     (implies (comp-gcd$input-format inputs data-size)
              (booleanp (nth 1 inputs)))
     :hints (("Goal" :in-theory (enable comp-gcd$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm comp-gcd$input-format-lemma-3
     (implies (and (comp-gcd$input-format inputs data-size)
                   (nth 0 inputs))
              (bvp (comp-gcd$data-in inputs data-size)))
     :hints (("Goal" :in-theory (enable comp-gcd$input-format)))))

  (local
   (defthm comp-gcd-cond$in-act-inactive
     (implies (equal (nth *link$s*
                          (nth *comp-gcd$l0* st))
                     '(nil))
              (not (comp-gcd-cond$in-act
                    (comp-gcd$br-inputs inputs st data-size)
                    (nth *comp-gcd$br* st)
                    data-size)))
     :hints (("Goal" :in-theory (e/d (comp-gcd$br-inputs)
                                     ())))))

  (local
   (defthm comp-gcd-cond$out-act0-inactive
     (implies (equal (nth *link$s*
                          (nth *comp-gcd$s* st))
                     '(t))
              (not (comp-gcd-cond$out-act0
                    (comp-gcd$br-inputs inputs st data-size)
                    (nth *comp-gcd$br* st)
                    data-size)))
     :hints (("Goal" :in-theory (e/d (comp-gcd$br-inputs)
                                     ())))))

  (local
   (defthm comp-gcd-cond$out-act1-inactive
     (implies (or (equal (nth *link$s*
                              (nth *comp-gcd$s* st))
                         '(t))
                  (equal (nth *link$s*
                              (nth *comp-gcd$l1* st))
                         '(t)))
              (not (comp-gcd-cond$out-act1
                    (comp-gcd$br-inputs inputs st data-size)
                    (nth *comp-gcd$br* st)
                    data-size)))
     :hints (("Goal" :in-theory (e/d (comp-gcd$br-inputs)
                                     ())))))

  (local
   (defthm comp-gcd-cond$flag-inactive
     (implies (and (comp-gcd-cond$valid-st (nth *comp-gcd$br* st)
                                           data-size)
                   (comp-gcd-cond$out-act0
                    (comp-gcd$br-inputs inputs st data-size)
                    (nth *comp-gcd$br* st)
                    data-size))
              (not (comp-gcd-cond$flag
                    (comp-gcd$br-inputs inputs st data-size)
                    (nth *comp-gcd$br* st)
                    data-size)))
     :hints (("Goal" :in-theory (e/d (branch$act0
                                      gcd-cond$br-inputs
                                      gcd-cond$data-in
                                      gcd-cond$flag
                                      gcd-cond$act0
                                      comp-gcd$br-inputs
                                      comp-gcd-cond$valid-st
                                      comp-gcd-cond$br-inputs
                                      comp-gcd-cond$out-act0
                                      comp-gcd-cond$flag)
                                     (b-nor3))))))

  (local
   (defthm comp-gcd-cond$flag-active
     (implies (and (comp-gcd-cond$valid-st (nth *comp-gcd$br* st)
                                           data-size)
                   (comp-gcd-cond$out-act1
                    (comp-gcd$br-inputs inputs st data-size)
                    (nth *comp-gcd$br* st)
                    data-size))
              (equal (comp-gcd-cond$flag
                      (comp-gcd$br-inputs inputs st data-size)
                      (nth *comp-gcd$br* st)
                      data-size)
                     t))
     :hints (("Goal" :in-theory (e/d (branch$act1
                                      gcd-cond$br-inputs
                                      gcd-cond$data-in
                                      gcd-cond$flag
                                      gcd-cond$act1
                                      comp-gcd$br-inputs
                                      comp-gcd-cond$valid-st
                                      comp-gcd-cond$br-inputs
                                      comp-gcd-cond$out-act1
                                      comp-gcd-cond$flag)
                                     (b-nor3))))))

  (local
   (defthm booleanp-comp-gcd$body-act
     (b* ((body-inputs (comp-gcd$body-inputs inputs st data-size))
          (l1 (nth *comp-gcd$l1* st))
          (l1.d (nth *link$d* l1)))
       (implies (or (equal (nth *link$s*
                                (nth *comp-gcd$l1* st))
                           '(nil))
                    (and (equal (nth *link$s*
                                     (nth *comp-gcd$l1* st))
                                '(t))
                         (equal (nth *link$s*
                                     (nth *comp-gcd$l2* st))
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
                                        comp-gcd$body-inputs)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm comp-gcd$body-act-inactive
     (b* ((body-inputs (comp-gcd$body-inputs inputs st data-size)))
       (implies (or (equal (nth *link$s*
                                (nth *comp-gcd$l1* st))
                           '(nil))
                    (equal (nth *link$s*
                                (nth *comp-gcd$l2* st))
                           '(t)))
                (not (gcd-body1$act body-inputs data-size))))
     :hints (("Goal" :in-theory (enable comp-gcd$body-inputs)))))

  (local
   (defthm bvp-comp-gcd$body-data-out
     (b* ((body-inputs (comp-gcd$body-inputs inputs st data-size))
          (l1 (nth *comp-gcd$l1* st))
          (l1.d (nth *link$d* l1)))
       (implies (and (equal (len l1.d) (* 2 data-size))
                     (bvp (strip-cars l1.d)))
                (bvp (gcd-body1$data-out body-inputs data-size))))
     :hints (("Goal" :in-theory (enable gcd-body1$data-in
                                        comp-gcd$body-inputs)))))

  (defthm comp-gcd$inv-preserved
    (implies (and (comp-gcd$input-format inputs data-size)
                  (comp-gcd$valid-st st data-size)
                  (comp-gcd$inv st))
             (comp-gcd$inv (comp-gcd$step inputs st data-size)))
    :hints (("Goal"
             :use comp-gcd$input-format=>br$input-format
             :in-theory (e/d (f-sr
                              comp-gcd-cond$extracted-step
                              comp-gcd$valid-st
                              comp-gcd$inv
                              comp-gcd$step
                              comp-gcd$extract
                              comp-gcd$me-inputs
                              comp-gcd-cond$out-act
                              merge$act
                              merge$act0
                              merge$act1)
                             (comp-gcd$input-format=>br$input-format
                              nfix)))))
  )

;; The extracted next-state function for COMP-GCD.  Note that this function
;; avoids exploring the internal computation of COMP-GCD.

(defund comp-gcd$extracted-step (inputs st data-size)
  (b* ((data (gcd$op (comp-gcd$data-in inputs data-size)))
       (extracted-st (comp-gcd$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-gcd$out-act inputs st data-size) t)
      (cond
       ((equal (comp-gcd$in-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (comp-gcd$in-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm fv-if=v-if
     (implies (and (booleanp c)
                   (bvp a)
                   (bvp b)
                   (equal (len a) (len b)))
              (equal (fv-if c a b) (v-if c a b)))))

  (local
   (defthm comp-gcd$extracted-step-correct-aux-1
     (b* ((body-inputs (comp-gcd$body-inputs inputs st data-size))
          (l1 (nth *comp-gcd$l1* st))
          (l1.d (nth *link$d* l1)))
       (implies (and (natp data-size)
                     (equal (len l1.d) (* 2 data-size))
                     (bvp (strip-cars l1.d)))
                (equal
                 (gcd$op (gcd-body1$data-out body-inputs data-size))
                 (gcd$op (strip-cars l1.d)))))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d (gcd-body1$data-in
                               gcd-body1$a<b
                               gcd-body1$data-out
                               gcd-body1$data0-out
                               gcd-body1$data1-out
                               comp-gcd$body-inputs)
                              (v-if-works
                               v-not-take
                               v-not-nthcdr))))))

  (local
   (defthm comp-gcd$extracted-step-correct-aux-2
     (b* ((br-inputs (comp-gcd$br-inputs inputs st data-size))
          (l0 (nth *comp-gcd$l0* st))
          (l0.d (nth *link$d* l0)))
       (implies
        (and (natp data-size)
             (equal (len l0.d) (* 2 data-size))
             (bvp (strip-cars l0.d)))
        (equal (comp-gcd-cond$op
                (cons
                 (take data-size
                       (comp-gcd-cond$data-in br-inputs data-size))
                 (nthcdr data-size
                         (comp-gcd-cond$data-in br-inputs data-size))))
               (strip-cars l0.d))))
     :hints (("Goal" :in-theory (enable comp-gcd-cond$op
                                        comp-gcd-cond$data-in
                                        comp-gcd$br-inputs)))))

  (defthm comp-gcd$extracted-step-correct
    (b* ((next-st (comp-gcd$step inputs st data-size)))
      (implies (and (comp-gcd$input-format inputs data-size)
                    (comp-gcd$valid-st st data-size)
                    (comp-gcd$inv st))
               (equal (comp-gcd$extract next-st)
                      (comp-gcd$extracted-step inputs st data-size))))
    :hints (("Goal"
             :use comp-gcd$input-format=>br$input-format
             :in-theory (e/d (f-sr
                              joint-act
                              comp-gcd-cond$valid-st=>constraint
                              comp-gcd-cond$extracted-step
                              comp-gcd$extracted-step
                              comp-gcd$valid-st
                              comp-gcd$inv
                              comp-gcd$step
                              comp-gcd$in-act
                              comp-gcd$out-act
                              comp-gcd$data-out
                              comp-gcd$me-inputs
                              comp-gcd$extract
                              comp-gcd-cond$out-act
                              merge$act
                              merge$act0
                              merge$act1)
                             (comp-gcd$input-format=>br$input-format
                              nfix)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that comp-gcd$valid-st is an invariant.

(defthm comp-gcd$valid-st-preserved
  (implies (and (comp-gcd$input-format inputs data-size)
                (comp-gcd$valid-st st data-size))
           (comp-gcd$valid-st (comp-gcd$step inputs st data-size)
                              data-size))
  :hints (("Goal"
           :use comp-gcd$input-format=>br$input-format
           :in-theory (e/d (f-sr
                            joint-act
                            comp-gcd-cond$valid-st=>constraint
                            comp-gcd$valid-st
                            comp-gcd$step
                            comp-gcd$me-inputs
                            comp-gcd-cond$out-act
                            merge$act
                            merge$act0
                            merge$act1)
                           (comp-gcd$input-format=>br$input-format
                            nfix)))))

(encapsulate
  ()

  (local
   (defthm comp-gcd$extract-lemma-aux-1
     (implies (and (<= (len (comp-gcd-cond$extract st))
                       1)
                   (comp-gcd-cond$valid-st st data-size)
                   (comp-gcd-cond$inv st)
                   (comp-gcd-cond$out-act0 inputs st data-size))
              (equal (comp-gcd-cond$extract st)
                     (list (comp-gcd-cond$data1-out inputs st data-size))))
     :hints (("Goal"
              :in-theory (e/d (len-0-is-atom
                               branch$act0
                               gcd-cond$data-in
                               gcd-cond$br-inputs
                               gcd-cond$act0
                               gcd-cond$data1-out
                               comp-gcd-cond$op
                               comp-gcd-cond$valid-st
                               comp-gcd-cond$inv
                               comp-gcd-cond$extract
                               comp-gcd-cond$br-inputs
                               comp-gcd-cond$out-act0
                               comp-gcd-cond$data1-out)
                              (b-nor3
                               b-not
                               acl2::car-of-append))))))

  (local
   (defthm comp-gcd$extract-lemma-aux-2
     (implies (and (comp-gcd-cond$valid-st st data-size)
                   (comp-gcd-cond$out-act0 inputs st data-size))
              (equal (gcd$op
                      (comp-gcd-cond$data1-out inputs st data-size))
                     (comp-gcd-cond$data0-out inputs st data-size)))
     :hints (("Goal" :in-theory (enable branch$act0
                                        gcd-cond$data-in
                                        gcd-cond$br-inputs
                                        gcd-cond$act0
                                        gcd-cond$flag
                                        gcd-cond$data0-out
                                        gcd-cond$data1-out
                                        comp-gcd-cond$valid-st
                                        comp-gcd-cond$br-inputs
                                        comp-gcd-cond$out-act0
                                        comp-gcd-cond$data0-out
                                        comp-gcd-cond$data1-out
                                        gcd$op)))))

  (defthm comp-gcd$extract-lemma
    (implies (and (comp-gcd$valid-st st data-size)
                  (comp-gcd$inv st)
                  (comp-gcd$out-act inputs st data-size))
             (equal (list (comp-gcd$data-out inputs st data-size))
                    (nthcdr (1- (len (comp-gcd$extract st)))
                            (comp-gcd$extract st))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (comp-gcd$valid-st
                              comp-gcd$inv
                              comp-gcd$extract
                              comp-gcd$br-inputs
                              comp-gcd$out-act
                              comp-gcd$data-out)
                             (v-if-works
                              comp-gcd-cond$extract-lemma)))))
  )

;; Extract the accepted input sequence

(seq-gen comp-gcd in in-act 0
         (comp-gcd$data-in inputs data-size))

;; Extract the valid output sequence

(seq-gen comp-gcd out out-act 1
         (comp-gcd$data-out inputs st data-size)
         :netlist-data (nthcdr 2 outputs))

;; The multi-step input-output relationship

(in-out-stream-lemma comp-gcd :op gcd$op :inv t)

