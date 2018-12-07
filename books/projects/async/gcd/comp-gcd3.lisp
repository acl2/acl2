;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; December 2018

(in-package "ADE")

(include-book "comp-gcd-cond")
(include-book "gcd-body")

(local (include-book "gcd-alg"))

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of COMP-GCD3
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of COMP-GCD3
;;
;; Construct a DE module generator that computes the Greatest Common Divisor
;; (COMP-GCD3) of two natural numbers.  Prove the value and state lemmas for
;; this module generator.  We follow the link-joint model in building this
;; generator.

(defconst *comp-gcd3$go-num* (+ *merge$go-num*
                                *comp-gcd-cond$go-num*
                                *gcd-body$go-num*))
(defconst *comp-gcd3$st-len* 5)

(defun comp-gcd3$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun comp-gcd3$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (comp-gcd3$data-ins-len data-width)
     *comp-gcd3$go-num*))

;; DE module generator of COMP-GCD3

(module-generator
 comp-gcd3* (data-width)
 (si 'comp-gcd3 data-width)
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 (* 2 data-width))
                                     (sis 'go 0 *comp-gcd3$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-width))
 '(s l0 l1 l2 br)
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
        (list* 'merge-act 'cond-in-act (sis 'd0-in 0 (* 2 data-width))))

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
  (list 'br
        (list* 'cond-in-act 'branch-act 'out-act 'branch-act1 'done-
               (append (sis 'data-out 0 data-width)
                       (sis 'd1-in 0 (* 2 data-width))))
        (si 'comp-gcd-cond data-width)
        (list* 'l0-status 'br-empty-out0- 'br-empty-out1-
               (append (sis 'd0-out 0 (* 2 data-width))
                       (sis 'go
                            *merge$go-num*
                            *comp-gcd-cond$go-num*))))

  ;; Body
  (list 'body
        (list* 'body-act
               (sis 'd2-in 0 (* 2 data-width)))
        (si 'gcd-body data-width)
        (list* 'l1-status 'l2-status
               (append (sis 'd1-out 0 (* 2 data-width))
                       (sis 'go
                            (+ *merge$go-num*
                               *comp-gcd-cond$go-num*)
                            *gcd-body$go-num*)))))

 (declare (xargs :guard (natp data-width))))

(make-event
 `(progn
    ,@(state-accessors-gen 'comp-gcd3 '(s l0 l1 l2 br) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; COMP-GCD3.

(defund comp-gcd3$netlist (data-width)
  (declare (xargs :guard (and (natp data-width)
                              (<= 2 data-width))))
  (cons (comp-gcd3* data-width)
        (union$ (link1$netlist)
                (link$netlist (* 2 data-width))
                (comp-gcd-cond$netlist data-width)
                (gcd-body$netlist data-width)
                :test 'equal)))

;; Recognizer for COMP-GCD3

(defund comp-gcd3& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width)
                              (<= 2 data-width))))
  (b* ((subnetlist (delete-to-eq (si 'comp-gcd3 data-width) netlist)))
    (and (equal (assoc (si 'comp-gcd3 data-width) netlist)
                (comp-gcd3* data-width))
         (link1& subnetlist)
         (link& subnetlist (* 2 data-width))
         (comp-gcd-cond& subnetlist data-width)
         (gcd-body& subnetlist data-width)
         (merge& subnetlist (* 2 data-width)))))

;; Sanity check

(local
 (defthmd check-comp-gcd3$netlist-64
   (and (net-syntax-okp (comp-gcd3$netlist 64))
        (net-arity-okp (comp-gcd3$netlist 64))
        (comp-gcd3& (comp-gcd3$netlist 64) 64))))

;; Constraints on the state of COMP-GCD3

(defund comp-gcd3$st-format (st data-width)
  (b* ((l0 (get-field *comp-gcd3$l0* st))
       (l1 (get-field *comp-gcd3$l1* st))
       (l2 (get-field *comp-gcd3$l2* st))
       (br (get-field *comp-gcd3$br* st)))
    (and (link$st-format l0 (* 2 data-width))
         (link$st-format l1 (* 2 data-width))
         (link$st-format l2 (* 2 data-width))

         (comp-gcd-cond$st-format br data-width))))

(defthm comp-gcd3$st-format=>constraint
  (implies (comp-gcd3$st-format st data-width)
           (and (natp data-width)
                (<= 3 data-width)))
  :hints (("Goal"
           :in-theory (enable comp-gcd3$st-format)))
  :rule-classes :forward-chaining)

(defund comp-gcd3$valid-st (st data-width)
  (b* ((s (get-field *comp-gcd3$s* st))
       (l0 (get-field *comp-gcd3$l0* st))
       (l1 (get-field *comp-gcd3$l1* st))
       (l2 (get-field *comp-gcd3$l2* st))
       (br (get-field *comp-gcd3$br* st)))
    (and (link1$valid-st s)
         (link$valid-st l0 (* 2 data-width))
         (link$valid-st l1 (* 2 data-width))
         (link$valid-st l2 (* 2 data-width))

         (comp-gcd-cond$valid-st br data-width))))

(defthmd comp-gcd3$valid-st=>constraint
  (implies (comp-gcd3$valid-st st data-width)
           (and (natp data-width)
                (<= 3 data-width)))
  :hints (("Goal"
           :in-theory (enable comp-gcd-cond$valid-st=>constraint
                              comp-gcd3$valid-st)))
  :rule-classes :forward-chaining)

(defthmd comp-gcd3$valid-st=>st-format
  (implies (comp-gcd3$valid-st st data-width)
           (comp-gcd3$st-format st data-width))
  :hints (("Goal" :in-theory (e/d (comp-gcd-cond$valid-st=>st-format
                                   comp-gcd3$st-format
                                   comp-gcd3$valid-st)
                                  (link$st-format)))))

;; Extract the input and output signals for COMP-GCD3

(progn
  ;; Extract the input data

  (defun comp-gcd3$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (* 2 (mbe :logic (nfix data-width)
                    :exec  data-width))
          (nthcdr 2 inputs)))

  (defthm len-comp-gcd3$data-in
    (equal (len (comp-gcd3$data-in inputs data-width))
           (* 2 (nfix data-width))))

  (in-theory (disable comp-gcd3$data-in))

  ;; Extract the inputs for the merge-in joint

  (defund comp-gcd3$me-inputs (inputs st data-width)
    (b* ((full-in (nth 0 inputs))
         (data-in (comp-gcd3$data-in inputs data-width))
         (go-signals (nthcdr (comp-gcd3$data-ins-len data-width) inputs))

         (me-go-signals (take *merge$go-num* go-signals))

         (s (get-field *comp-gcd3$s* st))
         (s.s (get-field *link1$s* s))
         (s.d (get-field *link1$d* s))
         (l0 (get-field *comp-gcd3$l0* st))
         (l0.s (get-field *link$s* l0))
         (l2 (get-field *comp-gcd3$l2* st))
         (l2.s (get-field *link$s* l2))
         (l2.d (get-field *link$d* l2))

         (me-full-in0 (f-and full-in (car s.s)))
         (me-full-in1 (f-and (car l2.s) (car s.s))))

      (list* me-full-in0 me-full-in1 (car l0.s) (car s.d)
             (append data-in
                     (v-threefix (strip-cars l2.d))
                     me-go-signals))))

  ;; Extract the inputs for the branch-out joint

  (defund comp-gcd3$br-inputs (inputs st data-width)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (comp-gcd3$data-ins-len data-width) inputs))

         (br-go-signals (take *comp-gcd-cond$go-num*
                              (nthcdr *merge$go-num* go-signals)))

         (s (get-field *comp-gcd3$s* st))
         (s.s (get-field *link1$s* s))
         (l0 (get-field *comp-gcd3$l0* st))
         (l0.s (get-field *link$s* l0))
         (l0.d (get-field *link$d* l0))
         (l1 (get-field *comp-gcd3$l1* st))
         (l1.s (get-field *link$s* l1))

         (br-empty-out0- (f-or empty-out- (car s.s)))
         (br-empty-out1- (f-or (car l1.s) (car s.s))))

      (list* (f-buf (car l0.s)) br-empty-out0- br-empty-out1-
             (append (v-threefix (strip-cars l0.d))
                     br-go-signals))))

  ;; Extract the inputs for the "body" joint

  (defund comp-gcd3$body-inputs (inputs st data-width)
    (b* ((go-signals (nthcdr (comp-gcd3$data-ins-len data-width) inputs))

         (body-go-signals (take *gcd-body$go-num*
                                (nthcdr (+ *merge$go-num*
                                           *comp-gcd-cond$go-num*)
                                        go-signals)))

         (l1 (get-field *comp-gcd3$l1* st))
         (l1.s (get-field *link$s* l1))
         (l1.d (get-field *link$d* l1))
         (l2 (get-field *comp-gcd3$l2* st))
         (l2.s (get-field *link$s* l2)))

      (list* (f-buf (car l1.s)) (f-buf (car l2.s))
             (append (v-threefix (strip-cars l1.d))
                     body-go-signals))))

  ;; Extract the "in-act" signal

  (defund comp-gcd3$in-act (inputs st data-width)
    (merge$act0 (comp-gcd3$me-inputs inputs st data-width)
                (* 2 data-width)))

  (defthm comp-gcd3$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (comp-gcd3$in-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable comp-gcd3$me-inputs
                                       comp-gcd3$in-act))))

  ;; Extract the "out-act" signal

  (defund comp-gcd3$out-act (inputs st data-width)
    (comp-gcd-cond$out-act0 (comp-gcd3$br-inputs inputs st data-width)
                            (get-field *comp-gcd3$br* st)
                            data-width))

  (defthm comp-gcd3$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (comp-gcd3$out-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable comp-gcd3$br-inputs
                                       comp-gcd3$out-act))))

  ;; Extract the output data

  (defund comp-gcd3$data-out (inputs st data-width)
    (comp-gcd-cond$data0-out (comp-gcd3$br-inputs inputs st data-width)
                             (get-field *comp-gcd3$br* st)
                             data-width))

  (defthm len-comp-gcd3$data-out-1
    (implies (comp-gcd3$st-format st data-width)
             (equal (len (comp-gcd3$data-out inputs st data-width))
                    data-width))
    :hints (("Goal" :in-theory (enable comp-gcd3$st-format
                                       comp-gcd3$data-out))))

  (defthm len-comp-gcd3$data-out-2
    (implies (comp-gcd3$valid-st st data-width)
             (equal (len (comp-gcd3$data-out inputs st data-width))
                    data-width))
    :hints (("Goal" :in-theory (enable comp-gcd3$valid-st
                                       comp-gcd3$data-out))))

  (defthm bvp-comp-gcd3$data-out
    (implies (and (comp-gcd3$valid-st st data-width)
                  (comp-gcd3$out-act inputs st data-width))
             (bvp (comp-gcd3$data-out inputs st data-width)))
    :hints (("Goal" :in-theory (enable comp-gcd3$valid-st
                                       comp-gcd3$out-act
                                       comp-gcd3$data-out))))

  (defun comp-gcd3$outputs (inputs st data-width)
    (list* (comp-gcd3$in-act inputs st data-width)
           (comp-gcd3$out-act inputs st data-width)
           (comp-gcd3$data-out inputs st data-width)))
  )

;; The value lemma for COMP-GCD3

(defthm comp-gcd3$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (comp-gcd3& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-width))
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-gcd3$go-num*)
                  (comp-gcd3$st-format st data-width))
             (equal (se (si 'comp-gcd3 data-width) inputs st netlist)
                    (comp-gcd3$outputs inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'comp-gcd3 data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            comp-gcd-cond$st-format=>constraint
                            comp-gcd3&
                            comp-gcd3*$destructure
                            comp-gcd3$data-in
                            merge$act0
                            comp-gcd3$st-format
                            comp-gcd3$in-act
                            comp-gcd3$out-act
                            comp-gcd3$data-out
                            comp-gcd3$br-inputs
                            comp-gcd3$me-inputs)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of COMP-GCD3.

(defun comp-gcd3$step (inputs st data-width)
  (b* ((data-in (comp-gcd3$data-in inputs data-width))

       (s (get-field *comp-gcd3$s* st))
       (s.d (get-field *link1$d* s))
       (l0 (get-field *comp-gcd3$l0* st))
       (l1 (get-field *comp-gcd3$l1* st))
       (l2 (get-field *comp-gcd3$l2* st))
       (l2.d (get-field *link$d* l2))
       (br (get-field *comp-gcd3$br* st))

       (me-inputs (comp-gcd3$me-inputs inputs st data-width))
       (br-inputs (comp-gcd3$br-inputs inputs st data-width))
       (body-inputs (comp-gcd3$body-inputs inputs st data-width))

       (d1-in (comp-gcd-cond$data1-out br-inputs br data-width))
       (d2-in (gcd-body$data-out body-inputs data-width))

       (done- (comp-gcd-cond$flag br-inputs br data-width))
       (merge-act1 (merge$act1 me-inputs (* 2 data-width)))
       (merge-act (merge$act me-inputs (* 2 data-width)))
       (cond-in-act (comp-gcd-cond$in-act br-inputs br data-width))
       (branch-act1 (comp-gcd-cond$out-act1 br-inputs br data-width))
       (branch-act (comp-gcd-cond$out-act br-inputs br data-width))
       (body-act (gcd-body$act body-inputs data-width))

       (s-inputs (list branch-act merge-act done-))
       (l0-inputs (list* merge-act cond-in-act
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
     (link$step l2-inputs l2 (* 2 data-width))

     ;; COMP-GCD-COND
     (comp-gcd-cond$step br-inputs br data-width))))

(defthm len-of-comp-gcd3$step
  (equal (len (comp-gcd3$step inputs st data-width))
         *comp-gcd3$st-len*))

;; The state lemma for COMP-GCD3

(defthm comp-gcd3$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (comp-gcd3& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-width))
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-gcd3$go-num*)
                  (comp-gcd3$st-format st data-width))
             (equal (de (si 'comp-gcd3 data-width) inputs st netlist)
                    (comp-gcd3$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'comp-gcd3 data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            comp-gcd-cond$st-format=>constraint
                            comp-gcd3&
                            comp-gcd3*$destructure
                            merge$act
                            merge$act0
                            merge$act1
                            merge$value
                            comp-gcd3$st-format
                            comp-gcd3$data-in
                            comp-gcd3$br-inputs
                            comp-gcd3$me-inputs
                            comp-gcd3$body-inputs)
                           (de-module-disabled-rules)))))

(in-theory (disable comp-gcd3$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund comp-gcd3$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (comp-gcd3$data-in inputs data-width))
       (go-signals (nthcdr (comp-gcd3$data-ins-len data-width) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *comp-gcd3$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(local
 (defthm comp-gcd3$input-format=>br$input-format
   (implies (and (comp-gcd3$input-format inputs data-width)
                 (comp-gcd3$valid-st st data-width))
            (comp-gcd-cond$input-format
             (comp-gcd3$br-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (comp-gcd-cond$valid-st=>constraint
                             comp-gcd3$input-format
                             comp-gcd-cond$input-format
                             comp-gcd-cond$data-in
                             comp-gcd3$valid-st
                             comp-gcd3$br-inputs)
                            ())))))

(defthm booleanp-comp-gcd3$in-act
  (implies (and (comp-gcd3$input-format inputs data-width)
                (comp-gcd3$valid-st st data-width))
           (booleanp (comp-gcd3$in-act inputs st data-width)))
  :hints (("Goal" :in-theory (enable merge$act0
                                     comp-gcd3$input-format
                                     comp-gcd3$valid-st
                                     comp-gcd3$in-act
                                     comp-gcd3$me-inputs)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-gcd3$out-act
  (implies (and (comp-gcd3$input-format inputs data-width)
                (comp-gcd3$valid-st st data-width))
           (booleanp (comp-gcd3$out-act inputs st data-width)))
  :hints (("Goal"
           :use comp-gcd3$input-format=>br$input-format
           :in-theory (e/d (comp-gcd3$valid-st
                            comp-gcd3$out-act)
                           (comp-gcd3$input-format=>br$input-format))))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma comp-gcd3)

;; ======================================================================

;; 3. Single-Step-Update Property

;; Specify the functionality of COMP-GCD3, i.e., computing the greatest common
;; divisor of two natural numbers (see comp-gcd3$op).  Prove the correctness of
;; comp-gcd3$op.

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
   (defun comp-gcd3$op (x)
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
        (t (comp-gcd3$op
            (v-if a<b
                  (append a b-a)
                  (append a-b b))))))))

  (defun comp-gcd3$op (x)
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
       (t (comp-gcd3$op
           (v-if a<b
                 (append a b-a)
                 (append a-b b)))))))

  (local
   (defthm comp-gcd3$op-lemma-aux
     (implies (and (bv2p a b)
                   (not (v-< nil t (rev a) (rev b)))
                   (equal (v-to-nat a) 0))
              (equal a b))
     :hints (("Goal" :use (v-to-nat-equality
                           v-<-correct-2)))
     :rule-classes nil))

  (defthm comp-gcd3$op-lemma
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
               (equal (comp-gcd3$op (v-if a<b
                                          (append a b-a)
                                          (append a-b b)))
                      (comp-gcd3$op x))))
    :hints (("Goal"
             :induct (comp-gcd3$op x)
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
                    comp-gcd3$op-lemma-aux
                    (a (take data-width x))
                    (b (nthcdr data-width x)))))))

  ;; Prove that comp-gcd3$op correctly computes the greatest common divisor

  (local
   (defthm v-to-nat-of-COMP-GCD3$OP-is-GCD-ALG
     (implies (and (equal data-width (/ (len x) 2))
                   (bvp x))
              (equal (v-to-nat (comp-gcd3$op x))
                     (gcd-alg (v-to-nat (take data-width x))
                              (v-to-nat (nthcdr data-width x)))))
     :hints (("Goal" :in-theory (e/d ()
                                     (v-not-take
                                      v-not-nthcdr))))))

  (in-theory (disable comp-gcd3$op))
  )

;; The operation of COMP-GCD3 over a data sequence

(defun comp-gcd3$op-map (x)
  (if (atom x)
      nil
    (cons (comp-gcd3$op (car x))
          (comp-gcd3$op-map (cdr x)))))

(defthm len-of-comp-gcd3$op-map
  (equal (len (comp-gcd3$op-map x))
         (len x)))

(defthm comp-gcd3$op-map-of-append
  (equal (comp-gcd3$op-map (append x y))
         (append (comp-gcd3$op-map x) (comp-gcd3$op-map y))))

;; The extraction function for COMP-GCD3 that extracts the future output
;; sequence from the current state.

(defund comp-gcd3$extract (st)
  (b* ((l0 (get-field *comp-gcd3$l0* st))
       (l1 (get-field *comp-gcd3$l1* st))
       (l2 (get-field *comp-gcd3$l2* st))
       (br (get-field *comp-gcd3$br* st)))
    (comp-gcd3$op-map
     (append (extract-valid-data (list l1 l2 l0))
             (comp-gcd-cond$extract br)))))

(defthm comp-gcd3$extract-not-empty
  (implies (and (comp-gcd3$out-act inputs st data-width)
                (comp-gcd3$valid-st st data-width))
           (< 0 (len (comp-gcd3$extract st))))
  :hints (("Goal"
           :in-theory (e/d (comp-gcd3$valid-st
                            comp-gcd3$extract
                            comp-gcd3$out-act)
                           ())))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund comp-gcd3$inv (st)
    (b* ((s (get-field *comp-gcd3$s* st))
         (s.s (get-field *link1$s* s))
         (s.d (get-field *link1$d* s))
         (br (get-field *comp-gcd3$br* st)))
      (and (comp-gcd-cond$inv br)
           (if (and (fullp s.s) (not (car s.d)))
               (= (len (comp-gcd3$extract st))
                  0)
             (= (len (comp-gcd3$extract st))
                1)))))

  (local
   (defthm comp-gcd3$input-format-lemma-1
     (implies (comp-gcd3$input-format inputs data-width)
              (booleanp (nth 0 inputs)))
     :hints (("Goal" :in-theory (enable comp-gcd3$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm comp-gcd3$input-format-lemma-2
     (implies (comp-gcd3$input-format inputs data-width)
              (booleanp (nth 1 inputs)))
     :hints (("Goal" :in-theory (enable comp-gcd3$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm comp-gcd3$input-format-lemma-3
     (implies (and (comp-gcd3$input-format inputs data-width)
                   (nth 0 inputs))
              (bvp (comp-gcd3$data-in inputs data-width)))
     :hints (("Goal" :in-theory (enable comp-gcd3$input-format)))))

  (local
   (defthm comp-gcd-cond$in-act-inactive
     (implies (equal (nth *link$s*
                          (nth *comp-gcd3$l0* st))
                     '(nil))
              (not (comp-gcd-cond$in-act
                    (comp-gcd3$br-inputs inputs st data-width)
                    (nth *comp-gcd3$br* st)
                    data-width)))
     :hints (("Goal" :in-theory (e/d (get-field
                                      comp-gcd3$br-inputs)
                                     ())))))

  (local
   (defthm comp-gcd-cond$out-act0-inactive
     (implies (equal (nth *link$s*
                          (nth *comp-gcd3$s* st))
                     '(t))
              (not (comp-gcd-cond$out-act0
                    (comp-gcd3$br-inputs inputs st data-width)
                    (nth *comp-gcd3$br* st)
                    data-width)))
     :hints (("Goal" :in-theory (e/d (get-field
                                      comp-gcd3$br-inputs)
                                     ())))))

  (local
   (defthm comp-gcd-cond$out-act1-inactive
     (implies (or (equal (nth *link$s*
                              (nth *comp-gcd3$s* st))
                         '(t))
                  (equal (nth *link$s*
                              (nth *comp-gcd3$l1* st))
                         '(t)))
              (not (comp-gcd-cond$out-act1
                    (comp-gcd3$br-inputs inputs st data-width)
                    (nth *comp-gcd3$br* st)
                    data-width)))
     :hints (("Goal" :in-theory (e/d (get-field
                                      comp-gcd3$br-inputs)
                                     ())))))

  (local
   (defthm comp-gcd-cond$flag-inactive
     (implies (and (comp-gcd-cond$valid-st (nth *comp-gcd3$br* st)
                                           data-width)
                   (comp-gcd-cond$out-act0
                    (comp-gcd3$br-inputs inputs st data-width)
                    (nth *comp-gcd3$br* st)
                    data-width))
              (not (comp-gcd-cond$flag
                    (comp-gcd3$br-inputs inputs st data-width)
                    (nth *comp-gcd3$br* st)
                    data-width)))
     :hints (("Goal" :in-theory (e/d (get-field
                                      branch$act0
                                      gcd-cond$br-inputs
                                      gcd-cond$data-in
                                      gcd-cond$flag
                                      gcd-cond$act0
                                      comp-gcd3$br-inputs
                                      comp-gcd-cond$valid-st
                                      comp-gcd-cond$br-inputs
                                      comp-gcd-cond$out-act0
                                      comp-gcd-cond$flag)
                                     (b-nor3))))))

  (local
   (defthm comp-gcd-cond$flag-active
     (implies (and (comp-gcd-cond$valid-st (nth *comp-gcd3$br* st)
                                           data-width)
                   (comp-gcd-cond$out-act1
                    (comp-gcd3$br-inputs inputs st data-width)
                    (nth *comp-gcd3$br* st)
                    data-width))
              (equal (comp-gcd-cond$flag
                      (comp-gcd3$br-inputs inputs st data-width)
                      (nth *comp-gcd3$br* st)
                      data-width)
                     t))
     :hints (("Goal" :in-theory (e/d (get-field
                                      branch$act1
                                      gcd-cond$br-inputs
                                      gcd-cond$data-in
                                      gcd-cond$flag
                                      gcd-cond$act1
                                      comp-gcd3$br-inputs
                                      comp-gcd-cond$valid-st
                                      comp-gcd-cond$br-inputs
                                      comp-gcd-cond$out-act1
                                      comp-gcd-cond$flag)
                                     (b-nor3))))))

  (local
   (defthm booleanp-comp-gcd3$body-act
     (b* ((body-inputs (comp-gcd3$body-inputs inputs st data-width))
          (l1 (nth *comp-gcd3$l1* st))
          (l1.d (nth *link$d* l1)))
       (implies (or (equal (nth *link$s*
                                (nth *comp-gcd3$l1* st))
                           '(nil))
                    (and (equal (nth *link$s*
                                     (nth *comp-gcd3$l1* st))
                                '(t))
                         (equal (nth *link$s*
                                     (nth *comp-gcd3$l2* st))
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
                                        comp-gcd3$body-inputs)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm comp-gcd3$body-act-inactive
     (b* ((body-inputs (comp-gcd3$body-inputs inputs st data-width)))
       (implies (or (equal (nth *link$s*
                                (nth *comp-gcd3$l1* st))
                           '(nil))
                    (equal (nth *link$s*
                                (nth *comp-gcd3$l2* st))
                           '(t)))
                (not (gcd-body$act body-inputs data-width))))
     :hints (("Goal" :in-theory (enable get-field
                                        comp-gcd3$body-inputs)))))

  (local
   (defthm bvp-comp-gcd3$body-data-out
     (b* ((body-inputs (comp-gcd3$body-inputs inputs st data-width))
          (l1 (nth *comp-gcd3$l1* st))
          (l1.d (nth *link$d* l1)))
       (implies (and (equal (len l1.d) (* 2 data-width))
                     (bvp (strip-cars l1.d)))
                (bvp (gcd-body$data-out body-inputs data-width))))
     :hints (("Goal" :in-theory (enable get-field
                                        gcd-body$data-in
                                        comp-gcd3$body-inputs)))))

  (defthm comp-gcd3$inv-preserved
    (implies (and (comp-gcd3$input-format inputs data-width)
                  (comp-gcd3$valid-st st data-width)
                  (comp-gcd3$inv st))
             (comp-gcd3$inv (comp-gcd3$step inputs st data-width)))
    :hints (("Goal"
             :use comp-gcd3$input-format=>br$input-format
             :in-theory (e/d (get-field
                              f-sr
                              comp-gcd-cond$extracted-step
                              comp-gcd3$valid-st
                              comp-gcd3$inv
                              comp-gcd3$step
                              comp-gcd3$extract
                              comp-gcd3$me-inputs
                              comp-gcd-cond$out-act
                              merge$act
                              merge$act0
                              merge$act1)
                             (comp-gcd3$input-format=>br$input-format
                              nfix)))))
  )

;; The extracted next-state function for COMP-GCD3.  Note that this function
;; avoids exploring the internal computation of COMP-GCD3.

(defund comp-gcd3$extracted-step (inputs st data-width)
  (b* ((data (comp-gcd3$op (comp-gcd3$data-in inputs data-width)))
       (extracted-st (comp-gcd3$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-gcd3$out-act inputs st data-width) t)
      (cond
       ((equal (comp-gcd3$in-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (comp-gcd3$in-act inputs st data-width) t)
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
   (defthm comp-gcd3$extracted-step-correct-aux-1
     (b* ((body-inputs (comp-gcd3$body-inputs inputs st data-width))
          (l1 (nth *comp-gcd3$l1* st))
          (l1.d (nth *link$d* l1)))
       (implies (and (natp data-width)
                     (equal (len l1.d) (* 2 data-width))
                     (bvp (strip-cars l1.d)))
                (equal
                 (comp-gcd3$op (gcd-body$data-out body-inputs data-width))
                 (comp-gcd3$op (strip-cars l1.d)))))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d (get-field
                               gcd-body$data-in
                               gcd-body$a<b
                               gcd-body$data-out
                               gcd-body$data0-out
                               gcd-body$data1-out
                               comp-gcd3$body-inputs)
                              (v-if-works
                               v-not-take
                               v-not-nthcdr))))))

  (local
   (defthm comp-gcd3$extracted-step-correct-aux-2
     (b* ((br-inputs (comp-gcd3$br-inputs inputs st data-width))
          (l0 (nth *comp-gcd3$l0* st))
          (l0.d (nth *link$d* l0)))
       (implies
        (and (natp data-width)
             (equal (len l0.d) (* 2 data-width))
             (bvp (strip-cars l0.d)))
        (equal (comp-gcd-cond$op
                (cons
                 (take data-width
                       (comp-gcd-cond$data-in br-inputs data-width))
                 (nthcdr data-width
                         (comp-gcd-cond$data-in br-inputs data-width))))
               (strip-cars l0.d))))
     :hints (("Goal" :in-theory (enable get-field
                                        comp-gcd-cond$op
                                        comp-gcd-cond$data-in
                                        comp-gcd3$br-inputs)))))

  (defthm comp-gcd3$extracted-step-correct
    (b* ((next-st (comp-gcd3$step inputs st data-width)))
      (implies (and (comp-gcd3$input-format inputs data-width)
                    (comp-gcd3$valid-st st data-width)
                    (comp-gcd3$inv st))
               (equal (comp-gcd3$extract next-st)
                      (comp-gcd3$extracted-step inputs st data-width))))
    :hints (("Goal"
             :use comp-gcd3$input-format=>br$input-format
             :in-theory (e/d (get-field
                              f-sr
                              joint-act
                              comp-gcd-cond$valid-st=>constraint
                              comp-gcd-cond$extracted-step
                              comp-gcd3$extracted-step
                              comp-gcd3$valid-st
                              comp-gcd3$inv
                              comp-gcd3$step
                              comp-gcd3$in-act
                              comp-gcd3$out-act
                              comp-gcd3$data-out
                              comp-gcd3$me-inputs
                              comp-gcd3$extract
                              comp-gcd-cond$out-act
                              merge$act
                              merge$act0
                              merge$act1)
                             (comp-gcd3$input-format=>br$input-format
                              nfix)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that comp-gcd3$valid-st is an invariant.

(defthm comp-gcd3$valid-st-preserved
  (implies (and (comp-gcd3$input-format inputs data-width)
                (comp-gcd3$valid-st st data-width))
           (comp-gcd3$valid-st (comp-gcd3$step inputs st data-width)
                              data-width))
  :hints (("Goal"
           :use comp-gcd3$input-format=>br$input-format
           :in-theory (e/d (get-field
                            f-sr
                            joint-act
                            comp-gcd-cond$valid-st=>constraint
                            comp-gcd3$valid-st
                            comp-gcd3$step
                            comp-gcd3$me-inputs
                            comp-gcd-cond$out-act
                            merge$act
                            merge$act0
                            merge$act1)
                           (comp-gcd3$input-format=>br$input-format
                            nfix)))))

(encapsulate
  ()

  (local
   (defthm comp-gcd3$extract-lemma-aux-1
     (implies (and (<= (len (comp-gcd-cond$extract st))
                       1)
                   (comp-gcd-cond$valid-st st data-width)
                   (comp-gcd-cond$inv st)
                   (comp-gcd-cond$out-act0 inputs st data-width))
              (equal (comp-gcd-cond$extract st)
                     (list (comp-gcd-cond$data1-out inputs st data-width))))
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
   (defthm comp-gcd3$extract-lemma-aux-2
     (implies (and (comp-gcd-cond$valid-st st data-width)
                   (comp-gcd-cond$out-act0 inputs st data-width))
              (equal (comp-gcd3$op
                      (comp-gcd-cond$data1-out inputs st data-width))
                     (comp-gcd-cond$data0-out inputs st data-width)))
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
                                        comp-gcd3$op)))))

  (defthm comp-gcd3$extract-lemma
    (implies (and (comp-gcd3$valid-st st data-width)
                  (comp-gcd3$inv st)
                  (comp-gcd3$out-act inputs st data-width))
             (equal (list (comp-gcd3$data-out inputs st data-width))
                    (nthcdr (1- (len (comp-gcd3$extract st)))
                            (comp-gcd3$extract st))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (comp-gcd3$valid-st
                              comp-gcd3$inv
                              comp-gcd3$extract
                              comp-gcd3$br-inputs
                              comp-gcd3$out-act
                              comp-gcd3$data-out)
                             (v-if-works
                              comp-gcd-cond$extract-lemma)))))
  )

;; Extract the accepted input sequence

(seq-gen comp-gcd3 in in-act 0
         (comp-gcd3$data-in inputs data-width))

;; Extract the valid output sequence

(seq-gen comp-gcd3 out out-act 1
         (comp-gcd3$data-out inputs st data-width)
         :netlist-data (nthcdr 2 outputs))

;; The multi-step input-output relationship

(in-out-stream-lemma comp-gcd3 :op t :inv t)

