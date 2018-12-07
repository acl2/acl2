;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; November 2018

(in-package "ADE")

(include-book "alt-branch")
(include-book "alt-merge")
(include-book "queue2")
(include-book "queue3")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

(local
 (deftheory round-robin1$disabled-rules
   '(if*
     not
     take-redefinition
     pairlis$
     strip-cars
     true-listp
     default-car
     default-cdr
     default-+-1
     default-+-2
     acl2::append-of-cons
     acl2::simplify-products-gather-exponents-equal
     acl2::normalize-terms-such-as-a/a+b-+-b/a+b
     acl2::len-when-prefixp
     bv-is-true-list
     queue2$in-act-inactive
     queue2$out-act-inactive
     queue3$in-act-inactive
     queue3$out-act-inactive
     v-threefix
     open-v-threefix)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of RR1
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of RR1
;;
;; Construct a DE module generator for round-robin circuits using the
;; link-joint model.  Prove the value and state lemmas for this module
;; generator.

(defconst *round-robin1$go-num* (+ *queue2$go-num*
                                   *queue3$go-num*
                                   *alt-branch$go-num*
                                   *alt-merge$go-num*))
(defconst *round-robin1$st-len* 8)

(defun round-robin1$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun round-robin1$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (round-robin1$data-ins-len data-width)
     *round-robin1$go-num*))

;; DE module generator of RR1.  The ALT-BRANCH joint in RR1 accepts input data
;; and places them alternately into two queues.  The ALT-MERGE joint takes data
;; alternately from two queues and delivers them as outputs.

(module-generator
 round-robin1* (data-width)
 (si 'round-robin1 data-width)
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 data-width)
                                    (sis 'go 0 *round-robin1$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-width))
 '(a0 b0 a1 b1 q2 q3 br me)
 (list
  ;; LINKS
  ;; A0
  (list 'a0
        (list* 'a0-status (sis 'a0-out 0 data-width))
        (si 'link data-width)
        (list* 'br-act0 'q2-in-act (sis 'data 0 data-width)))

  ;; B0
  (list 'b0
        (list* 'b0-status (sis 'b0-out 0 data-width))
        (si 'link data-width)
        (list* 'br-act1 'q3-in-act (sis 'data 0 data-width)))

  ;; A1
  (list 'a1
        (list* 'a1-status (sis 'a1-out 0 data-width))
        (si 'link data-width)
        (list* 'q2-out-act 'me-act0 (sis 'q2-data-out 0 data-width)))

  ;; B1
  (list 'b1
        (list* 'b1-status (sis 'b1-out 0 data-width))
        (si 'link data-width)
        (list* 'q3-out-act 'me-act1 (sis 'q3-data-out 0 data-width)))

  ;; JOINTS
  ;; 2-link queue Q2
  (list 'q2
        (list* 'q2-in-act 'q2-out-act
               (sis 'q2-data-out 0 data-width))
        (si 'queue2 data-width)
        (list* 'a0-status 'a1-status
               (append (sis 'a0-out 0 data-width)
                       (sis 'go 0 *queue2$go-num*))))

  ;; 3-link queue Q3
  (list 'q3
        (list* 'q3-in-act 'q3-out-act
               (sis 'q3-data-out 0 data-width))
        (si 'queue3 data-width)
        (list* 'b0-status 'b1-status
               (append (sis 'b0-out 0 data-width)
                       (sis 'go
                            *queue2$go-num*
                            *queue3$go-num*))))

  ;; Alt-Branch
  (list 'br
        (list* 'in-act 'br-act0 'br-act1
               (sis 'data 0 data-width))
        (si 'alt-branch data-width)
        (list* 'full-in 'a0-status 'b0-status
               (append (sis 'data-in 0 data-width)
                       (sis 'go
                            (+ *queue2$go-num*
                               *queue3$go-num*)
                            *alt-branch$go-num*))))

  ;; Alt-Merge
  (list 'me
        (list* 'out-act 'me-act0 'me-act1
               (sis 'data-out 0 data-width))
        (si 'alt-merge data-width)
        (list* 'a1-status 'b1-status 'empty-out-
               (append (sis 'a1-out 0 data-width)
                       (sis 'b1-out 0 data-width)
                       (sis 'go
                            (+ *queue2$go-num*
                               *queue3$go-num*
                               *alt-branch$go-num*)
                            *alt-merge$go-num*)))))

 (declare (xargs :guard (natp data-width))))

(make-event
 `(progn
    ,@(state-accessors-gen 'round-robin1 '(a0 b0 a1 b1 q2 q3 br me) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of RR1.

(defund round-robin1$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (round-robin1* data-width)
        (union$ (queue2$netlist data-width)
                (queue3$netlist data-width)
                (alt-branch$netlist data-width)
                (alt-merge$netlist data-width)
                :test 'equal)))

;; Recognizer for RR1

(defund round-robin1& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (b* ((subnetlist (delete-to-eq (si 'round-robin1 data-width) netlist)))
    (and (equal (assoc (si 'round-robin1 data-width) netlist)
                (round-robin1* data-width))
         (link& subnetlist data-width)
         (queue2& subnetlist data-width)
         (queue3& subnetlist data-width)
         (alt-branch& subnetlist data-width)
         (alt-merge& subnetlist data-width))))

;; Sanity check

(local
 (defthmd check-round-robin1$netlist-64
   (and (net-syntax-okp (round-robin1$netlist 64))
        (net-arity-okp (round-robin1$netlist 64))
        (round-robin1& (round-robin1$netlist 64) 64))))

;; Constraints on the state of RR1

(defund round-robin1$st-format (st data-width)
  (b* ((a0 (get-field *round-robin1$a0* st))
       (b0 (get-field *round-robin1$b0* st))
       (a1 (get-field *round-robin1$a1* st))
       (b1 (get-field *round-robin1$b1* st))
       (q2 (get-field *round-robin1$q2* st))
       (q3 (get-field *round-robin1$q3* st)))
    (and (< 0 data-width)

         (link$st-format a0 data-width)
         (link$st-format b0 data-width)
         (link$st-format a1 data-width)
         (link$st-format b1 data-width)

         (queue2$st-format q2 data-width)
         (queue3$st-format q3 data-width))))

(defthm round-robin1$st-format=>constraint
  (implies (round-robin1$st-format st data-width)
           (posp data-width))
  :hints (("Goal" :in-theory (enable round-robin1$st-format)))
  :rule-classes :forward-chaining)

(defund round-robin1$valid-st (st data-width)
  (b* ((a0 (get-field *round-robin1$a0* st))
       (b0 (get-field *round-robin1$b0* st))
       (a1 (get-field *round-robin1$a1* st))
       (b1 (get-field *round-robin1$b1* st))
       (q2 (get-field *round-robin1$q2* st))
       (q3 (get-field *round-robin1$q3* st))
       (br (get-field *round-robin1$br* st))
       (me (get-field *round-robin1$me* st)))
    (and (round-robin1$st-format st data-width)

         (link$valid-st a0 data-width)
         (link$valid-st b0 data-width)
         (link$valid-st a1 data-width)
         (link$valid-st b1 data-width)

         (queue2$valid-st q2 data-width)
         (queue3$valid-st q3 data-width)

         (alt-branch$valid-st br)
         (alt-merge$valid-st me))))

(defthmd round-robin1$valid-st=>constraint
  (implies (round-robin1$valid-st st data-width)
           (posp data-width))
  :hints (("Goal" :in-theory (enable round-robin1$valid-st)))
  :rule-classes :forward-chaining)

(defthmd round-robin1$valid-st=>st-format
  (implies (round-robin1$valid-st st data-width)
           (round-robin1$st-format st data-width))
  :hints (("Goal" :in-theory (e/d (round-robin1$valid-st)
                                  ()))))

;; Extract the input and output signals for RR1

(progn
  ;; Extract the input data

  (defun round-robin1$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 2 inputs)))

  (defthm len-round-robin1$data-in
    (equal (len (round-robin1$data-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable round-robin1$data-in))

  ;; Extract the inputs for the Q2 joint

  (defund round-robin1$q2-inputs (inputs st data-width)
    (b* ((go-signals (nthcdr (round-robin1$data-ins-len data-width) inputs))

         (q2-go-signals (take *queue2$go-num* go-signals))

         (a0 (get-field *round-robin1$a0* st))
         (a0.s (get-field *link$s* a0))
         (a0.d (get-field *link$d* a0))
         (a1 (get-field *round-robin1$a1* st))
         (a1.s (get-field *link$s* a1)))

      (list* (f-buf (car a0.s)) (f-buf (car a1.s))
             (append (v-threefix (strip-cars a0.d))
                     q2-go-signals))))

  ;; Extract the inputs for the Q3 joint

  (defund round-robin1$q3-inputs (inputs st data-width)
    (b* ((go-signals (nthcdr (round-robin1$data-ins-len data-width) inputs))

         (q3-go-signals (take *queue3$go-num*
                              (nthcdr *queue2$go-num*
                                      go-signals)))

         (b0 (get-field *round-robin1$b0* st))
         (b0.s (get-field *link$s* b0))
         (b0.d (get-field *link$d* b0))
         (b1 (get-field *round-robin1$b1* st))
         (b1.s (get-field *link$s* b1)))

      (list* (f-buf (car b0.s)) (f-buf (car b1.s))
             (append (v-threefix (strip-cars b0.d))
                     q3-go-signals))))

  ;; Extract the inputs for the alt-branch joint

  (defund round-robin1$br-inputs (inputs st data-width)
    (b* ((full-in    (nth 0 inputs))
         (data-in    (round-robin1$data-in inputs data-width))
         (go-signals (nthcdr (round-robin1$data-ins-len data-width) inputs))

         (br-go-signals (take *alt-branch$go-num*
                              (nthcdr (+ *queue2$go-num*
                                         *queue3$go-num*)
                                      go-signals)))

         (a0 (get-field *round-robin1$a0* st))
         (a0.s (get-field *link$s* a0))
         (b0 (get-field *round-robin1$b0* st))
         (b0.s (get-field *link$s* b0)))

      (list* full-in (f-buf (car a0.s)) (f-buf (car b0.s))
             (append data-in br-go-signals))))

  ;; Extract the inputs for the alt-merge joint

  (defund round-robin1$me-inputs (inputs st data-width)
    (b* ((empty-out-  (nth 1 inputs))
         (go-signals (nthcdr (round-robin1$data-ins-len data-width) inputs))

         (me-go-signals (take *alt-merge$go-num*
                              (nthcdr (+ *queue2$go-num*
                                         *queue3$go-num*
                                         *alt-branch$go-num*)
                                      go-signals)))

         (a1 (get-field *round-robin1$a1* st))
         (a1.s (get-field *link$s* a1))
         (a1.d (get-field *link$d* a1))
         (b1 (get-field *round-robin1$b1* st))
         (b1.s (get-field *link$s* b1))
         (b1.d (get-field *link$d* b1)))

      (list* (f-buf (car a1.s)) (f-buf (car b1.s)) empty-out-
             (append (v-threefix (strip-cars a1.d))
                     (v-threefix (strip-cars b1.d))
                     me-go-signals))))

  ;; Extract the "in-act" signal

  (defund round-robin1$in-act (inputs st data-width)
    (b* ((br-inputs (round-robin1$br-inputs inputs st data-width))
         (br (get-field *round-robin1$br* st)))
      (alt-branch$act br-inputs br data-width)))

  (defthm round-robin1$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (round-robin1$in-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable round-robin1$br-inputs
                                       round-robin1$in-act))))

  ;; Extract the "out-act" signal

  (defund round-robin1$out-act (inputs st data-width)
    (b* ((me-inputs (round-robin1$me-inputs inputs st data-width))
         (me (get-field *round-robin1$me* st)))
      (alt-merge$act me-inputs me data-width)))

  (defthm round-robin1$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (round-robin1$out-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable round-robin1$me-inputs
                                       round-robin1$out-act))))

  ;; Extract the output data

  (defund round-robin1$data-out (st)
    (b* ((a1 (get-field *round-robin1$a1* st))
         (a1.d (get-field *link$d* a1))
         (b1 (get-field *round-robin1$b1* st))
         (b1.d (get-field *link$d* b1))
         (me (get-field *round-robin1$me* st))

         (me-select (get-field *alt-merge$select* me))
         (me-select.d (get-field *link1$d* me-select)))
      (fv-if (car me-select.d)
             (strip-cars b1.d)
             (strip-cars a1.d))))

  (defthm len-round-robin1$data-out-1
    (implies (round-robin1$st-format st data-width)
             (equal (len (round-robin1$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable round-robin1$st-format
                                       round-robin1$data-out))))

  (defthm len-round-robin1$data-out-2
    (implies (round-robin1$valid-st st data-width)
             (equal (len (round-robin1$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable round-robin1$valid-st
                                       round-robin1$data-out))))

  (defthm bvp-round-robin1$data-out
    (implies (and (round-robin1$valid-st st data-width)
                  (round-robin1$out-act inputs st data-width))
             (bvp (round-robin1$data-out st)))
    :hints (("Goal" :in-theory (enable f-and3
                                       f-and
                                       joint-act
                                       round-robin1$valid-st
                                       round-robin1$st-format
                                       round-robin1$out-act
                                       round-robin1$data-out
                                       round-robin1$me-inputs
                                       alt-merge$valid-st
                                       alt-merge$act
                                       alt-merge$act0
                                       alt-merge$act1))))

  (defun round-robin1$outputs (inputs st data-width)
    (list* (round-robin1$in-act inputs st data-width)
           (round-robin1$out-act inputs st data-width)
           (round-robin1$data-out st)))
  )

;; The value lemma for RR1

(defthm round-robin1$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (round-robin1& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *round-robin1$go-num*)
                  (round-robin1$st-format st data-width))
             (equal (se (si 'round-robin1 data-width) inputs st netlist)
                    (round-robin1$outputs inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'round-robin1 data-width)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            round-robin1&
                            round-robin1*$destructure
                            round-robin1$data-in
                            round-robin1$st-format
                            round-robin1$in-act
                            round-robin1$out-act
                            round-robin1$data-out
                            round-robin1$br-inputs
                            round-robin1$me-inputs)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of RR1.

(defun round-robin1$step (inputs st data-width)
  (b* ((data-in (round-robin1$data-in inputs data-width))

       (a0 (get-field *round-robin1$a0* st))
       (b0 (get-field *round-robin1$b0* st))
       (a1 (get-field *round-robin1$a1* st))
       (b1 (get-field *round-robin1$b1* st))
       (q2 (get-field *round-robin1$q2* st))
       (q3 (get-field *round-robin1$q3* st))
       (br (get-field *round-robin1$br* st))
       (me (get-field *round-robin1$me* st))

       (q2-inputs (round-robin1$q2-inputs inputs st data-width))
       (q2-in-act (queue2$in-act q2-inputs q2 data-width))
       (q2-out-act (queue2$out-act q2-inputs q2 data-width))
       (q2-data-out (queue2$data-out q2))

       (q3-inputs (round-robin1$q3-inputs inputs st data-width))
       (q3-in-act (queue3$in-act q3-inputs q3 data-width))
       (q3-out-act (queue3$out-act q3-inputs q3 data-width))
       (q3-data-out (queue3$data-out q3))

       (br-inputs (round-robin1$br-inputs inputs st data-width))
       (br-act0 (alt-branch$act0 br-inputs br data-width))
       (br-act1 (alt-branch$act1 br-inputs br data-width))

       (me-inputs (round-robin1$me-inputs inputs st data-width))
       (me-act0 (alt-merge$act0 me-inputs me data-width))
       (me-act1 (alt-merge$act1 me-inputs me data-width))

       (a0-inputs (list* br-act0 q2-in-act data-in))
       (b0-inputs (list* br-act1 q3-in-act data-in))
       (a1-inputs (list* q2-out-act me-act0 q2-data-out))
       (b1-inputs (list* q3-out-act me-act1 q3-data-out)))

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
     (queue3$step q3-inputs q3 data-width)
     ;; Joint ALT-BRANCH
     (alt-branch$step br-inputs br data-width)
     ;; Joint ALT-MERGE
     (alt-merge$step me-inputs me data-width))))

(defthm len-of-round-robin1$step
  (equal (len (round-robin1$step inputs st data-width))
         *round-robin1$st-len*))

;; The state lemma for RR1

(defthm round-robin1$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (round-robin1& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *round-robin1$go-num*)
                  (round-robin1$st-format st data-width))
             (equal (de (si 'round-robin1 data-width) inputs st netlist)
                    (round-robin1$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'round-robin1 data-width)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            round-robin1&
                            round-robin1*$destructure
                            round-robin1$st-format
                            round-robin1$data-in
                            round-robin1$q2-inputs
                            round-robin1$q3-inputs
                            round-robin1$br-inputs
                            round-robin1$me-inputs)
                           (de-module-disabled-rules)))))

(in-theory (disable round-robin1$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund round-robin1$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (round-robin1$data-in inputs data-width))
       (go-signals (nthcdr (round-robin1$data-ins-len data-width) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *round-robin1$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(local
 (defthm round-robin1$input-format=>q2$input-format
   (implies (and (round-robin1$input-format inputs data-width)
                 (round-robin1$valid-st st data-width))
            (queue2$input-format
             (round-robin1$q2-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (round-robin1$input-format
                             queue2$input-format
                             queue2$data-in
                             round-robin1$valid-st
                             round-robin1$st-format
                             round-robin1$q2-inputs)
                            ())))))

(local
 (defthm round-robin1$input-format=>q3$input-format
   (implies (and (round-robin1$input-format inputs data-width)
                 (round-robin1$valid-st st data-width))
            (queue3$input-format
             (round-robin1$q3-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (round-robin1$input-format
                             queue3$input-format
                             queue3$data-in
                             round-robin1$valid-st
                             round-robin1$st-format
                             round-robin1$q3-inputs)
                            ())))))

(local
 (defthm round-robin1$input-format=>br$input-format
   (implies (and (round-robin1$input-format inputs data-width)
                 (round-robin1$valid-st st data-width))
            (alt-branch$input-format
             (round-robin1$br-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (round-robin1$input-format
                             alt-branch$input-format
                             alt-branch$data-in
                             round-robin1$valid-st
                             round-robin1$st-format
                             round-robin1$br-inputs)
                            ())))))

(local
 (defthm round-robin1$input-format=>me$input-format
   (implies (and (round-robin1$input-format inputs data-width)
                 (round-robin1$valid-st st data-width))
            (alt-merge$input-format
             (round-robin1$me-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (round-robin1$input-format
                             alt-merge$input-format
                             alt-merge$data0-in
                             alt-merge$data1-in
                             round-robin1$valid-st
                             round-robin1$st-format
                             round-robin1$me-inputs)
                            ())))))

(defthm booleanp-round-robin1$in-act
  (implies (and (round-robin1$input-format inputs data-width)
                (round-robin1$valid-st st data-width))
           (booleanp (round-robin1$in-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (enable round-robin1$valid-st
                              round-robin1$in-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-round-robin1$out-act
  (implies (and (round-robin1$input-format inputs data-width)
                (round-robin1$valid-st st data-width))
           (booleanp (round-robin1$out-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (enable round-robin1$valid-st
                              round-robin1$out-act)))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma round-robin1)

;; ======================================================================

;; 3. Single-Step-Update Property

(defun intertwine (l1 l2)
  (declare (xargs :guard t))
  (cond ((atom l1) l2)
        ((atom l2) l1)
        (t (append (list (car l1) (car l2))
                   (intertwine (cdr l1) (cdr l2))))))

(defthm consp-intertwine
  (implies (or (consp l1) (consp l2)
               (< 0 (len l1)) (< 0 (len l2)))
           (consp (intertwine l1 l2)))
  :rule-classes (:rewrite :type-prescription))

(defthm true-listp-intertwine
  (implies (and (true-listp l1)
                (true-listp l2))
           (true-listp (intertwine l1 l2)))
  :rule-classes (:rewrite :type-prescription))

(defthm len-intertwine
  (equal (len (intertwine l1 l2))
         (+ (len l1) (len l2))))

(defthm len-of-cdr-intertwine
  (implies (or (< 0 (len l1)) (< 0 (len l2)))
           (equal (len (cdr (intertwine l1 l2)))
                  (+ -1 (len l1) (len l2)))))

(defthm intertwine-append-1
  (implies (and (or (equal (len x1) (len x2))
                    (equal (len x1) (1+ (len x2))))
                (consp y))
           (equal (intertwine (append x1 y) x2)
                  (append (intertwine x1 x2) y))))

(defthm intertwine-append-2
  (implies (and (<= (len x1) (1+ (len x2)))
                (consp y))
           (equal (intertwine x1 (append x2 y))
                  (append (intertwine x1 x2) y))))

(defthm intertwine-append-append
  (implies (equal (len x1) (len x2))
           (equal (intertwine (append x1 y1) (append x2 y2))
                  (append (intertwine x1 x2) (intertwine y1 y2)))))

;; The extraction function for RR1 that extracts the future output sequence
;; from the current state.

(defund round-robin1$extract (st)
  (b* ((a0 (get-field *round-robin1$a0* st))
       (b0 (get-field *round-robin1$b0* st))
       (a1 (get-field *round-robin1$a1* st))
       (b1 (get-field *round-robin1$b1* st))
       (q2 (get-field *round-robin1$q2* st))
       (q3 (get-field *round-robin1$q3* st))
       (me (get-field *round-robin1$me* st))

       (a-seq (append (extract-valid-data (list a0))
                      (queue2$extract q2)
                      (extract-valid-data (list a1))))
       (b-seq (append (extract-valid-data (list b0))
                      (queue3$extract q3)
                      (extract-valid-data (list b1))))

       (me-select (get-field *alt-merge$select* me))
       (me-select.s (get-field *link1$s* me-select))
       (me-select.d (get-field *link1$d* me-select))
       (me-select-buf (get-field *alt-merge$select-buf* me))
       (me-select-buf.d (get-field *link1$d* me-select-buf))
       (valid-me-select (if (fullp me-select.s)
                            (car me-select.d)
                          (car me-select-buf.d))))

    (cond ((< (len a-seq) (len b-seq))
           (intertwine b-seq a-seq))
          ((< (len b-seq) (len a-seq))
           (intertwine a-seq b-seq))
          (valid-me-select (intertwine a-seq b-seq))
          (t (intertwine b-seq a-seq)))))

(defthm round-robin1$extract-not-empty
  (implies (and (round-robin1$out-act inputs st data-width)
                (round-robin1$valid-st st data-width))
           (< 0 (len (round-robin1$extract st))))
  :hints (("Goal"
           :in-theory (e/d (f-and3
                            alt-merge$act
                            alt-merge$act0
                            alt-merge$act1
                            round-robin1$me-inputs
                            round-robin1$valid-st
                            round-robin1$extract
                            round-robin1$out-act)
                           ())))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund round-robin1$inv (st)
    (b* ((a0 (get-field *round-robin1$a0* st))
         (b0 (get-field *round-robin1$b0* st))
         (a1 (get-field *round-robin1$a1* st))
         (b1 (get-field *round-robin1$b1* st))
         (q2 (get-field *round-robin1$q2* st))
         (q3 (get-field *round-robin1$q3* st))
         (br (get-field *round-robin1$br* st))
         (me (get-field *round-robin1$me* st))

         (a-seq (append (extract-valid-data (list a0))
                        (queue2$extract q2)
                        (extract-valid-data (list a1))))
         (b-seq (append (extract-valid-data (list b0))
                        (queue3$extract q3)
                        (extract-valid-data (list b1))))

         (br-select (get-field *alt-branch$select* br))
         (br-select.s (get-field *link1$s* br-select))
         (br-select.d (get-field *link1$d* br-select))
         (br-select-buf (get-field *alt-branch$select-buf* br))
         (br-select-buf.d (get-field *link1$d* br-select-buf))
         (valid-br-select (if (fullp br-select.s)
                              (car br-select.d)
                            (car br-select-buf.d)))

         (me-select (get-field *alt-merge$select* me))
         (me-select.s (get-field *link1$s* me-select))
         (me-select.d (get-field *link1$d* me-select))
         (me-select-buf (get-field *alt-merge$select-buf* me))
         (me-select-buf.d (get-field *link1$d* me-select-buf))
         (valid-me-select (if (fullp me-select.s)
                              (car me-select.d)
                            (car me-select-buf.d))))

      (and (alt-branch$inv br)
           (alt-merge$inv me)
           (or (and (equal (len a-seq) (len b-seq))
                    (equal valid-br-select valid-me-select))
               (and (equal (len a-seq) (1+ (len b-seq)))
                    valid-br-select
                    (not valid-me-select))
               (and (equal (1+ (len a-seq)) (len b-seq))
                    (not valid-br-select)
                    valid-me-select)))))

  (local
   (defthm round-robin1$input-format-lemma-1
     (implies (round-robin1$input-format inputs data-width)
              (booleanp (nth 0 inputs)))
     :hints (("Goal" :in-theory (enable round-robin1$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm round-robin1$input-format-lemma-2
     (implies (round-robin1$input-format inputs data-width)
              (booleanp (nth 1 inputs)))
     :hints (("Goal" :in-theory (enable round-robin1$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm round-robin1$input-format-lemma-3
     (implies (and (round-robin1$input-format inputs data-width)
                   (nth 0 inputs))
              (bvp (round-robin1$data-in inputs data-width)))
     :hints (("Goal" :in-theory (enable round-robin1$input-format)))))

  (local
   (defthm round-robin1$q2-in-act-inactive
     (implies (equal (nth *link$s*
                          (nth *round-robin1$a0* st))
                     '(nil))
              (not (queue2$in-act
                    (round-robin1$q2-inputs inputs st data-width)
                    (nth *round-robin1$q2* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 round-robin1$q2-inputs)))))

  (local
   (defthm round-robin1$q3-in-act-inactive
     (implies (equal (nth *link$s*
                          (nth *round-robin1$b0* st))
                     '(nil))
              (not (queue3$in-act
                    (round-robin1$q3-inputs inputs st data-width)
                    (nth *round-robin1$q3* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 round-robin1$q3-inputs)))))

  (local
   (defthm round-robin1$q2-out-act-inactive
     (implies (equal (nth *link$s*
                          (nth *round-robin1$a1* st))
                     '(t))
              (not (queue2$out-act
                    (round-robin1$q2-inputs inputs st data-width)
                    (nth *round-robin1$q2* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 round-robin1$q2-inputs)))))

  (local
   (defthm round-robin1$q3-out-act-inactive
     (implies (equal (nth *link$s*
                          (nth *round-robin1$b1* st))
                     '(t))
              (not (queue3$out-act
                    (round-robin1$q3-inputs inputs st data-width)
                    (nth *round-robin1$q3* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 round-robin1$q3-inputs)))))

  (local
   (defthm round-robin1$br-act0-inactive
     (implies (equal (nth *link$s*
                          (nth *round-robin1$a0* st))
                     '(t))
              (not (alt-branch$act0
                    (round-robin1$br-inputs inputs st data-width)
                    (nth *round-robin1$br* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 round-robin1$br-inputs)))))

  (local
   (defthm round-robin1$br-act1-inactive
     (implies (equal (nth *link$s*
                          (nth *round-robin1$b0* st))
                     '(t))
              (not (alt-branch$act1
                    (round-robin1$br-inputs inputs st data-width)
                    (nth *round-robin1$br* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 round-robin1$br-inputs)))))

  (local
   (defthm round-robin1$me-act0-inactive
     (implies (equal (nth *link$s*
                          (nth *round-robin1$a1* st))
                     '(nil))
              (not (alt-merge$act0
                    (round-robin1$me-inputs inputs st data-width)
                    (nth *round-robin1$me* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 round-robin1$me-inputs)))))

  (local
   (defthm round-robin1$me-act1-inactive
     (implies (equal (nth *link$s*
                          (nth *round-robin1$b1* st))
                     '(nil))
              (not (alt-merge$act1
                    (round-robin1$me-inputs inputs st data-width)
                    (nth *round-robin1$me* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 round-robin1$me-inputs)))))

  (defthm round-robin1$inv-preserved
    (implies (and (round-robin1$input-format inputs data-width)
                  (round-robin1$valid-st st data-width)
                  (round-robin1$inv st))
             (round-robin1$inv
              (round-robin1$step inputs st data-width)))
    :hints (("Goal"
             :use (round-robin1$input-format=>q2$input-format
                   round-robin1$input-format=>q3$input-format)
             :in-theory (e/d (get-field
                              f-sr
                              queue2$extracted-step
                              queue3$extracted-step
                              round-robin1$valid-st
                              round-robin1$inv
                              round-robin1$step
                              round-robin1$br-inputs
                              round-robin1$me-inputs
                              alt-branch$valid-st
                              alt-branch$inv
                              alt-branch$step
                              alt-branch$act
                              alt-branch$act0
                              alt-branch$act1
                              alt-merge$valid-st
                              alt-merge$inv
                              alt-merge$step
                              alt-merge$act
                              alt-merge$act0
                              alt-merge$act1)
                             (round-robin1$input-format=>q2$input-format
                              round-robin1$input-format=>q3$input-format
                              nfix
                              append
                              round-robin1$disabled-rules)))))
  )

;; The extracted next-state function for RR1.  Note that this function avoids
;; exploring the internal computation of RR1.

(defund round-robin1$extracted-step (inputs st data-width)
  (b* ((data (round-robin1$data-in inputs data-width))
       (extracted-st (round-robin1$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (round-robin1$out-act inputs st data-width) t)
      (cond
       ((equal (round-robin1$in-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (round-robin1$in-act inputs st data-width) t)
          (cons data extracted-st))
         (t extracted-st))))))

(local
 (defthmd cons-append-instances
   (and (equal (cons e (append (queue2$extract st)
                               x))
               (append (cons e (queue2$extract st))
                       x))
        (equal (cons e (append (queue3$extract st)
                               x))
               (append (cons e (queue3$extract st))
                       x)))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm consp-queue2$extract
     (implies (and (queue2$out-act inputs st data-width)
                   (queue2$valid-st st data-width))
              (consp (queue2$extract st)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue2$valid-st
                                 queue2$extract
                                 queue2$out-act)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm consp-queue3$extract
     (implies (and (queue3$out-act inputs st data-width)
                   (queue3$valid-st st data-width))
              (consp (queue3$extract st)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue3$valid-st
                                 queue3$extract
                                 queue3$out-act)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm round-robin1$q2-get-$data-in-rewrite
     (b* ((a0 (get-field *round-robin1$a0* st))
          (a0.d (get-field *link$d* a0)))
       (implies (and (bvp (strip-cars a0.d))
                     (equal (len a0.d) data-width))
                (equal (queue2$data-in
                        (round-robin1$q2-inputs inputs st data-width)
                        data-width)
                       (strip-cars a0.d))))
     :hints (("Goal"
              :in-theory (enable queue2$data-in
                                 round-robin1$q2-inputs)))))

  (local
   (defthm round-robin1$q3-get-$data-in-rewrite
     (b* ((b0 (get-field *round-robin1$b0* st))
          (b0.d (get-field *link$d* b0)))
       (implies (and (bvp (strip-cars b0.d))
                     (equal (len b0.d) data-width))
                (equal (queue3$data-in
                        (round-robin1$q3-inputs inputs st data-width)
                        data-width)
                       (strip-cars b0.d))))
     :hints (("Goal"
              :in-theory (enable queue3$data-in
                                 round-robin1$q3-inputs)))))

  (local
   (defthm round-robin1$extracted-step-correct-aux-1
     (equal (cons e (append (intertwine x y)
                            z))
            (append (intertwine (cons e y)
                                x)
                    z))))

  (local
   (defthm round-robin1$extracted-step-correct-aux-2
     (equal (cons e (append (cdr (intertwine x y))
                            z))
            (append (cons e (cdr (intertwine x y)))
                    z))))

  (local
   (defthm round-robin1$extracted-step-correct-aux-3
     (implies (consp x)
              (equal (cons (car x)
                           (intertwine (queue2$extract st)
                                       (cdr x)))
                     (intertwine x (queue2$extract st))))))

  (local
   (defthm round-robin1$extracted-step-correct-aux-4
     (implies (consp x)
              (equal (cons (car x)
                           (intertwine (queue3$extract st)
                                       (cdr x)))
                     (intertwine x (queue3$extract st))))))

  (local
   (defthm round-robin1$extracted-step-correct-aux-5
     (implies (consp x)
              (equal (cons (car x)
                           (intertwine (append y z)
                                       (cdr x)))
                     (intertwine x (append y z))))
     :hints (("Goal" :in-theory (disable intertwine-append-2)))))

  (defthm round-robin1$extracted-step-correct
    (b* ((next-st (round-robin1$step inputs st data-width)))
      (implies (and (round-robin1$input-format inputs data-width)
                    (round-robin1$valid-st st data-width)
                    (round-robin1$inv st))
               (equal (round-robin1$extract next-st)
                      (round-robin1$extracted-step inputs st data-width))))
    :hints (("Goal"
             :use (round-robin1$input-format=>q2$input-format
                   round-robin1$input-format=>q3$input-format)
             :in-theory (e/d (get-field
                              f-sr
                              joint-act
                              len-0-is-atom
                              cons-append-instances
                              queue2$extracted-step
                              queue3$extracted-step
                              round-robin1$extracted-step
                              round-robin1$valid-st
                              round-robin1$inv
                              round-robin1$step
                              round-robin1$in-act
                              round-robin1$out-act
                              round-robin1$extract
                              round-robin1$br-inputs
                              round-robin1$me-inputs
                              alt-branch$valid-st
                              alt-branch$inv
                              alt-branch$act
                              alt-branch$act0
                              alt-branch$act1
                              alt-merge$valid-st
                              alt-merge$inv
                              alt-merge$step
                              alt-merge$act
                              alt-merge$act0
                              alt-merge$act1)
                             (round-robin1$input-format=>q2$input-format
                              round-robin1$input-format=>q3$input-format
                              b-and3
                              b-or3
                              b-not
                              round-robin1$disabled-rules)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that round-robin1$valid-st is an invariant.

(encapsulate
  ()

  (local
   (defthm round-robin1$br-acts-inactive
     (b* ((br-inputs (round-robin1$br-inputs inputs st data-width))
          (br (nth *round-robin1$br* st)))
       (implies (not (nth 0 inputs))
                (and (not (alt-branch$act0 br-inputs br data-width))
                     (not (alt-branch$act1 br-inputs br data-width)))))
     :hints (("Goal" :in-theory (enable round-robin1$br-inputs)))))

  (defthm round-robin1$valid-st-preserved
    (implies (and (round-robin1$input-format inputs data-width)
                  (round-robin1$valid-st st data-width))
             (round-robin1$valid-st
              (round-robin1$step inputs st data-width)
              data-width))
    :hints (("Goal"
             :use (round-robin1$input-format=>q2$input-format
                   round-robin1$input-format=>q3$input-format
                   round-robin1$input-format=>br$input-format
                   round-robin1$input-format=>me$input-format)
             :in-theory (e/d (get-field
                              f-sr
                              round-robin1$input-format
                              round-robin1$valid-st
                              round-robin1$st-format
                              round-robin1$step
                              round-robin1$in-act
                              round-robin1$out-act)
                             (round-robin1$input-format=>q2$input-format
                              round-robin1$input-format=>q3$input-format
                              round-robin1$input-format=>br$input-format
                              round-robin1$input-format=>me$input-format
                              nfix
                              acl2::true-listp-append
                              round-robin1$disabled-rules)))))
  )

(defthm round-robin1$extract-lemma
  (implies (and (round-robin1$valid-st st data-width)
                (round-robin1$inv st)
                (round-robin1$out-act inputs st data-width))
           (equal (list (round-robin1$data-out st))
                  (nthcdr (1- (len (round-robin1$extract st)))
                          (round-robin1$extract st))))
  :hints (("Goal"
           :do-not-induct t
           :use round-robin1$valid-st=>constraint
           :in-theory (e/d (f-and3
                            len-0-is-atom
                            cons-append-instances
                            left-associativity-of-append
                            round-robin1$valid-st
                            round-robin1$inv
                            round-robin1$extract
                            round-robin1$out-act
                            round-robin1$data-out
                            round-robin1$me-inputs
                            alt-merge$valid-st
                            alt-merge$act
                            alt-merge$act0
                            alt-merge$act1)
                           (nfix
                            b-not
                            append
                            associativity-of-append
                            round-robin1$disabled-rules)))))

;; Extract the accepted input sequence

(seq-gen round-robin1 in in-act 0
         (round-robin1$data-in inputs data-width))

;; Extract the valid output sequence

(seq-gen round-robin1 out out-act 1
         (round-robin1$data-out st)
         :netlist-data (nthcdr 2 outputs))

;; The multi-step input-output relationship

(in-out-stream-lemma round-robin1 :inv t)

