;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

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
     take
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

(defun round-robin1$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (mbe :logic (nfix data-size)
            :exec  data-size)))

(defun round-robin1$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (round-robin1$data-ins-len data-size)
     *round-robin1$go-num*))

;; DE module generator of RR1.  The ALT-BRANCH joint in RR1 accepts input data
;; and places them alternately into two queues.  The ALT-MERGE joint takes data
;; alternately from two queues and delivers them as outputs.

(module-generator
 round-robin1* (data-size)
 (si 'round-robin1 data-size)
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 data-size)
                                    (sis 'go 0 *round-robin1$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-size))
 '(a0 b0 a1 b1 q2 q3 br me)
 (list
  ;; LINKS
  ;; A0
  (list 'a0
        (list* 'a0-status (sis 'a0-out 0 data-size))
        (si 'link data-size)
        (list* 'br-act0 'q2-in-act (sis 'data 0 data-size)))

  ;; B0
  (list 'b0
        (list* 'b0-status (sis 'b0-out 0 data-size))
        (si 'link data-size)
        (list* 'br-act1 'q3-in-act (sis 'data 0 data-size)))

  ;; A1
  (list 'a1
        (list* 'a1-status (sis 'a1-out 0 data-size))
        (si 'link data-size)
        (list* 'q2-out-act 'me-act0 (sis 'q2-data-out 0 data-size)))

  ;; B1
  (list 'b1
        (list* 'b1-status (sis 'b1-out 0 data-size))
        (si 'link data-size)
        (list* 'q3-out-act 'me-act1 (sis 'q3-data-out 0 data-size)))

  ;; JOINTS
  ;; 2-link queue Q2
  (list 'q2
        (list* 'q2-in-act 'q2-out-act
               (sis 'q2-data-out 0 data-size))
        (si 'queue2 data-size)
        (list* 'a0-status 'a1-status
               (append (sis 'a0-out 0 data-size)
                       (sis 'go 0 *queue2$go-num*))))

  ;; 3-link queue Q3
  (list 'q3
        (list* 'q3-in-act 'q3-out-act
               (sis 'q3-data-out 0 data-size))
        (si 'queue3 data-size)
        (list* 'b0-status 'b1-status
               (append (sis 'b0-out 0 data-size)
                       (sis 'go
                            *queue2$go-num*
                            *queue3$go-num*))))

  ;; Alt-Branch
  (list 'br
        (list* 'in-act 'br-act0 'br-act1
               (sis 'data 0 data-size))
        (si 'alt-branch data-size)
        (list* 'full-in 'a0-status 'b0-status
               (append (sis 'data-in 0 data-size)
                       (sis 'go
                            (+ *queue2$go-num*
                               *queue3$go-num*)
                            *alt-branch$go-num*))))

  ;; Alt-Merge
  (list 'me
        (list* 'out-act 'me-act0 'me-act1
               (sis 'data-out 0 data-size))
        (si 'alt-merge data-size)
        (list* 'a1-status 'b1-status 'empty-out-
               (append (sis 'a1-out 0 data-size)
                       (sis 'b1-out 0 data-size)
                       (sis 'go
                            (+ *queue2$go-num*
                               *queue3$go-num*
                               *alt-branch$go-num*)
                            *alt-merge$go-num*)))))

 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'round-robin1 '(a0 b0 a1 b1 q2 q3 br me) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of RR1.

(defund round-robin1$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (round-robin1* data-size)
        (union$ (queue2$netlist data-size)
                (queue3$netlist data-size)
                (alt-branch$netlist data-size)
                (alt-merge$netlist data-size)
                :test 'equal)))

;; Recognizer for RR1

(defund round-robin1& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'round-robin1 data-size) netlist)))
    (and (equal (assoc (si 'round-robin1 data-size) netlist)
                (round-robin1* data-size))
         (link& subnetlist data-size)
         (queue2& subnetlist data-size)
         (queue3& subnetlist data-size)
         (alt-branch& subnetlist data-size)
         (alt-merge& subnetlist data-size))))

;; Sanity check

(local
 (defthmd check-round-robin1$netlist-64
   (and (net-syntax-okp (round-robin1$netlist 64))
        (net-arity-okp (round-robin1$netlist 64))
        (round-robin1& (round-robin1$netlist 64) 64))))

;; Constraints on the state of RR1

(defund round-robin1$st-format (st data-size)
  (b* ((a0 (nth *round-robin1$a0* st))
       (b0 (nth *round-robin1$b0* st))
       (a1 (nth *round-robin1$a1* st))
       (b1 (nth *round-robin1$b1* st))
       (q2 (nth *round-robin1$q2* st))
       (q3 (nth *round-robin1$q3* st)))
    (and (< 0 data-size)

         (link$st-format a0 data-size)
         (link$st-format b0 data-size)
         (link$st-format a1 data-size)
         (link$st-format b1 data-size)

         (queue2$st-format q2 data-size)
         (queue3$st-format q3 data-size))))

(defthm round-robin1$st-format=>constraint
  (implies (round-robin1$st-format st data-size)
           (posp data-size))
  :hints (("Goal" :in-theory (enable round-robin1$st-format)))
  :rule-classes :forward-chaining)

(defund round-robin1$valid-st (st data-size)
  (b* ((a0 (nth *round-robin1$a0* st))
       (b0 (nth *round-robin1$b0* st))
       (a1 (nth *round-robin1$a1* st))
       (b1 (nth *round-robin1$b1* st))
       (q2 (nth *round-robin1$q2* st))
       (q3 (nth *round-robin1$q3* st))
       (br (nth *round-robin1$br* st))
       (me (nth *round-robin1$me* st)))
    (and (round-robin1$st-format st data-size)

         (link$valid-st a0 data-size)
         (link$valid-st b0 data-size)
         (link$valid-st a1 data-size)
         (link$valid-st b1 data-size)

         (queue2$valid-st q2 data-size)
         (queue3$valid-st q3 data-size)

         (alt-branch$valid-st br)
         (alt-merge$valid-st me))))

(defthmd round-robin1$valid-st=>constraint
  (implies (round-robin1$valid-st st data-size)
           (posp data-size))
  :hints (("Goal" :in-theory (enable round-robin1$valid-st)))
  :rule-classes :forward-chaining)

(defthmd round-robin1$valid-st=>st-format
  (implies (round-robin1$valid-st st data-size)
           (round-robin1$st-format st data-size))
  :hints (("Goal" :in-theory (e/d (round-robin1$valid-st)
                                  ()))))

;; Extract the input and output signals for RR1

(progn
  ;; Extract the input data

  (defun round-robin1$data-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (mbe :logic (nfix data-size)
               :exec  data-size)
          (nthcdr 2 inputs)))

  (defthm len-round-robin1$data-in
    (equal (len (round-robin1$data-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable round-robin1$data-in))

  ;; Extract the inputs for the Q2 joint

  (defund round-robin1$q2-inputs (inputs st data-size)
    (b* ((go-signals (nthcdr (round-robin1$data-ins-len data-size) inputs))

         (q2-go-signals (take *queue2$go-num* go-signals))

         (a0 (nth *round-robin1$a0* st))
         (a0.s (nth *link$s* a0))
         (a0.d (nth *link$d* a0))
         (a1 (nth *round-robin1$a1* st))
         (a1.s (nth *link$s* a1)))

      (list* (f-buf (car a0.s)) (f-buf (car a1.s))
             (append (v-threefix (strip-cars a0.d))
                     q2-go-signals))))

  ;; Extract the inputs for the Q3 joint

  (defund round-robin1$q3-inputs (inputs st data-size)
    (b* ((go-signals (nthcdr (round-robin1$data-ins-len data-size) inputs))

         (q3-go-signals (take *queue3$go-num*
                              (nthcdr *queue2$go-num*
                                      go-signals)))

         (b0 (nth *round-robin1$b0* st))
         (b0.s (nth *link$s* b0))
         (b0.d (nth *link$d* b0))
         (b1 (nth *round-robin1$b1* st))
         (b1.s (nth *link$s* b1)))

      (list* (f-buf (car b0.s)) (f-buf (car b1.s))
             (append (v-threefix (strip-cars b0.d))
                     q3-go-signals))))

  ;; Extract the inputs for the alt-branch joint

  (defund round-robin1$br-inputs (inputs st data-size)
    (b* ((full-in    (nth 0 inputs))
         (data-in    (round-robin1$data-in inputs data-size))
         (go-signals (nthcdr (round-robin1$data-ins-len data-size) inputs))

         (br-go-signals (take *alt-branch$go-num*
                              (nthcdr (+ *queue2$go-num*
                                         *queue3$go-num*)
                                      go-signals)))

         (a0 (nth *round-robin1$a0* st))
         (a0.s (nth *link$s* a0))
         (b0 (nth *round-robin1$b0* st))
         (b0.s (nth *link$s* b0)))

      (list* full-in (f-buf (car a0.s)) (f-buf (car b0.s))
             (append data-in br-go-signals))))

  ;; Extract the inputs for the alt-merge joint

  (defund round-robin1$me-inputs (inputs st data-size)
    (b* ((empty-out-  (nth 1 inputs))
         (go-signals (nthcdr (round-robin1$data-ins-len data-size) inputs))

         (me-go-signals (take *alt-merge$go-num*
                              (nthcdr (+ *queue2$go-num*
                                         *queue3$go-num*
                                         *alt-branch$go-num*)
                                      go-signals)))

         (a1 (nth *round-robin1$a1* st))
         (a1.s (nth *link$s* a1))
         (a1.d (nth *link$d* a1))
         (b1 (nth *round-robin1$b1* st))
         (b1.s (nth *link$s* b1))
         (b1.d (nth *link$d* b1)))

      (list* (f-buf (car a1.s)) (f-buf (car b1.s)) empty-out-
             (append (v-threefix (strip-cars a1.d))
                     (v-threefix (strip-cars b1.d))
                     me-go-signals))))

  ;; Extract the "in-act" signal

  (defund round-robin1$in-act (inputs st data-size)
    (b* ((br-inputs (round-robin1$br-inputs inputs st data-size))
         (br (nth *round-robin1$br* st)))
      (alt-branch$act br-inputs br data-size)))

  (defthm round-robin1$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (round-robin1$in-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable round-robin1$br-inputs
                                       round-robin1$in-act))))

  ;; Extract the "out-act" signal

  (defund round-robin1$out-act (inputs st data-size)
    (b* ((me-inputs (round-robin1$me-inputs inputs st data-size))
         (me (nth *round-robin1$me* st)))
      (alt-merge$act me-inputs me data-size)))

  (defthm round-robin1$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (round-robin1$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable round-robin1$me-inputs
                                       round-robin1$out-act))))

  ;; Extract the output data

  (defund round-robin1$data-out (st)
    (b* ((a1 (nth *round-robin1$a1* st))
         (a1.d (nth *link$d* a1))
         (b1 (nth *round-robin1$b1* st))
         (b1.d (nth *link$d* b1))
         (me (nth *round-robin1$me* st))

         (me-select (nth *alt-merge$select* me))
         (me-select.d (nth *link1$d* me-select)))
      (fv-if (car me-select.d)
             (strip-cars b1.d)
             (strip-cars a1.d))))

  (defthm len-round-robin1$data-out-1
    (implies (round-robin1$st-format st data-size)
             (equal (len (round-robin1$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable round-robin1$st-format
                                       round-robin1$data-out))))

  (defthm len-round-robin1$data-out-2
    (implies (round-robin1$valid-st st data-size)
             (equal (len (round-robin1$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable round-robin1$valid-st
                                       round-robin1$data-out))))

  (defthm bvp-round-robin1$data-out
    (implies (and (round-robin1$valid-st st data-size)
                  (round-robin1$out-act inputs st data-size))
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

  (defun round-robin1$outputs (inputs st data-size)
    (list* (round-robin1$in-act inputs st data-size)
           (round-robin1$out-act inputs st data-size)
           (round-robin1$data-out st)))
  )

;; The value lemma for RR1

(defthm round-robin1$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (round-robin1& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *round-robin1$go-num*)
                  (round-robin1$st-format st data-size))
             (equal (se (si 'round-robin1 data-size) inputs st netlist)
                    (round-robin1$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'round-robin1 data-size)
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

(defun round-robin1$step (inputs st data-size)
  (b* ((data-in (round-robin1$data-in inputs data-size))

       (a0 (nth *round-robin1$a0* st))
       (b0 (nth *round-robin1$b0* st))
       (a1 (nth *round-robin1$a1* st))
       (b1 (nth *round-robin1$b1* st))
       (q2 (nth *round-robin1$q2* st))
       (q3 (nth *round-robin1$q3* st))
       (br (nth *round-robin1$br* st))
       (me (nth *round-robin1$me* st))

       (q2-inputs (round-robin1$q2-inputs inputs st data-size))
       (q2-in-act (queue2$in-act q2-inputs q2 data-size))
       (q2-out-act (queue2$out-act q2-inputs q2 data-size))
       (q2-data-out (queue2$data-out q2))

       (q3-inputs (round-robin1$q3-inputs inputs st data-size))
       (q3-in-act (queue3$in-act q3-inputs q3 data-size))
       (q3-out-act (queue3$out-act q3-inputs q3 data-size))
       (q3-data-out (queue3$data-out q3))

       (br-inputs (round-robin1$br-inputs inputs st data-size))
       (br-act0 (alt-branch$act0 br-inputs br data-size))
       (br-act1 (alt-branch$act1 br-inputs br data-size))

       (me-inputs (round-robin1$me-inputs inputs st data-size))
       (me-act0 (alt-merge$act0 me-inputs me data-size))
       (me-act1 (alt-merge$act1 me-inputs me data-size))

       (a0-inputs (list* br-act0 q2-in-act data-in))
       (b0-inputs (list* br-act1 q3-in-act data-in))
       (a1-inputs (list* q2-out-act me-act0 q2-data-out))
       (b1-inputs (list* q3-out-act me-act1 q3-data-out)))

    (list
     ;; A0
     (link$step a0-inputs a0 data-size)
     ;; B0
     (link$step b0-inputs b0 data-size)
     ;; A1
     (link$step a1-inputs a1 data-size)
     ;; B1
     (link$step b1-inputs b1 data-size)

     ;; Joint Q2
     (queue2$step q2-inputs q2 data-size)
     ;; Joint Q3
     (queue3$step q3-inputs q3 data-size)
     ;; Joint ALT-BRANCH
     (alt-branch$step br-inputs br data-size)
     ;; Joint ALT-MERGE
     (alt-merge$step me-inputs me data-size))))

;; The state lemma for RR1

(defthm round-robin1$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (round-robin1& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *round-robin1$go-num*)
                  (round-robin1$st-format st data-size))
             (equal (de (si 'round-robin1 data-size) inputs st netlist)
                    (round-robin1$step inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'round-robin1 data-size)
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

(defund round-robin1$input-format (inputs data-size)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-size))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (round-robin1$data-in inputs data-size))
       (go-signals (nthcdr (round-robin1$data-ins-len data-size) inputs)))
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
   (implies (and (round-robin1$input-format inputs data-size)
                 (round-robin1$valid-st st data-size))
            (queue2$input-format
             (round-robin1$q2-inputs inputs st data-size)
             data-size))
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
   (implies (and (round-robin1$input-format inputs data-size)
                 (round-robin1$valid-st st data-size))
            (queue3$input-format
             (round-robin1$q3-inputs inputs st data-size)
             data-size))
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
   (implies (and (round-robin1$input-format inputs data-size)
                 (round-robin1$valid-st st data-size))
            (alt-branch$input-format
             (round-robin1$br-inputs inputs st data-size)
             data-size))
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
   (implies (and (round-robin1$input-format inputs data-size)
                 (round-robin1$valid-st st data-size))
            (alt-merge$input-format
             (round-robin1$me-inputs inputs st data-size)
             data-size))
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
  (implies (and (round-robin1$input-format inputs data-size)
                (round-robin1$valid-st st data-size))
           (booleanp (round-robin1$in-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (enable round-robin1$valid-st
                              round-robin1$in-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-round-robin1$out-act
  (implies (and (round-robin1$input-format inputs data-size)
                (round-robin1$valid-st st data-size))
           (booleanp (round-robin1$out-act inputs st data-size)))
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
  (b* ((a0 (nth *round-robin1$a0* st))
       (b0 (nth *round-robin1$b0* st))
       (a1 (nth *round-robin1$a1* st))
       (b1 (nth *round-robin1$b1* st))
       (q2 (nth *round-robin1$q2* st))
       (q3 (nth *round-robin1$q3* st))
       (me (nth *round-robin1$me* st))

       (a-seq (append (extract-valid-data (list a0))
                      (queue2$extract q2)
                      (extract-valid-data (list a1))))
       (b-seq (append (extract-valid-data (list b0))
                      (queue3$extract q3)
                      (extract-valid-data (list b1))))

       (me-select (nth *alt-merge$select* me))
       (me-select.s (nth *link1$s* me-select))
       (me-select.d (nth *link1$d* me-select))
       (me-select-buf (nth *alt-merge$select-buf* me))
       (me-select-buf.d (nth *link1$d* me-select-buf))
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
  (implies (and (round-robin1$out-act inputs st data-size)
                (round-robin1$valid-st st data-size))
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
    (b* ((a0 (nth *round-robin1$a0* st))
         (b0 (nth *round-robin1$b0* st))
         (a1 (nth *round-robin1$a1* st))
         (b1 (nth *round-robin1$b1* st))
         (q2 (nth *round-robin1$q2* st))
         (q3 (nth *round-robin1$q3* st))
         (br (nth *round-robin1$br* st))
         (me (nth *round-robin1$me* st))

         (a-seq (append (extract-valid-data (list a0))
                        (queue2$extract q2)
                        (extract-valid-data (list a1))))
         (b-seq (append (extract-valid-data (list b0))
                        (queue3$extract q3)
                        (extract-valid-data (list b1))))

         (br-select (nth *alt-branch$select* br))
         (br-select.s (nth *link1$s* br-select))
         (br-select.d (nth *link1$d* br-select))
         (br-select-buf (nth *alt-branch$select-buf* br))
         (br-select-buf.d (nth *link1$d* br-select-buf))
         (valid-br-select (if (fullp br-select.s)
                              (car br-select.d)
                            (car br-select-buf.d)))

         (me-select (nth *alt-merge$select* me))
         (me-select.s (nth *link1$s* me-select))
         (me-select.d (nth *link1$d* me-select))
         (me-select-buf (nth *alt-merge$select-buf* me))
         (me-select-buf.d (nth *link1$d* me-select-buf))
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
     (implies (round-robin1$input-format inputs data-size)
              (booleanp (nth 0 inputs)))
     :hints (("Goal" :in-theory (enable round-robin1$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm round-robin1$input-format-lemma-2
     (implies (round-robin1$input-format inputs data-size)
              (booleanp (nth 1 inputs)))
     :hints (("Goal" :in-theory (enable round-robin1$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm round-robin1$input-format-lemma-3
     (implies (and (round-robin1$input-format inputs data-size)
                   (nth 0 inputs))
              (bvp (round-robin1$data-in inputs data-size)))
     :hints (("Goal" :in-theory (enable round-robin1$input-format)))))

  (local
   (defthm round-robin1$q2-in-act-inactive
     (implies (equal (nth *link$s*
                          (nth *round-robin1$a0* st))
                     '(nil))
              (not (queue2$in-act
                    (round-robin1$q2-inputs inputs st data-size)
                    (nth *round-robin1$q2* st)
                    data-size)))
     :hints (("Goal"
              :in-theory (enable round-robin1$q2-inputs)))))

  (local
   (defthm round-robin1$q3-in-act-inactive
     (implies (equal (nth *link$s*
                          (nth *round-robin1$b0* st))
                     '(nil))
              (not (queue3$in-act
                    (round-robin1$q3-inputs inputs st data-size)
                    (nth *round-robin1$q3* st)
                    data-size)))
     :hints (("Goal"
              :in-theory (enable round-robin1$q3-inputs)))))

  (local
   (defthm round-robin1$q2-out-act-inactive
     (implies (equal (nth *link$s*
                          (nth *round-robin1$a1* st))
                     '(t))
              (not (queue2$out-act
                    (round-robin1$q2-inputs inputs st data-size)
                    (nth *round-robin1$q2* st)
                    data-size)))
     :hints (("Goal"
              :in-theory (enable round-robin1$q2-inputs)))))

  (local
   (defthm round-robin1$q3-out-act-inactive
     (implies (equal (nth *link$s*
                          (nth *round-robin1$b1* st))
                     '(t))
              (not (queue3$out-act
                    (round-robin1$q3-inputs inputs st data-size)
                    (nth *round-robin1$q3* st)
                    data-size)))
     :hints (("Goal"
              :in-theory (enable round-robin1$q3-inputs)))))

  (local
   (defthm round-robin1$br-act0-inactive
     (implies (equal (nth *link$s*
                          (nth *round-robin1$a0* st))
                     '(t))
              (not (alt-branch$act0
                    (round-robin1$br-inputs inputs st data-size)
                    (nth *round-robin1$br* st)
                    data-size)))
     :hints (("Goal"
              :in-theory (enable round-robin1$br-inputs)))))

  (local
   (defthm round-robin1$br-act1-inactive
     (implies (equal (nth *link$s*
                          (nth *round-robin1$b0* st))
                     '(t))
              (not (alt-branch$act1
                    (round-robin1$br-inputs inputs st data-size)
                    (nth *round-robin1$br* st)
                    data-size)))
     :hints (("Goal"
              :in-theory (enable round-robin1$br-inputs)))))

  (local
   (defthm round-robin1$me-act0-inactive
     (implies (equal (nth *link$s*
                          (nth *round-robin1$a1* st))
                     '(nil))
              (not (alt-merge$act0
                    (round-robin1$me-inputs inputs st data-size)
                    (nth *round-robin1$me* st)
                    data-size)))
     :hints (("Goal"
              :in-theory (enable round-robin1$me-inputs)))))

  (local
   (defthm round-robin1$me-act1-inactive
     (implies (equal (nth *link$s*
                          (nth *round-robin1$b1* st))
                     '(nil))
              (not (alt-merge$act1
                    (round-robin1$me-inputs inputs st data-size)
                    (nth *round-robin1$me* st)
                    data-size)))
     :hints (("Goal"
              :in-theory (enable round-robin1$me-inputs)))))

  (defthm round-robin1$inv-preserved
    (implies (and (round-robin1$input-format inputs data-size)
                  (round-robin1$valid-st st data-size)
                  (round-robin1$inv st))
             (round-robin1$inv
              (round-robin1$step inputs st data-size)))
    :hints (("Goal"
             :use (round-robin1$input-format=>q2$input-format
                   round-robin1$input-format=>q3$input-format)
             :in-theory (e/d (f-sr
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

(defund round-robin1$extracted-step (inputs st data-size)
  (b* ((data (round-robin1$data-in inputs data-size))
       (extracted-st (round-robin1$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (round-robin1$out-act inputs st data-size) t)
      (cond
       ((equal (round-robin1$in-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (round-robin1$in-act inputs st data-size) t)
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
     (implies (and (queue2$out-act inputs st data-size)
                   (queue2$valid-st st data-size))
              (consp (queue2$extract st)))
     :hints (("Goal"
              :in-theory (enable queue2$valid-st
                                 queue2$extract
                                 queue2$out-act)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm consp-queue3$extract
     (implies (and (queue3$out-act inputs st data-size)
                   (queue3$valid-st st data-size))
              (consp (queue3$extract st)))
     :hints (("Goal"
              :in-theory (enable queue3$valid-st
                                 queue3$extract
                                 queue3$out-act)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm round-robin1$q2-get-$data-in-rewrite
     (b* ((a0 (nth *round-robin1$a0* st))
          (a0.d (nth *link$d* a0)))
       (implies (and (bvp (strip-cars a0.d))
                     (equal (len a0.d) data-size))
                (equal (queue2$data-in
                        (round-robin1$q2-inputs inputs st data-size)
                        data-size)
                       (strip-cars a0.d))))
     :hints (("Goal"
              :in-theory (enable queue2$data-in
                                 round-robin1$q2-inputs)))))

  (local
   (defthm round-robin1$q3-get-$data-in-rewrite
     (b* ((b0 (nth *round-robin1$b0* st))
          (b0.d (nth *link$d* b0)))
       (implies (and (bvp (strip-cars b0.d))
                     (equal (len b0.d) data-size))
                (equal (queue3$data-in
                        (round-robin1$q3-inputs inputs st data-size)
                        data-size)
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
    (b* ((next-st (round-robin1$step inputs st data-size)))
      (implies (and (round-robin1$input-format inputs data-size)
                    (round-robin1$valid-st st data-size)
                    (round-robin1$inv st))
               (equal (round-robin1$extract next-st)
                      (round-robin1$extracted-step inputs st data-size))))
    :hints (("Goal"
             :use (round-robin1$input-format=>q2$input-format
                   round-robin1$input-format=>q3$input-format)
             :in-theory (e/d (f-sr
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
     (b* ((br-inputs (round-robin1$br-inputs inputs st data-size))
          (br (nth *round-robin1$br* st)))
       (implies (not (nth 0 inputs))
                (and (not (alt-branch$act0 br-inputs br data-size))
                     (not (alt-branch$act1 br-inputs br data-size)))))
     :hints (("Goal" :in-theory (enable round-robin1$br-inputs)))))

  (defthm round-robin1$valid-st-preserved
    (implies (and (round-robin1$input-format inputs data-size)
                  (round-robin1$valid-st st data-size))
             (round-robin1$valid-st
              (round-robin1$step inputs st data-size)
              data-size))
    :hints (("Goal"
             :use (round-robin1$input-format=>q2$input-format
                   round-robin1$input-format=>q3$input-format
                   round-robin1$input-format=>br$input-format
                   round-robin1$input-format=>me$input-format)
             :in-theory (e/d (f-sr
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
  (implies (and (round-robin1$valid-st st data-size)
                (round-robin1$inv st)
                (round-robin1$out-act inputs st data-size))
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
         (round-robin1$data-in inputs data-size))

;; Extract the valid output sequence

(seq-gen round-robin1 out out-act 1
         (round-robin1$data-out st)
         :netlist-data (nthcdr 2 outputs))

;; The multi-step input-output relationship

(in-out-stream-lemma round-robin1 :inv t)
