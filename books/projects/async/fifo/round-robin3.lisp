;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "alt-branch")
(include-book "alt-merge")
(include-book "queue8-l")
(include-book "queue10-l")

(local (include-book "arithmetic-5/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of RR3
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of RR3
;;
;; Construct a DE module generator for round-robin circuits using the
;; link-joint model.  Prove the value and state lemmas for this module
;; generator.

(defconst *round-robin3$go-num* (+ *queue8-l$go-num*
                                   *queue10-l$go-num*
                                   *alt-branch$go-num*
                                   *alt-merge$go-num*))

(defconst *round-robin3$go-branch-offset*
  (+ 2 *queue8-l$go-num* *queue10-l$go-num*))

(defconst *round-robin3$go-merge-offset*
  (+ 2 *queue8-l$go-num* *queue10-l$go-num* *alt-branch$go-num*))

(defun round-robin3$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (mbe :logic (nfix data-size)
            :exec  data-size)))

(defun round-robin3$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (round-robin3$data-ins-len data-size)
     *round-robin3$go-num*))

;; DE module generator of RR3.  The ALT-BRANCH joint in RR3 accepts input data
;; and places them alternately into two queues.  The ALT-MERGE joint takes data
;; alternately from two queues and delivers them as outputs.

(module-generator
 round-robin3* (data-size)
 (si 'round-robin3 data-size)
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 data-size)
                                    (sis 'go 0 *round-robin3$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-size))
 '(q8-l q10-l br me)
 (list
  ;; LINKS
  ;; 8-link queue Q8-L
  (list 'q8-l
        (list* 'q8-l-ready-in- 'q8-l-ready-out
               (sis 'q8-l-data-out 0 data-size))
        (si 'queue8-l data-size)
        (list* 'br-act0 'me-act0
               (append (sis 'data 0 data-size)
                       (sis 'go 0 *queue8-l$go-num*))))

  ;; 10-link queue Q10-L
  (list 'q10-l
        (list* 'q10-l-ready-in- 'q10-l-ready-out
               (sis 'q10-l-data-out 0 data-size))
        (si 'queue10-l data-size)
        (list* 'br-act1 'me-act1
               (append (sis 'data 0 data-size)
                       (sis 'go
                            *queue8-l$go-num*
                            *queue10-l$go-num*))))

  ;; JOINTS
  ;; Alt-Branch
  (list 'br
        (list* 'in-act 'br-act0 'br-act1
               (sis 'data 0 data-size))
        (si 'alt-branch data-size)
        (list* 'full-in 'q8-l-ready-in- 'q10-l-ready-in-
               (append (sis 'data-in 0 data-size)
                       (sis 'go
                            (+ *queue8-l$go-num*
                               *queue10-l$go-num*)
                            *alt-branch$go-num*))))

  ;; Alt-Merge
  (list 'me
        (list* 'out-act 'me-act0 'me-act1
               (sis 'data-out 0 data-size))
        (si 'alt-merge data-size)
        (list* 'q8-l-ready-out 'q10-l-ready-out 'empty-out-
               (append (sis 'q8-l-data-out 0 data-size)
                       (sis 'q10-l-data-out 0 data-size)
                       (sis 'go
                            (+ *queue8-l$go-num*
                               *queue10-l$go-num*
                               *alt-branch$go-num*)
                            *alt-merge$go-num*)))))

 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'round-robin3 '(q8-l q10-l br me) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of RR3.

(defund round-robin3$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (round-robin3* data-size)
        (union$ (queue8-l$netlist data-size)
                (queue10-l$netlist data-size)
                (alt-branch$netlist data-size)
                (alt-merge$netlist data-size)
                :test 'equal)))

;; Recognizer for RR3

(defund round-robin3& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'round-robin3 data-size) netlist)))
    (and (equal (assoc (si 'round-robin3 data-size) netlist)
                (round-robin3* data-size))
         (queue8-l& subnetlist data-size)
         (queue10-l& subnetlist data-size)
         (alt-branch& subnetlist data-size)
         (alt-merge& subnetlist data-size))))

;; Sanity check

(local
 (defthmd check-round-robin3$netlist-64
   (and (net-syntax-okp (round-robin3$netlist 64))
        (net-arity-okp (round-robin3$netlist 64))
        (round-robin3& (round-robin3$netlist 64) 64))))

;; Constraints on the state of RR3

(defund round-robin3$st-format (st data-size)
  (b* ((q8-l (nth *round-robin3$q8-l* st))
       (q10-l (nth *round-robin3$q10-l* st)))
    (and (< 0 data-size)
         (queue8-l$st-format q8-l data-size)
         (queue10-l$st-format q10-l data-size))))

(defthm round-robin3$st-format=>constraint
  (implies (round-robin3$st-format st data-size)
           (posp data-size))
  :hints (("Goal" :in-theory (enable round-robin3$st-format)))
  :rule-classes :forward-chaining)

(defund round-robin3$valid-st (st data-size)
  (b* ((q8-l (nth *round-robin3$q8-l* st))
       (q10-l (nth *round-robin3$q10-l* st))
       (br (nth *round-robin3$br* st))
       (me (nth *round-robin3$me* st)))
    (and (< 0 data-size)
         (queue8-l$valid-st q8-l data-size)
         (queue10-l$valid-st q10-l data-size)

         (alt-branch$valid-st br)
         (alt-merge$valid-st me))))

(defthmd round-robin3$valid-st=>constraint
  (implies (round-robin3$valid-st st data-size)
           (posp data-size))
  :hints (("Goal" :in-theory (enable round-robin3$valid-st
                                     queue8-l$valid-st=>constraint)))
  :rule-classes :forward-chaining)

(defthmd round-robin3$valid-st=>st-format
  (implies (round-robin3$valid-st st data-size)
           (round-robin3$st-format st data-size))
  :hints (("Goal" :in-theory (e/d (queue8-l$valid-st=>st-format
                                   queue10-l$valid-st=>st-format
                                   round-robin3$st-format
                                   round-robin3$valid-st)
                                  ()))))

;; Extract the input and output signals for RR3

(progn
  ;; Extract the input data

  (defun round-robin3$data-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (mbe :logic (nfix data-size)
               :exec  data-size)
          (nthcdr 2 inputs)))

  (defthm len-round-robin3$data-in
    (equal (len (round-robin3$data-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable round-robin3$data-in))

  ;; Extract the inputs for the alt-branch joint

  (defund round-robin3$br-inputs (inputs st data-size)
    (b* ((full-in (nth 0 inputs))
         (data-in (round-robin3$data-in inputs data-size))
         (go-signals (nthcdr (round-robin3$data-ins-len data-size) inputs))

         (br-go-signals (take *alt-branch$go-num*
                              (nthcdr (+ *queue8-l$go-num*
                                         *queue10-l$go-num*)
                                      go-signals)))

         (q8-l (nth *round-robin3$q8-l* st))
         (q10-l (nth *round-robin3$q10-l* st))

         (q8-l-ready-in- (queue8-l$ready-in- q8-l))
         (q10-l-ready-in- (queue10-l$ready-in- q10-l)))

      (list* full-in q8-l-ready-in- q10-l-ready-in-
             (append data-in br-go-signals))))

  ;; Extract the inputs for the alt-merge joint

  (defund round-robin3$me-inputs (inputs st data-size)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (round-robin3$data-ins-len data-size) inputs))

         (me-go-signals (take *alt-merge$go-num*
                              (nthcdr (+ *queue8-l$go-num*
                                         *queue10-l$go-num*
                                         *alt-branch$go-num*)
                                      go-signals)))

         (q8-l (nth *round-robin3$q8-l* st))
         (q10-l (nth *round-robin3$q10-l* st))

         (q8-l-ready-out (queue8-l$ready-out q8-l))
         (q8-l-data-out (queue8-l$data-out q8-l))
         (q10-l-ready-out (queue10-l$ready-out q10-l))
         (q10-l-data-out (queue10-l$data-out q10-l)))

      (list* q8-l-ready-out q10-l-ready-out empty-out-
             (append q8-l-data-out q10-l-data-out me-go-signals))))

  ;; Extract the inputs for the Q8-L' link

  (defund round-robin3$q8-l-inputs (inputs st data-size)
    (b* ((data-in (round-robin3$data-in inputs data-size))
         (go-signals (nthcdr (round-robin3$data-ins-len data-size) inputs))

         (q8-l-go-signals (take *queue8-l$go-num* go-signals))

         (br (nth *round-robin3$br* st))
         (me (nth *round-robin3$me* st))

         (br-inputs (round-robin3$br-inputs inputs st data-size))
         (me-inputs (round-robin3$me-inputs inputs st data-size))

         (br-act0 (alt-branch$act0 br-inputs br data-size))
         (me-act0 (alt-merge$act0 me-inputs me data-size)))

      (list* br-act0 me-act0
             (append data-in
                     q8-l-go-signals))))

  ;; Extract the inputs for the Q10-L' link

  (defund round-robin3$q10-l-inputs (inputs st data-size)
    (b* ((data-in (round-robin3$data-in inputs data-size))
         (go-signals (nthcdr (round-robin3$data-ins-len data-size) inputs))

         (q10-l-go-signals (take *queue10-l$go-num*
                               (nthcdr *queue8-l$go-num*
                                       go-signals)))

         (br (nth *round-robin3$br* st))
         (me (nth *round-robin3$me* st))

         (br-inputs (round-robin3$br-inputs inputs st data-size))
         (me-inputs (round-robin3$me-inputs inputs st data-size))

         (br-act1 (alt-branch$act1 br-inputs br data-size))
         (me-act1 (alt-merge$act1 me-inputs me data-size)))

      (list* br-act1 me-act1
             (append data-in
                     q10-l-go-signals))))

  ;; Extract the "in-act" signal

  (defund round-robin3$in-act (inputs st data-size)
    (b* ((br-inputs (round-robin3$br-inputs inputs st data-size))
         (br (nth *round-robin3$br* st)))
      (alt-branch$act br-inputs br data-size)))

  (defthm round-robin3$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (round-robin3$in-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable round-robin3$br-inputs
                                       round-robin3$in-act))))

  ;; Extract the "out-act" signal

  (defund round-robin3$out-act (inputs st data-size)
    (b* ((me-inputs (round-robin3$me-inputs inputs st data-size))
         (me (nth *round-robin3$me* st)))
      (alt-merge$act me-inputs me data-size)))

  (defthm round-robin3$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (round-robin3$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable round-robin3$me-inputs
                                       round-robin3$out-act))))

  ;; Extract the output data

  (defund round-robin3$data-out (st)
    (b* ((q8-l (nth *round-robin3$q8-l* st))
         (q10-l (nth *round-robin3$q10-l* st))
         (me (nth *round-robin3$me* st))

         (q8-l-data-out (queue8-l$data-out q8-l))
         (q10-l-data-out (queue10-l$data-out q10-l))

         (me-select (nth *alt-merge$select* me))
         (me-select.d (nth *link1$d* me-select)))
      (fv-if (car me-select.d)
             q10-l-data-out
             q8-l-data-out)))

  (defthm len-round-robin3$data-out-1
    (implies (round-robin3$st-format st data-size)
             (equal (len (round-robin3$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable round-robin3$st-format
                                       round-robin3$data-out))))

  (defthm len-round-robin3$data-out-2
    (implies (round-robin3$valid-st st data-size)
             (equal (len (round-robin3$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable round-robin3$valid-st
                                       round-robin3$data-out))))

  (defthm bvp-round-robin3$data-out
    (implies (and (round-robin3$valid-st st data-size)
                  (round-robin3$out-act inputs st data-size))
             (bvp (round-robin3$data-out st)))
    :hints (("Goal" :in-theory (enable f-and3
                                       f-and
                                       joint-act
                                       round-robin3$valid-st
                                       round-robin3$out-act
                                       round-robin3$data-out
                                       round-robin3$me-inputs
                                       queue8-l$valid-st=>constraint
                                       alt-merge$valid-st
                                       alt-merge$act
                                       alt-merge$act0
                                       alt-merge$act1))))

  (defun round-robin3$outputs (inputs st data-size)
    (list* (round-robin3$in-act inputs st data-size)
           (round-robin3$out-act inputs st data-size)
           (round-robin3$data-out st)))
  )

;; The value lemma for RR3

(defthm round-robin3$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (round-robin3& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *round-robin3$go-num*)
                  (round-robin3$st-format st data-size))
             (equal (se (si 'round-robin3 data-size) inputs st netlist)
                    (round-robin3$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'round-robin3 data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            round-robin3&
                            round-robin3*$destructure
                            round-robin3$data-in
                            round-robin3$st-format
                            round-robin3$in-act
                            round-robin3$out-act
                            round-robin3$data-out
                            round-robin3$br-inputs
                            round-robin3$me-inputs)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of RR3.

(defun round-robin3$step (inputs st data-size)
  (b* ((q8-l (nth *round-robin3$q8-l* st))
       (q10-l (nth *round-robin3$q10-l* st))
       (br (nth *round-robin3$br* st))
       (me (nth *round-robin3$me* st))

       (q8-l-inputs (round-robin3$q8-l-inputs inputs st data-size))
       (q10-l-inputs (round-robin3$q10-l-inputs inputs st data-size))
       (br-inputs (round-robin3$br-inputs inputs st data-size))
       (me-inputs (round-robin3$me-inputs inputs st data-size)))

    (list
     ;; Q8-L'
     (queue8-l$step q8-l-inputs q8-l data-size)
     ;; Q10-L'
     (queue10-l$step q10-l-inputs q10-l data-size)
     ;; Joint ALT-BRANCH
     (alt-branch$step br-inputs br data-size)
     ;; Joint ALT-MERGE
     (alt-merge$step me-inputs me data-size))))

;; The state lemma for RR3

(defthm round-robin3$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (round-robin3& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *round-robin3$go-num*)
                  (round-robin3$st-format st data-size))
             (equal (de (si 'round-robin3 data-size) inputs st netlist)
                    (round-robin3$step inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'round-robin3 data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            round-robin3&
                            round-robin3*$destructure
                            round-robin3$st-format
                            round-robin3$data-in
                            round-robin3$q8-l-inputs
                            round-robin3$q10-l-inputs
                            round-robin3$br-inputs
                            round-robin3$me-inputs)
                           (de-module-disabled-rules)))))

(in-theory (disable round-robin3$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund round-robin3$input-format (inputs data-size)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-size))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (round-robin3$data-in inputs data-size))
       (go-signals (nthcdr (round-robin3$data-ins-len data-size) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *round-robin3$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(local
 (defthm round-robin3$input-format=>q8-l$input-format
   (implies (and (round-robin3$input-format inputs data-size)
                 (round-robin3$valid-st st data-size))
            (queue8-l$input-format
             (round-robin3$q8-l-inputs inputs st data-size)
             (nth *round-robin3$q8-l* st)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (f-and3
                             queue8-l$valid-st=>constraint
                             queue8-l$input-format
                             queue8-l$in-act
                             queue8-l$out-act
                             queue8-l$data-in
                             alt-branch$valid-st
                             alt-branch$act
                             alt-branch$act0
                             alt-merge$valid-st
                             alt-merge$act
                             alt-merge$act0
                             round-robin3$input-format
                             round-robin3$valid-st
                             round-robin3$q8-l-inputs
                             round-robin3$br-inputs
                             round-robin3$me-inputs)
                            (nfix
                             b-not
                             take-of-too-many))))))

(local
 (defthm round-robin3$input-format=>q10-l$input-format
   (implies (and (round-robin3$input-format inputs data-size)
                 (round-robin3$valid-st st data-size))
            (queue10-l$input-format
             (round-robin3$q10-l-inputs inputs st data-size)
             (nth *round-robin3$q10-l* st)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (f-and3
                             queue10-l$valid-st=>constraint
                             queue10-l$input-format
                             queue10-l$in-act
                             queue10-l$out-act
                             queue10-l$data-in
                             alt-branch$valid-st
                             alt-branch$act
                             alt-branch$act1
                             alt-merge$valid-st
                             alt-merge$act
                             alt-merge$act1
                             round-robin3$input-format
                             round-robin3$valid-st
                             round-robin3$q10-l-inputs
                             round-robin3$br-inputs
                             round-robin3$me-inputs)
                            (nfix
                             b-not
                             take-of-too-many))))))

(local
 (defthm round-robin3$input-format=>br$input-format
   (implies (and (round-robin3$input-format inputs data-size)
                 (round-robin3$valid-st st data-size))
            (alt-branch$input-format
             (round-robin3$br-inputs inputs st data-size)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (queue8-l$valid-st=>constraint
                             alt-branch$input-format
                             alt-branch$data-in
                             round-robin3$input-format
                             round-robin3$valid-st
                             round-robin3$br-inputs)
                            (nfix
                             take-of-too-many))))))

(local
 (defthm round-robin3$input-format=>me$input-format
   (implies (and (round-robin3$input-format inputs data-size)
                 (round-robin3$valid-st st data-size))
            (alt-merge$input-format
             (round-robin3$me-inputs inputs st data-size)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (queue8-l$valid-st=>constraint
                             alt-merge$input-format
                             alt-merge$data0-in
                             alt-merge$data1-in
                             round-robin3$input-format
                             round-robin3$valid-st
                             round-robin3$me-inputs)
                            (take-of-too-many))))))

(defthm booleanp-round-robin3$in-act
  (implies (and (round-robin3$input-format inputs data-size)
                (round-robin3$valid-st st data-size))
           (booleanp (round-robin3$in-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (enable round-robin3$valid-st
                              round-robin3$in-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-round-robin3$out-act
  (implies (and (round-robin3$input-format inputs data-size)
                (round-robin3$valid-st st data-size))
           (booleanp (round-robin3$out-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (enable round-robin3$valid-st
                              round-robin3$out-act)))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma round-robin3)

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

;; The extraction function for RR3 that extracts the future output sequence
;; from the current state.

(defund round-robin3$extract (st)
  (b* ((q8-l (nth *round-robin3$q8-l* st))
       (q10-l (nth *round-robin3$q10-l* st))
       (me (nth *round-robin3$me* st))

       (a-seq (queue8-l$extract q8-l))
       (b-seq (queue10-l$extract q10-l))

       (me-select       (nth *alt-merge$select* me))
       (me-select.s     (nth *link1$s* me-select))
       (me-select.d     (nth *link1$d* me-select))
       (me-select-buf   (nth *alt-merge$select-buf* me))
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

(defthm round-robin3$extract-not-empty
  (implies (and (round-robin3$out-act inputs st data-size)
                (round-robin3$valid-st st data-size))
           (< 0 (len (round-robin3$extract st))))
  :hints (("Goal"
           :in-theory (e/d (f-and3
                            f-and
                            joint-act
                            alt-merge$act
                            alt-merge$act0
                            alt-merge$act1
                            round-robin3$me-inputs
                            round-robin3$valid-st
                            round-robin3$extract
                            round-robin3$out-act)
                           ())))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund round-robin3$inv (st)
    (b* ((q8-l (nth *round-robin3$q8-l* st))
         (q10-l (nth *round-robin3$q10-l* st))
         (br (nth *round-robin3$br* st))
         (me (nth *round-robin3$me* st))

         (a-seq (queue8-l$extract q8-l))
         (b-seq (queue10-l$extract q10-l))

         (br-select       (nth *alt-branch$select* br))
         (br-select.s     (nth *link1$s* br-select))
         (br-select.d     (nth *link1$d* br-select))
         (br-select-buf   (nth *alt-branch$select-buf* br))
         (br-select-buf.d (nth *link1$d* br-select-buf))
         (valid-br-select (if (fullp br-select.s)
                              (car br-select.d)
                            (car br-select-buf.d)))

         (me-select       (nth *alt-merge$select* me))
         (me-select.s     (nth *link1$s* me-select))
         (me-select.d     (nth *link1$d* me-select))
         (me-select-buf   (nth *alt-merge$select-buf* me))
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
   (defthm round-robin3$input-format-lemma-1
     (implies (round-robin3$input-format inputs data-size)
              (booleanp (nth 0 inputs)))
     :hints (("Goal" :in-theory (enable round-robin3$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm round-robin3$input-format-lemma-2
     (implies (round-robin3$input-format inputs data-size)
              (booleanp (nth 1 inputs)))
     :hints (("Goal" :in-theory (enable round-robin3$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm round-robin3$q8-l+q10-l-in-act-inactive
     (implies (not (nth 0 inputs))
              (and
               (not (queue8-l$in-act
                     (round-robin3$q8-l-inputs inputs st data-size)))
               (not (queue10-l$in-act
                     (round-robin3$q10-l-inputs inputs st data-size)))))
     :hints (("Goal" :in-theory (e/d (queue8-l$in-act
                                      queue10-l$in-act
                                      round-robin3$q8-l-inputs
                                      round-robin3$q10-l-inputs
                                      round-robin3$br-inputs)
                                     ())))))

  (local
   (defthm round-robin3$q8-l-in-act-inactive-1
     (b* ((br (nth *round-robin3$br* st))
          (br-select (nth *alt-branch$select* br))
          (br-select.s (nth *link1$s* br-select))
          (br-select.d (nth *link1$d* br-select))
          (br-select-buf (nth *alt-branch$select-buf* br))
          (br-select-buf.s (nth *link1$s* br-select-buf)))

       (implies (and (alt-branch$valid-st br)
                     (or (and (equal br-select.s '(t))
                              (car br-select.d))
                         (equal br-select-buf.s '(t))))
                (not (queue8-l$in-act
                      (round-robin3$q8-l-inputs inputs st data-size)))))
     :hints (("Goal" :in-theory (enable f-or3
                                        queue8-l$in-act
                                        alt-branch$valid-st
                                        alt-branch$act0
                                        round-robin3$q8-l-inputs)))))

  (local
   (defthm round-robin3$q8-l-in-act-inactive-2
     (implies (and (queue8-l$valid-st (nth *round-robin3$q8-l* st) data-size)
                   (queue8-l$ready-in- (nth *round-robin3$q8-l* st)))
              (not (queue8-l$in-act
                    (round-robin3$q8-l-inputs inputs st data-size))))
     :hints (("Goal" :in-theory (e/d (queue8-l$valid-st
                                      queue8-l$ready-in-
                                      queue8-l$in-act
                                      round-robin3$q8-l-inputs
                                      round-robin3$br-inputs)
                                     ())))))

  (local
   (defthm round-robin3$q8-l-out-act-inactive-1
     (b* ((me (nth *round-robin3$me* st))
          (me-select (nth *alt-merge$select* me))
          (me-select.s (nth *link1$s* me-select))
          (me-select.d (nth *link1$d* me-select))
          (me-select-buf (nth *alt-merge$select-buf* me))
          (me-select-buf.s (nth *link1$s* me-select-buf)))

       (implies (and (alt-merge$valid-st me)
                     (or (and (equal me-select.s '(t))
                              (car me-select.d))
                         (equal me-select-buf.s '(t))))
                (not (queue8-l$out-act
                      (round-robin3$q8-l-inputs inputs st data-size)))))
     :hints (("Goal" :in-theory (enable f-and3
                                        queue8-l$out-act
                                        alt-merge$valid-st
                                        alt-merge$act0
                                        round-robin3$q8-l-inputs)))))

  (local
   (defthm round-robin3$q8-l-out-act-inactive-2
     (implies (and (queue8-l$valid-st (nth *round-robin3$q8-l* st) data-size)
                   (not (queue8-l$ready-out (nth *round-robin3$q8-l* st))))
              (not (queue8-l$out-act
                    (round-robin3$q8-l-inputs inputs st data-size))))
     :hints (("Goal" :in-theory (e/d (queue8-l$valid-st
                                      queue8-l$ready-out
                                      queue8-l$out-act
                                      round-robin3$q8-l-inputs
                                      round-robin3$me-inputs)
                                     ())))))

  (local
   (defthm round-robin3$q10-l-in-act-inactive-1
     (b* ((br (nth *round-robin3$br* st))
          (br-select (nth *alt-branch$select* br))
          (br-select.s (nth *link1$s* br-select))
          (br-select.d (nth *link1$d* br-select))
          (br-select-buf (nth *alt-branch$select-buf* br))
          (br-select-buf.s (nth *link1$s* br-select-buf)))

       (implies (and (alt-branch$valid-st br)
                     (or (and (equal br-select.s '(t))
                              (not (car br-select.d)))
                         (equal br-select-buf.s '(t))))
                (not (queue10-l$in-act
                      (round-robin3$q10-l-inputs inputs st data-size)))))
     :hints (("Goal" :in-theory (enable f-or3
                                        queue10-l$in-act
                                        alt-branch$valid-st
                                        alt-branch$act1
                                        round-robin3$q10-l-inputs)))))

  (local
   (defthm round-robin3$q10-l-in-act-inactive-2
     (implies (and (queue10-l$valid-st (nth *round-robin3$q10-l* st) data-size)
                   (queue10-l$ready-in- (nth *round-robin3$q10-l* st)))
              (not (queue10-l$in-act
                    (round-robin3$q10-l-inputs inputs st data-size))))
     :hints (("Goal" :in-theory (e/d (queue10-l$valid-st
                                      queue10-l$ready-in-
                                      queue10-l$in-act
                                      round-robin3$q10-l-inputs
                                      round-robin3$br-inputs)
                                     ())))))

  (local
   (defthm round-robin3$q10-l-out-act-inactive-1
     (b* ((me (nth *round-robin3$me* st))
          (me-select (nth *alt-merge$select* me))
          (me-select.s (nth *link1$s* me-select))
          (me-select.d (nth *link1$d* me-select))
          (me-select-buf (nth *alt-merge$select-buf* me))
          (me-select-buf.s (nth *link1$s* me-select-buf)))

       (implies (and (alt-merge$valid-st me)
                     (or (and (equal me-select.s '(t))
                              (not (car me-select.d)))
                         (equal me-select-buf.s '(t))))
                (not (queue10-l$out-act
                      (round-robin3$q10-l-inputs inputs st data-size)))))
     :hints (("Goal" :in-theory (enable f-and3
                                        queue10-l$out-act
                                        alt-merge$valid-st
                                        alt-merge$act1
                                        round-robin3$q10-l-inputs)))))

  (local
   (defthm round-robin3$q10-l-out-act-inactive-2
     (implies (and (queue10-l$valid-st (nth *round-robin3$q10-l* st) data-size)
                   (not (queue10-l$ready-out (nth *round-robin3$q10-l* st))))
              (not (queue10-l$out-act
                    (round-robin3$q10-l-inputs inputs st data-size))))
     :hints (("Goal" :in-theory (e/d (queue10-l$valid-st
                                      queue10-l$ready-out
                                      queue10-l$out-act
                                      round-robin3$q10-l-inputs
                                      round-robin3$me-inputs)
                                     ())))))

  (local
   (defthm round-robin3$rewrite-to-q8-l-in-act
     (b* ((q8-l (nth *round-robin3$q8-l* st))
          (br (nth *round-robin3$br* st))
          (br-select (nth *alt-branch$select* br))
          (br-select.s (nth *link1$s* br-select))
          (br-select.d (nth *link1$d* br-select))
          (br-select-buf (nth *alt-branch$select-buf* br))
          (br-select-buf.s (nth *link1$s* br-select-buf)))

       (implies
        (and (queue8-l$valid-st q8-l data-size)
             (equal x (nth 0 inputs))
             (equal y (queue8-l$ready-in- q8-l))
             (equal br-select.s '(t))
             (not (car br-select.d))
             (equal br-select-buf.s '(nil)))
        (equal (joint-act x
                          y
                          (car (nthcdr (+ *round-robin3$go-branch-offset*
                                          data-size)
                                       inputs)))
               (queue8-l$in-act
                (round-robin3$q8-l-inputs inputs st data-size)))))
     :hints (("Goal" :in-theory (enable queue8-l$valid-st=>constraint
                                        queue8-l$in-act
                                        alt-branch$act0
                                        round-robin3$q8-l-inputs
                                        round-robin3$br-inputs)))))

  (local
   (defthm round-robin3$rewrite-to-q8-l-out-act
     (b* ((q8-l (nth *round-robin3$q8-l* st))
          (q10-l (nth *round-robin3$q10-l* st))
          (me (nth *round-robin3$me* st))
          (me-select (nth *alt-merge$select* me))
          (me-select.s (nth *link1$s* me-select))
          (me-select.d (nth *link1$d* me-select))
          (me-select-buf (nth *alt-merge$select-buf* me))
          (me-select-buf.s (nth *link1$s* me-select-buf)))

       (implies
        (and (queue8-l$valid-st q8-l data-size)
             (queue10-l$valid-st q10-l data-size)
             (equal x (queue8-l$ready-out q8-l))
             (equal y (nth 1 inputs))
             (equal me-select.s '(t))
             (not (car me-select.d))
             (equal me-select-buf.s '(nil)))
        (equal (joint-act x
                          y
                          (car (nthcdr (+ *round-robin3$go-merge-offset*
                                          data-size)
                                       inputs)))
               (queue8-l$out-act
                (round-robin3$q8-l-inputs inputs st data-size)))))
     :hints (("Goal" :in-theory (enable queue8-l$valid-st=>constraint
                                        queue8-l$out-act
                                        alt-merge$act0
                                        round-robin3$q8-l-inputs
                                        round-robin3$me-inputs)))))

  (local
   (defthm round-robin3$rewrite-to-q10-l-in-act
     (b* ((q10-l (nth *round-robin3$q10-l* st))
          (br (nth *round-robin3$br* st))
          (br-select (nth *alt-branch$select* br))
          (br-select.s (nth *link1$s* br-select))
          (br-select.d (nth *link1$d* br-select))
          (br-select-buf (nth *alt-branch$select-buf* br))
          (br-select-buf.s (nth *link1$s* br-select-buf)))

       (implies
        (and (queue10-l$valid-st q10-l data-size)
             (equal x (nth 0 inputs))
             (equal y (queue10-l$ready-in- q10-l))
             (equal br-select.s '(t))
             (equal (car br-select.d) t)
             (equal br-select-buf.s '(nil)))
        (equal (joint-act x
                          y
                          (car (nthcdr (+ *round-robin3$go-branch-offset*
                                          data-size)
                                       inputs)))
               (queue10-l$in-act
                (round-robin3$q10-l-inputs inputs st data-size)))))
     :hints (("Goal" :in-theory (enable queue10-l$valid-st=>constraint
                                        queue10-l$in-act
                                        alt-branch$act1
                                        round-robin3$q10-l-inputs
                                        round-robin3$br-inputs)))))

  (local
   (defthm round-robin3$rewrite-to-q10-l-out-act
     (b* ((q8-l (nth *round-robin3$q8-l* st))
          (q10-l (nth *round-robin3$q10-l* st))
          (me (nth *round-robin3$me* st))
          (me-select (nth *alt-merge$select* me))
          (me-select.s (nth *link1$s* me-select))
          (me-select.d (nth *link1$d* me-select))
          (me-select-buf (nth *alt-merge$select-buf* me))
          (me-select-buf.s (nth *link1$s* me-select-buf)))

       (implies
        (and (queue8-l$valid-st q8-l data-size)
             (queue10-l$valid-st q10-l data-size)
             (equal x (queue10-l$ready-out q10-l))
             (equal y (nth 1 inputs))
             (equal me-select.s '(t))
             (equal (car me-select.d) t)
             (equal me-select-buf.s '(nil)))
        (equal (joint-act x
                          y
                          (car (nthcdr (+ *round-robin3$go-merge-offset*
                                          data-size)
                                       inputs)))
               (queue10-l$out-act
                (round-robin3$q10-l-inputs inputs st data-size)))))
     :hints (("Goal" :in-theory (enable queue10-l$valid-st=>constraint
                                        queue10-l$out-act
                                        alt-merge$act1
                                        round-robin3$q10-l-inputs
                                        round-robin3$me-inputs)))))

  (defthm round-robin3$inv-preserved
    (implies (and (round-robin3$input-format inputs data-size)
                  (round-robin3$valid-st st data-size)
                  (round-robin3$inv st))
             (round-robin3$inv (round-robin3$step inputs st data-size)))
    :hints (("Goal"
             :use (round-robin3$input-format=>q8-l$input-format
                   round-robin3$input-format=>q10-l$input-format)
             :in-theory (e/d (f-sr
                              queue8-l$valid-st=>constraint
                              queue8-l$extracted-step
                              queue10-l$extracted-step
                              round-robin3$valid-st
                              round-robin3$inv
                              round-robin3$step
                              round-robin3$br-inputs
                              round-robin3$me-inputs
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
                             (round-robin3$input-format=>q8-l$input-format
                              round-robin3$input-format=>q10-l$input-format)))))
  )

;; The extracted next-state function for RR3.  Note that this function avoids
;; exploring the internal computation of RR3.

(defund round-robin3$extracted-step (inputs st data-size)
  (b* ((data (round-robin3$data-in inputs data-size))
       (extracted-st (round-robin3$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (round-robin3$out-act inputs st data-size) t)
      (cond
       ((equal (round-robin3$in-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (round-robin3$in-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (in-theory (disable acl2::simplify-products-gather-exponents-<)))

  (local
   (defthm round-robin3$q8-l-data-in-rewrite
     (equal (queue8-l$data-in
             (round-robin3$q8-l-inputs inputs st data-size)
             data-size)
            (round-robin3$data-in inputs data-size))
     :hints (("Goal"
              :in-theory (enable queue8-l$data-in
                                 round-robin3$q8-l-inputs)))))

  (local
   (defthm round-robin3$q10-l-data-in-rewrite
     (equal (queue10-l$data-in
             (round-robin3$q10-l-inputs inputs st data-size)
             data-size)
            (round-robin3$data-in inputs data-size))
     :hints (("Goal"
              :in-theory (enable queue10-l$data-in
                                 round-robin3$q10-l-inputs)))))

  (local
   (defthm cons-intertwine
     (implies (consp l1)
              (equal (cons (car l1)
                           (intertwine l2 (cdr l1)))
                     (intertwine l1 l2)))))

  (local
   (defthmd take-intertwine-1
     (implies (and (equal (len l1) (len l2))
                   (natp m)
                   (<= m (len l1))
                   (equal m (1+ n)))
              (equal (take (+ m n) (intertwine l1 l2))
                     (intertwine (take m l1) (take n l2))))))

  (local
   (defthmd take-intertwine-2
     (implies (and (equal (len l1) (1+ (len l2)))
                   (natp m)
                   (<= m (len l1))
                   (equal m n))
              (equal (take (+ m n) (intertwine l1 l2))
                     (intertwine (take m l1) (take n l2))))))

  (local
   (defthm take-intertwine-1-instance
     (implies (and (equal (len l1) (len l2))
                   (true-listp l1)
                   (equal m (+ -1 (len l1) (len l2)))
                   (equal n (1- (len l2))))
              (equal (take m (intertwine l1 l2))
                     (intertwine l1 (take n l2))))
     :hints (("Goal"
              :use (:instance take-intertwine-1
                              (m (- m n)))))))

  (local
   (defthm take-intertwine-2-instance
     (implies (and (equal (len l1) (1+ (len l2)))
                   (true-listp l2)
                   (equal m (1- (len l1)))
                   (equal n (+ -1 (len l1) (len l2))))
              (equal (take n (intertwine l1 l2))
                     (intertwine (take m l1) l2)))
     :hints (("Goal"
              :use (:instance take-intertwine-2
                              (n (- n m)))))))

  (defthm round-robin3$extracted-step-correct
    (b* ((next-st (round-robin3$step inputs st data-size)))
      (implies (and (round-robin3$input-format inputs data-size)
                    (round-robin3$valid-st st data-size)
                    (round-robin3$inv st))
               (equal (round-robin3$extract next-st)
                      (round-robin3$extracted-step inputs st data-size))))
    :hints (("Goal"
             :use (round-robin3$input-format=>q8-l$input-format
                   round-robin3$input-format=>q10-l$input-format)
             :in-theory (e/d (f-sr
                              queue8-l$valid-st=>constraint
                              queue8-l$extracted-step
                              queue10-l$extracted-step
                              round-robin3$extracted-step
                              round-robin3$valid-st
                              round-robin3$inv
                              round-robin3$step
                              round-robin3$in-act
                              round-robin3$out-act
                              round-robin3$extract
                              round-robin3$br-inputs
                              round-robin3$me-inputs
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
                             (round-robin3$input-format=>q8-l$input-format
                              round-robin3$input-format=>q10-l$input-format
                              nfix)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that round-robin3$valid-st is an invariant.

(defthm round-robin3$valid-st-preserved
  (implies (and (round-robin3$input-format inputs data-size)
                (round-robin3$valid-st st data-size))
           (round-robin3$valid-st
            (round-robin3$step inputs st data-size)
            data-size))
  :hints (("Goal"
           :in-theory (e/d (round-robin3$valid-st
                            round-robin3$step)
                           ()))))

(encapsulate
  ()

  (local
   (defun nthcdr-intertwine-1-induct (m n l1 l2)
     (if (zp n)
         (list m l1 l2)
       (nthcdr-intertwine-1-induct (- m 2) (1- n) (cdr l1) (cdr l2)))))

  (local
   (defthm nthcdr-intertwine-1
     (implies (and (equal (len l1) (len l2))
                   (equal n (1- (len l2)))
                   (equal m (nfix (1+ (* 2 n)))))
              (equal (nthcdr m (intertwine l1 l2))
                     (nthcdr n l2)))
     :hints (("Goal"
              :induct (nthcdr-intertwine-1-induct m n l1 l2)
              :in-theory (enable len-0-is-atom)))))

  (local
   (defthm nthcdr-intertwine-2
     (implies (and (equal (len l1) (1+ (len l2)))
                   (equal n (len l2))
                   (equal m (* 2 n)))
              (equal (nthcdr m (intertwine l1 l2))
                     (nthcdr n l1)))))

  (defthm round-robin3$extract-lemma
    (implies (and (round-robin3$input-format inputs data-size)
                  (round-robin3$valid-st st data-size)
                  (round-robin3$inv st)
                  (round-robin3$out-act inputs st data-size))
             (equal (list (round-robin3$data-out st))
                    (nthcdr (1- (len (round-robin3$extract st)))
                            (round-robin3$extract st))))
    :hints (("Goal"
             :do-not-induct t
             :use round-robin3$valid-st=>constraint
             :in-theory (e/d (f-and3
                              queue8-l$extract-lemma-2
                              queue10-l$extract-lemma-2
                              round-robin3$valid-st
                              round-robin3$inv
                              round-robin3$extract
                              round-robin3$out-act
                              round-robin3$data-out
                              round-robin3$me-inputs
                              alt-merge$valid-st
                              alt-merge$act
                              alt-merge$act0
                              alt-merge$act1)
                             (round-robin3$valid-st=>constraint)))))
  )

;; Extract the accepted input sequence

(seq-gen round-robin3 in in-act 0
         (round-robin3$data-in inputs data-size))

;; Extract the valid output sequence

(seq-gen round-robin3 out out-act 1
         (round-robin3$data-out st)
         :netlist-data (nthcdr 2 outputs))

;; The multi-step input-output relationship

(in-out-stream-lemma round-robin3 :inv t)

