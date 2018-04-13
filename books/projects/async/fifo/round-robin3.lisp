;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; April 2018

(in-package "ADE")

(include-book "alt-branch")
(include-book "alt-merge")
(include-book "queue8-as-link")
(include-book "queue10-as-link")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of RR3
;;; 2. Specify the Final State of RR3 After An N-Step Execution
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of RR3
;;
;; Construct a DE module generator for a round-robin circuit, RR3, using the
;; link-joint model.  Prove the value and state lemmas for this module
;; generator.

(defconst *round-robin3$go-num* (+ *queue8$go-num*
                                   *queue10$go-num*
                                   *alt-branch$go-num*
                                   *alt-merge$go-num*))
(defconst *round-robin3$st-len* 4)

(defconst *round-robin3$go-branch-offset*
  (+ 2 *queue8$go-num* *queue10$go-num*))

(defconst *round-robin3$go-merge-offset*
  (+ 2 *queue8$go-num* *queue10$go-num* *alt-branch$go-num*))

(defun round-robin3$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun round-robin3$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (round-robin3$data-ins-len data-width)
     *round-robin3$go-num*))

;; DE module generator of RR3.  The ALT-BRANCH joint in RR3 accepts input data
;; and places them alternately into two queues.  The ALT-MERGE joint takes data
;; alternately from two queues and delivers them as outputs.

(module-generator
 round-robin3* (data-width)
 (si 'round-robin3 data-width)
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 data-width)
                                    (sis 'go 0 *round-robin3$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-width))
 '(q8 q10 br me)
 (list
  ;; LINKS
  ;; 8-link queue Q8
  (list 'q8
        (list* 'q8-ready-in- 'q8-ready-out
               (sis 'q8-data-out 0 data-width))
        (si 'queue8 data-width)
        (list* 'br-act0 'me-act0
               (append (sis 'data 0 data-width)
                       (sis 'go 0 *queue8$go-num*))))

  ;; 10-link queue Q10
  (list 'q10
        (list* 'q10-ready-in- 'q10-ready-out
               (sis 'q10-data-out 0 data-width))
        (si 'queue10 data-width)
        (list* 'br-act1 'me-act1
               (append (sis 'data 0 data-width)
                       (sis 'go
                            *queue8$go-num*
                            *queue10$go-num*))))

  ;; JOINTS
  ;; Alt-Branch
  (list 'br
        (list* 'in-act 'br-act0 'br-act1
               (sis 'data 0 data-width))
        (si 'alt-branch data-width)
        (list* 'full-in 'q8-ready-in- 'q10-ready-in-
               (append (sis 'data-in 0 data-width)
                       (sis 'go
                            (+ *queue8$go-num*
                               *queue10$go-num*)
                            *alt-branch$go-num*))))

  ;; Alt-Merge
  (list 'me
        (list* 'out-act 'me-act0 'me-act1
               (sis 'data-out 0 data-width))
        (si 'alt-merge data-width)
        (list* 'q8-ready-out 'q10-ready-out 'empty-out-
               (append (sis 'q8-data-out 0 data-width)
                       (sis 'q10-data-out 0 data-width)
                       (sis 'go
                            (+ *queue8$go-num*
                               *queue10$go-num*
                               *alt-branch$go-num*)
                            *alt-merge$go-num*)))))

 :guard (natp data-width))

(make-event
 `(progn
    ,@(state-accessors-gen 'round-robin3 '(q8 q10 br me) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of RR3.

(defun round-robin3$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (round-robin3* data-width)
        (union$ (queue8$netlist data-width)
                (queue10$netlist data-width)
                (alt-branch$netlist data-width)
                (alt-merge$netlist data-width)
                :test 'equal)))

;; Recognizer for RR3

(defund round-robin3& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (and (equal (assoc (si 'round-robin3 data-width) netlist)
              (round-robin3* data-width))
       (b* ((netlist (delete-to-eq (si 'round-robin3 data-width) netlist)))
         (and (queue8& netlist data-width)
              (queue10& netlist data-width)
              (alt-branch& netlist data-width)
              (alt-merge& netlist data-width)))))

;; Sanity check

(local
 (defthmd check-round-robin3$netlist-64
   (and (net-syntax-okp (round-robin3$netlist 64))
        (net-arity-okp (round-robin3$netlist 64))
        (round-robin3& (round-robin3$netlist 64) 64))))

;; Constraints on the state of RR3

(defund round-robin3$st-format (st data-width)
  (b* ((q8 (get-field *round-robin3$q8* st))
       (q10 (get-field *round-robin3$q10* st)))
    (and (< 0 data-width)
         (queue8$st-format q8 data-width)
         (queue10$st-format q10 data-width))))

(defthm round-robin3$st-format=>posp-data-width
  (implies (round-robin3$st-format st data-width)
           (posp data-width))
  :hints (("Goal" :in-theory (enable round-robin3$st-format)))
  :rule-classes :forward-chaining)

(defund round-robin3$valid-st (st data-width)
  (b* ((q8 (get-field *round-robin3$q8* st))
       (q10 (get-field *round-robin3$q10* st))
       (br (get-field *round-robin3$br* st))
       (me (get-field *round-robin3$me* st)))
    (and (queue8$valid-st q8 data-width)
         (queue10$valid-st q10 data-width)

         (alt-branch$valid-st br)
         (alt-merge$valid-st me))))

(defthmd round-robin3$valid-st=>natp-data-width
  (implies (round-robin3$valid-st st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable round-robin3$valid-st
                                     queue8$valid-st=>natp-data-width)))
  :rule-classes :forward-chaining)

;; Extract the input and output signals from RR3

(progn
  ;; Extract the input data

  (defun round-robin3$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 2 inputs)))

  (defthm len-round-robin3$data-in
    (equal (len (round-robin3$data-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable round-robin3$data-in))

  ;; Extract the inputs for the alt-branch joint

  (defund round-robin3$br-inputs (inputs st data-width)
    (b* ((full-in (nth 0 inputs))
         (data-in (round-robin3$data-in inputs data-width))
         (go-signals (nthcdr (round-robin3$data-ins-len data-width) inputs))

         (br-go-signals (take *alt-branch$go-num*
                              (nthcdr (+ *queue8$go-num*
                                         *queue10$go-num*)
                                      go-signals)))

         (q8 (get-field *round-robin3$q8* st))
         (q10 (get-field *round-robin3$q10* st))

         (q8-ready-in- (queue8$ready-in- q8))
         (q10-ready-in- (queue10$ready-in- q10)))

      (list* full-in q8-ready-in- q10-ready-in-
             (append data-in br-go-signals))))

  ;; Extract the inputs for the alt-merge joint

  (defund round-robin3$me-inputs (inputs st data-width)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (round-robin3$data-ins-len data-width) inputs))

         (me-go-signals (nthcdr (+ *queue8$go-num*
                                   *queue10$go-num*
                                   *alt-branch$go-num*)
                                go-signals))

         (q8 (get-field *round-robin3$q8* st))
         (q10 (get-field *round-robin3$q10* st))

         (q8-ready-out (queue8$ready-out q8))
         (q8-data-out (queue8$data-out q8))
         (q10-ready-out (queue10$ready-out q10))
         (q10-data-out (queue10$data-out q10)))

      (list* q8-ready-out q10-ready-out empty-out-
             (append q8-data-out q10-data-out me-go-signals))))

  ;; Extract the inputs for the Q8' link

  (defund round-robin3$q8-inputs (inputs st data-width)
    (b* ((data-in (round-robin3$data-in inputs data-width))
         (go-signals (nthcdr (round-robin3$data-ins-len data-width) inputs))

         (q8-go-signals (take *queue8$go-num* go-signals))

         (br (get-field *round-robin3$br* st))
         (me (get-field *round-robin3$me* st))

         (br-inputs (round-robin3$br-inputs inputs st data-width))
         (me-inputs (round-robin3$me-inputs inputs st data-width))

         (br-act0 (alt-branch$act0 br-inputs br data-width))
         (me-act0 (alt-merge$act0 me-inputs me data-width)))

      (list* br-act0 me-act0
             (append (v-threefix data-in)
                     q8-go-signals))))

  ;; Extract the inputs for the Q10' link

  (defund round-robin3$q10-inputs (inputs st data-width)
    (b* ((data-in (round-robin3$data-in inputs data-width))
         (go-signals (nthcdr (round-robin3$data-ins-len data-width) inputs))

         (q10-go-signals (take *queue10$go-num*
                               (nthcdr *queue8$go-num*
                                       go-signals)))

         (br (get-field *round-robin3$br* st))
         (me (get-field *round-robin3$me* st))

         (br-inputs (round-robin3$br-inputs inputs st data-width))
         (me-inputs (round-robin3$me-inputs inputs st data-width))

         (br-act1 (alt-branch$act1 br-inputs br data-width))
         (me-act1 (alt-merge$act1 me-inputs me data-width)))

      (list* br-act1 me-act1
             (append (v-threefix data-in)
                     q10-go-signals))))

  ;; Extract the "in-act" signal

  (defund round-robin3$in-act (inputs st data-width)
    (b* ((br-inputs (round-robin3$br-inputs inputs st data-width))
         (br (get-field *round-robin3$br* st)))
      (alt-branch$act br-inputs br data-width)))

  ;; Extract the "out-act" signal

  (defund round-robin3$out-act (inputs st data-width)
    (b* ((me-inputs (round-robin3$me-inputs inputs st data-width))
         (me (get-field *round-robin3$me* st)))
      (alt-merge$act me-inputs me data-width)))

  ;; Extract the output data

  (defund round-robin3$data-out (st)
    (b* ((q8 (get-field *round-robin3$q8* st))
         (q10 (get-field *round-robin3$q10* st))
         (me (get-field *round-robin3$me* st))

         (q8-data-out (queue8$data-out q8))
         (q10-data-out (queue10$data-out q10))

         (me-select (get-field *alt-merge$select* me)))
      (fv-if (car me-select)
             q10-data-out
             q8-data-out)))

  (defthm len-round-robin3$data-out-1
    (implies (round-robin3$st-format st data-width)
             (equal (len (round-robin3$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable round-robin3$st-format
                                       round-robin3$data-out))))

  (defthm len-round-robin3$data-out-2
    (implies (round-robin3$valid-st st data-width)
             (equal (len (round-robin3$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable round-robin3$valid-st
                                       round-robin3$data-out))))

  (defthm bvp-round-robin3$data-out
    (implies (and (round-robin3$valid-st st data-width)
                  (round-robin3$out-act inputs st data-width))
             (bvp (round-robin3$data-out st)))
    :hints (("Goal" :in-theory (enable f-and3
                                       f-and
                                       joint-act
                                       round-robin3$valid-st
                                       round-robin3$out-act
                                       round-robin3$data-out
                                       round-robin3$me-inputs
                                       queue8$valid-st=>natp-data-width
                                       alt-merge$valid-st
                                       alt-merge$act
                                       alt-merge$act0
                                       alt-merge$act1))))
  )

(not-primp-lemma round-robin3) ;; Prove that RR3 is not a DE primitive.

;; The value lemma for RR3

(defthmd round-robin3$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (round-robin3& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *round-robin3$go-num*)
                  (round-robin3$st-format st data-width))
             (equal (se (si 'round-robin3 data-width) inputs st netlist)
                    (list* (round-robin3$in-act inputs st data-width)
                           (round-robin3$out-act inputs st data-width)
                           (round-robin3$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :expand (se (si 'round-robin3 data-width)
                       (list* full-in empty-out-
                              (append data-in go-signals))
                       st
                       netlist)
           :in-theory (e/d (de-rules
                            not-primp-round-robin3
                            round-robin3&
                            round-robin3*$destructure
                            round-robin3$data-in
                            queue8$value
                            queue10$value
                            alt-branch$value
                            alt-merge$value
                            round-robin3$st-format
                            round-robin3$in-act
                            round-robin3$out-act
                            round-robin3$data-out
                            round-robin3$br-inputs
                            round-robin3$me-inputs)
                           ((round-robin3*)
                            de-module-disabled-rules)))))

;; This function specifies the next state of RR3.

(defun round-robin3$step (inputs st data-width)
  (b* ((q8 (get-field *round-robin3$q8* st))
       (q10 (get-field *round-robin3$q10* st))
       (br (get-field *round-robin3$br* st))
       (me (get-field *round-robin3$me* st))

       (q8-inputs (round-robin3$q8-inputs inputs st data-width))
       (q10-inputs (round-robin3$q10-inputs inputs st data-width))
       (br-inputs (round-robin3$br-inputs inputs st data-width))
       (me-inputs (round-robin3$me-inputs inputs st data-width)))

    (list
     ;; Q8'
     (queue8$step q8-inputs q8 data-width)
     ;; Q10'
     (queue10$step q10-inputs q10 data-width)
     ;; Joint alt-branch
     (alt-branch$step br-inputs br data-width)
     ;; Joint alt-merge
     (alt-merge$step me-inputs me data-width))))

(defthm len-of-round-robin3$step
  (equal (len (round-robin3$step inputs st data-width))
         *round-robin3$st-len*))

;; The state lemma for RR3

(defthmd round-robin3$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (round-robin3& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *round-robin3$go-num*)
                  (round-robin3$st-format st data-width))
             (equal (de (si 'round-robin3 data-width) inputs st netlist)
                    (round-robin3$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :expand (de (si 'round-robin3 data-width)
                       (list* full-in empty-out-
                              (append data-in go-signals))
                       st
                       netlist)
           :in-theory (e/d (de-rules
                            not-primp-round-robin3
                            round-robin3&
                            round-robin3*$destructure
                            round-robin3$st-format
                            round-robin3$data-in
                            round-robin3$q8-inputs
                            round-robin3$q10-inputs
                            round-robin3$br-inputs
                            round-robin3$me-inputs
                            queue8$value queue8$state
                            queue10$value queue10$state
                            alt-branch$value alt-branch$state
                            alt-merge$value alt-merge$state)
                           ((round-robin3*)
                            de-module-disabled-rules)))))

(in-theory (disable round-robin3$step))

;; ======================================================================

;; 2. Specify the Final State of RR3 After An N-Step Execution

;; RR3 simulator

(progn
  (defun round-robin3$map-to-links (st)
    (b* ((q8 (get-field *round-robin3$q8* st))
         (q10 (get-field *round-robin3$q10* st))
         (br (get-field *round-robin3$br* st))
         (me (get-field *round-robin3$me* st)))
      (append (list (cons 'alt-branch (alt-branch$map-to-links br)))
              (list (cons 'Q8 (queue8$map-to-links q8)))
              (list (cons 'Q10 (queue10$map-to-links q10)))
              (list (cons 'alt-merge (alt-merge$map-to-links me))))))

  (defun round-robin3$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (round-robin3$map-to-links (car x))
            (round-robin3$map-to-links-list (cdr x)))))

  (defund round-robin3$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (round-robin3$ins-len data-width))
         ((mv inputs-lst state)
          (signal-vals-gen num-signals n state nil))
         ;;(- (cw "~x0~%" inputs-lst))
         (full '(t))
         (empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (q4-0 (list empty invalid-data
                     empty invalid-data
                     empty invalid-data
                     empty invalid-data))
         (q4-1 (list empty invalid-data
                     empty invalid-data
                     empty invalid-data
                     empty invalid-data))
         (q8 (list q4-0 q4-1))
         (q5-0 (list empty invalid-data
                     empty invalid-data
                     empty invalid-data
                     empty invalid-data
                     empty invalid-data))
         (q5-1 (list empty invalid-data
                     empty invalid-data
                     empty invalid-data
                     empty invalid-data
                     empty invalid-data))
         (q10 (list q5-0 q5-1))
         (br (list full '(nil)
                   empty '(x)))
         (me (list full '(nil)
                   empty '(x)))
         (st (list q8 q10 br me)))
      (mv (pretty-list
           (remove-dup-neighbors
            (round-robin3$map-to-links-list
             (de-sim-list (si 'round-robin3 data-width)
                          inputs-lst
                          st
                          (round-robin3$netlist data-width))))
           0)
          state)))
  )

;; Conditions on the inputs

(defund round-robin3$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (round-robin3$data-in inputs data-width))
       (go-signals (nthcdr (round-robin3$data-ins-len data-width) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *round-robin3$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(defthmd len-of-round-robin3$inputs
  (implies (round-robin3$input-format inputs data-width)
           (equal (len inputs) (round-robin3$ins-len data-width)))
  :hints (("Goal" :in-theory (enable round-robin3$input-format))))

(local
 (defthm round-robin3$input-format=>q8$input-format
   (implies (and (round-robin3$input-format inputs data-width)
                 (round-robin3$valid-st st data-width))
            (queue8$input-format
             (round-robin3$q8-inputs inputs st data-width)
             (nth *round-robin3$q8* st)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             f-and3
                             queue8$valid-st=>natp-data-width
                             queue8$input-format
                             queue8$in-act
                             queue8$out-act
                             queue8$data-in
                             alt-branch$valid-st
                             alt-branch$act
                             alt-branch$act0
                             alt-merge$valid-st
                             alt-merge$act
                             alt-merge$act0
                             round-robin3$input-format
                             round-robin3$valid-st
                             round-robin3$q8-inputs
                             round-robin3$br-inputs
                             round-robin3$me-inputs)
                            (nfix
                             nthcdr
                             b-not
                             take-of-too-many))))))

(local
 (defthm round-robin3$input-format=>q10$input-format
   (implies (and (round-robin3$input-format inputs data-width)
                 (round-robin3$valid-st st data-width))
            (queue10$input-format
             (round-robin3$q10-inputs inputs st data-width)
             (nth *round-robin3$q10* st)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             f-and3
                             queue10$valid-st=>natp-data-width
                             queue10$input-format
                             queue10$in-act
                             queue10$out-act
                             queue10$data-in
                             alt-branch$valid-st
                             alt-branch$act
                             alt-branch$act1
                             alt-merge$valid-st
                             alt-merge$act
                             alt-merge$act1
                             round-robin3$input-format
                             round-robin3$valid-st
                             round-robin3$q10-inputs
                             round-robin3$br-inputs
                             round-robin3$me-inputs)
                            (nfix
                             nthcdr
                             b-not
                             take-of-too-many))))))

(local
 (defthm round-robin3$input-format=>br$input-format
   (implies (and (round-robin3$input-format inputs data-width)
                 (round-robin3$valid-st st data-width))
            (alt-branch$input-format
             (round-robin3$br-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (queue8$valid-st=>natp-data-width
                             alt-branch$input-format
                             alt-branch$data-in
                             round-robin3$input-format
                             round-robin3$valid-st
                             round-robin3$br-inputs)
                            (nfix
                             nthcdr
                             take-of-too-many))))))

(local
 (defthm round-robin3$input-format=>me$input-format
   (implies (and (round-robin3$input-format inputs data-width)
                 (round-robin3$valid-st st data-width))
            (alt-merge$input-format
             (round-robin3$me-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :use len-of-round-robin3$inputs
            :in-theory (e/d (queue8$valid-st=>natp-data-width
                             alt-merge$input-format
                             alt-merge$data-in0
                             alt-merge$data-in1
                             round-robin3$input-format
                             round-robin3$valid-st
                             round-robin3$me-inputs)
                            (nthcdr
                             take-of-too-many))))))

(simulate-lemma round-robin3)

;; ======================================================================

;; 3. Single-Step-Update Property

(defun interleave (l1 l2)
  (declare (xargs :guard t))
  (cond ((atom l1) l2)
        ((atom l2) l1)
        (t (append (list (car l1) (car l2))
                   (interleave (cdr l1) (cdr l2))))))

(defthm consp-interleave
  (implies (or (consp l1) (consp l2)
               (< 0 (len l1)) (< 0 (len l2)))
           (consp (interleave l1 l2)))
  :rule-classes :type-prescription)

(defthm true-listp-interleave
  (implies (and (true-listp l1)
                (true-listp l2))
           (true-listp (interleave l1 l2)))
  :rule-classes :type-prescription)

(defthm len-interleave
  (equal (len (interleave l1 l2))
         (+ (len l1) (len l2))))

(defthm len-of-cdr-interleave
  (implies (or (< 0 (len l1)) (< 0 (len l2)))
           (equal (len (cdr (interleave l1 l2)))
                  (+ -1 (len l1) (len l2)))))

(defthm interleave-append-1
  (implies (and (or (equal (len x1) (len x2))
                    (equal (len x1) (1+ (len x2))))
                (consp y))
           (equal (interleave (append x1 y) x2)
                  (append (interleave x1 x2) y))))

(defthm interleave-append-2
  (implies (and (<= (len x1) (1+ (len x2)))
                (consp y))
           (equal (interleave x1 (append x2 y))
                  (append (interleave x1 x2) y))))

(defthm interleave-append-append
  (implies (equal (len x1) (len x2))
           (equal (interleave (append x1 y1) (append x2 y2))
                  (append (interleave x1 x2) (interleave y1 y2)))))

;; The extraction function for RR3 that extracts the future output sequence
;; from the current state.

(defund round-robin3$extract (st)
  (b* ((q8 (get-field *round-robin3$q8* st))
       (q10 (get-field *round-robin3$q10* st))
       (me (get-field *round-robin3$me* st))

       (a-seq (queue8$extract q8))
       (b-seq (queue10$extract q10))

       (me-lselect    (get-field *alt-merge$lselect* me))
       (me-select     (get-field *alt-merge$select* me))
       (me-select-buf (get-field *alt-merge$select-buf* me))
       (valid-me-select (if (fullp me-lselect)
                            (car me-select)
                          (car me-select-buf))))

    (cond ((< (len a-seq) (len b-seq))
           (interleave b-seq a-seq))
          ((< (len b-seq) (len a-seq))
           (interleave a-seq b-seq))
          (valid-me-select (interleave a-seq b-seq))
          (t (interleave b-seq a-seq)))))

(defthm round-robin3$extract-not-empty
  (implies (and (round-robin3$out-act inputs st data-width)
                (round-robin3$valid-st st data-width))
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
                           (nfix))))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund round-robin3$inv (st)
    (b* ((q8 (get-field *round-robin3$q8* st))
         (q10 (get-field *round-robin3$q10* st))
         (br (get-field *round-robin3$br* st))
         (me (get-field *round-robin3$me* st))

         (a-seq (queue8$extract q8))
         (b-seq (queue10$extract q10))

         (br-lselect    (get-field *alt-branch$lselect* br))
         (br-select     (get-field *alt-branch$select* br))
         (br-select-buf (get-field *alt-branch$select-buf* br))
         (valid-br-select (if (fullp br-lselect)
                              (car br-select)
                            (car br-select-buf)))

         (me-lselect    (get-field *alt-merge$lselect* me))
         (me-select     (get-field *alt-merge$select* me))
         (me-select-buf (get-field *alt-merge$select-buf* me))
         (valid-me-select (if (fullp me-lselect)
                              (car me-select)
                            (car me-select-buf))))

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
   (defthm round-robin3$q8+q10-in-act-nil
     (implies (not (nth 0 inputs))
              (and
               (not (queue8$in-act
                     (round-robin3$q8-inputs inputs st data-width)))
               (not (queue10$in-act
                     (round-robin3$q10-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (e/d (get-field
                                      queue8$in-act
                                      queue10$in-act
                                      alt-branch$act0
                                      alt-branch$act1
                                      round-robin3$q8-inputs
                                      round-robin3$q10-inputs
                                      round-robin3$br-inputs)
                                     ())))))

  (local
   (defthm round-robin3$q8-in-act-nil-1
     (b* ((br (nth *round-robin3$br* st))

          (br-lselect (nth *alt-branch$lselect* br))
          (br-select (nth *alt-branch$select* br))
          (br-lselect-buf (nth *alt-branch$lselect-buf* br)))

       (implies (and (alt-branch$valid-st br)
                     (or (and (equal br-lselect '(t))
                              (car br-select))
                         (equal br-lselect-buf '(t))))
                (not (queue8$in-act
                      (round-robin3$q8-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        f-or3
                                        queue8$in-act
                                        alt-branch$valid-st
                                        alt-branch$act0
                                        round-robin3$q8-inputs)))))

  (local
   (defthm round-robin3$q8-in-act-nil-2
     (implies (and (queue8$valid-st (nth *round-robin3$q8* st) data-width)
                   (queue8$ready-in- (nth *round-robin3$q8* st)))
              (not (queue8$in-act
                    (round-robin3$q8-inputs inputs st data-width))))
     :hints (("Goal" :in-theory (e/d (get-field
                                      f-or3
                                      queue8$valid-st
                                      queue8$ready-in-
                                      queue8$in-act
                                      alt-branch$act0
                                      round-robin3$q8-inputs
                                      round-robin3$br-inputs)
                                     ())))))

  (local
   (defthm round-robin3$q8-out-act-nil-1
     (b* ((me (nth *round-robin3$me* st))

          (me-lselect (nth *alt-merge$lselect* me))
          (me-select (nth *alt-merge$select* me))
          (me-lselect-buf (nth *alt-merge$lselect-buf* me)))

       (implies (and (alt-merge$valid-st me)
                     (or (and (equal me-lselect '(t))
                              (car me-select))
                         (equal me-lselect-buf '(t))))
                (not (queue8$out-act
                      (round-robin3$q8-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        f-and3
                                        queue8$out-act
                                        alt-merge$valid-st
                                        alt-merge$act0
                                        round-robin3$q8-inputs)))))

  (local
   (defthm round-robin3$q8-out-act-nil-2
     (implies (and (queue8$valid-st (nth *round-robin3$q8* st) data-width)
                   (not (queue8$ready-out (nth *round-robin3$q8* st))))
              (not (queue8$out-act
                    (round-robin3$q8-inputs inputs st data-width))))
     :hints (("Goal" :in-theory (e/d (get-field
                                      f-and3
                                      queue8$valid-st
                                      queue8$ready-out
                                      queue8$out-act
                                      alt-merge$act0
                                      round-robin3$q8-inputs
                                      round-robin3$me-inputs)
                                     ())))))

  (local
   (defthm round-robin3$q10-in-act-nil-1
     (b* ((br (nth *round-robin3$br* st))

          (br-lselect (nth *alt-branch$lselect* br))
          (br-select (nth *alt-branch$select* br))
          (br-lselect-buf (nth *alt-branch$lselect-buf* br)))

       (implies (and (alt-branch$valid-st br)
                     (or (and (equal br-lselect '(t))
                              (not (car br-select)))
                         (equal br-lselect-buf '(t))))
                (not (queue10$in-act
                      (round-robin3$q10-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        f-or3
                                        queue10$in-act
                                        alt-branch$valid-st
                                        alt-branch$act1
                                        round-robin3$q10-inputs)))))

  (local
   (defthm round-robin3$q10-in-act-nil-2
     (implies (and (queue10$valid-st (nth *round-robin3$q10* st) data-width)
                   (queue10$ready-in- (nth *round-robin3$q10* st)))
              (not (queue10$in-act
                    (round-robin3$q10-inputs inputs st data-width))))
     :hints (("Goal" :in-theory (e/d (get-field
                                      f-or3
                                      queue10$valid-st
                                      queue10$ready-in-
                                      queue10$in-act
                                      alt-branch$act1
                                      round-robin3$q10-inputs
                                      round-robin3$br-inputs)
                                     ())))))

  (local
   (defthm round-robin3$q10-out-act-nil-1
     (b* ((me (nth *round-robin3$me* st))

          (me-lselect (nth *alt-merge$lselect* me))
          (me-select (nth *alt-merge$select* me))
          (me-lselect-buf (nth *alt-merge$lselect-buf* me)))

       (implies (and (alt-merge$valid-st me)
                     (or (and (equal me-lselect '(t))
                              (not (car me-select)))
                         (equal me-lselect-buf '(t))))
                (not (queue10$out-act
                      (round-robin3$q10-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        f-and3
                                        queue10$out-act
                                        alt-merge$valid-st
                                        alt-merge$act1
                                        round-robin3$q10-inputs)))))

  (local
   (defthm round-robin3$q10-out-act-nil-2
     (implies (and (queue10$valid-st (nth *round-robin3$q10* st) data-width)
                   (not (queue10$ready-out (nth *round-robin3$q10* st))))
              (not (queue10$out-act
                    (round-robin3$q10-inputs inputs st data-width))))
     :hints (("Goal" :in-theory (e/d (get-field
                                      f-and3
                                      queue10$valid-st
                                      queue10$ready-out
                                      queue10$out-act
                                      alt-merge$act1
                                      round-robin3$q10-inputs
                                      round-robin3$me-inputs)
                                     ())))))

  (local
   (defthm booleanp-round-robin3$q8-in-act
     (b* ((q8 (nth *round-robin3$q8* st))
          (br (nth *round-robin3$br* st))

          (br-lselect (nth *alt-branch$lselect* br))
          (br-select (nth *alt-branch$select* br))
          (br-lselect-buf (nth *alt-branch$lselect-buf* br)))

       (implies (and (booleanp (nth 0 inputs))
                     (queue8$valid-st q8 data-width)
                     (equal br-lselect '(t))
                     (not (car br-select))
                     (equal br-lselect-buf '(nil)))
                (booleanp (queue8$in-act
                           (round-robin3$q8-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue8$in-act
                                        alt-branch$act0
                                        round-robin3$q8-inputs
                                        round-robin3$br-inputs)))
     :rule-classes :type-prescription))

  (local
   (defthm round-robin3$rewrite-to-q8-in-act-1
     (b* ((q8 (nth *round-robin3$q8* st))
          (br (nth *round-robin3$br* st))

          (br-lselect (nth *alt-branch$lselect* br))
          (br-select (nth *alt-branch$select* br))
          (br-lselect-buf (nth *alt-branch$lselect-buf* br)))

       (implies
        (and (booleanp x)
             (equal x (nth 0 inputs))
             (queue8$valid-st q8 data-width)
             (equal br-lselect '(t))
             (not (car br-select))
             (equal br-lselect-buf '(nil)))
        (equal (joint-act x
                          (queue8$ready-in- q8)
                          (car (nthcdr (+ *round-robin3$go-branch-offset*
                                          data-width)
                                       inputs)))
               (queue8$in-act
                (round-robin3$q8-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue8$valid-st=>natp-data-width
                                        queue8$in-act
                                        alt-branch$act0
                                        round-robin3$q8-inputs
                                        round-robin3$br-inputs)))))

  (local
   (defthm round-robin3$rewrite-to-q8-in-act-2
     (b* ((q8 (nth *round-robin3$q8* st))
          (br (nth *round-robin3$br* st))

          (br-lselect (nth *alt-branch$lselect* br))
          (br-select (nth *alt-branch$select* br))
          (br-lselect-buf (nth *alt-branch$lselect-buf* br)))

       (implies
        (and (booleanp x)
             (equal x (nth 0 inputs))
             (queue8$valid-st q8 data-width)
             (equal br-lselect '(t))
             (not (queue8$ready-in- q8))
             (equal br-lselect-buf '(nil)))
        (equal (joint-act x
                          (car br-select)
                          (car (nthcdr (+ *round-robin3$go-branch-offset*
                                          data-width)
                                       inputs)))
               (queue8$in-act
                (round-robin3$q8-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        f-or3
                                        queue8$valid-st=>natp-data-width
                                        queue8$in-act
                                        alt-branch$act0
                                        round-robin3$q8-inputs
                                        round-robin3$br-inputs)))))

  (local
   (defthm round-robin3$rewrite-to-q8-in-act-3
     (b* ((q8 (nth *round-robin3$q8* st))
          (br (nth *round-robin3$br* st))

          (br-lselect (nth *alt-branch$lselect* br))
          (br-select (nth *alt-branch$select* br))
          (br-lselect-buf (nth *alt-branch$lselect-buf* br)))

       (implies
        (and (equal (nth 0 inputs) t)
             (queue8$valid-st q8 data-width)
             (equal br-lselect '(t))
             (not (car br-select))
             (not (queue8$ready-in- q8))
             (equal br-lselect-buf '(nil)))
        (equal (f-bool
                (car (nthcdr (+ *round-robin3$go-branch-offset*
                                data-width)
                             inputs)))
               (queue8$in-act
                (round-robin3$q8-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue8$valid-st=>natp-data-width
                                        queue8$in-act
                                        alt-branch$act0
                                        round-robin3$q8-inputs
                                        round-robin3$br-inputs)))))

  (local
   (defthm booleanp-round-robin3$q8-out-act
     (b* ((q8 (nth *round-robin3$q8* st))
          (q10 (nth *round-robin3$q10* st))
          (me (nth *round-robin3$me* st))

          (me-lselect (nth *alt-merge$lselect* me))
          (me-select (nth *alt-merge$select* me))
          (me-lselect-buf (nth *alt-merge$lselect-buf* me)))

       (implies (and (booleanp (nth 1 inputs))
                     (queue8$valid-st q8 data-width)
                     (queue10$valid-st q10 data-width)
                     (equal me-lselect '(t))
                     (not (car me-select))
                     (equal me-lselect-buf '(nil)))
                (booleanp (queue8$out-act
                           (round-robin3$q8-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue8$out-act
                                        alt-merge$act0
                                        round-robin3$q8-inputs
                                        round-robin3$me-inputs)))
     :rule-classes :type-prescription))

  (local
   (defthm round-robin3$rewrite-to-q8-out-act-1
     (b* ((q8 (nth *round-robin3$q8* st))
          (q10 (nth *round-robin3$q10* st))
          (me (nth *round-robin3$me* st))

          (me-lselect (nth *alt-merge$lselect* me))
          (me-select (nth *alt-merge$select* me))
          (me-lselect-buf (nth *alt-merge$lselect-buf* me)))

       (implies
        (and (booleanp x)
             (equal x (nth 1 inputs))
             (queue8$valid-st q8 data-width)
             (queue10$valid-st q10 data-width)
             (equal me-lselect '(t))
             (not (car me-select))
             (equal me-lselect-buf '(nil)))
        (equal (joint-act (queue8$ready-out q8)
                          x
                          (nth 0 (nthcdr (+ *round-robin3$go-merge-offset*
                                            data-width)
                                         inputs)))
               (queue8$out-act
                (round-robin3$q8-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue8$valid-st=>natp-data-width
                                        queue8$out-act
                                        alt-merge$act0
                                        round-robin3$q8-inputs
                                        round-robin3$me-inputs)))))

  (local
   (defthm round-robin3$rewrite-to-q8-out-act-2
     (b* ((q8 (nth *round-robin3$q8* st))
          (q10 (nth *round-robin3$q10* st))
          (me (nth *round-robin3$me* st))

          (me-lselect (nth *alt-merge$lselect* me))
          (me-select (nth *alt-merge$select* me))
          (me-lselect-buf (nth *alt-merge$lselect-buf* me)))

       (implies
        (and (booleanp x)
             (equal x (nth 1 inputs))
             (queue8$valid-st q8 data-width)
             (queue10$valid-st q10 data-width)
             (equal me-lselect '(t))
             (not (car me-select))
             (queue8$ready-out q8)
             (equal me-lselect-buf '(nil)))
        (equal (joint-act t
                          x
                          (nth 0 (nthcdr (+ *round-robin3$go-merge-offset*
                                            data-width)
                                         inputs)))
               (queue8$out-act
                (round-robin3$q8-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        f-and3
                                        queue8$valid-st=>natp-data-width
                                        queue8$out-act
                                        alt-merge$act0
                                        round-robin3$q8-inputs
                                        round-robin3$me-inputs)))))

  (local
   (defthm booleanp-round-robin3$q10-in-act
     (b* ((q10 (nth *round-robin3$q10* st))
          (br (nth *round-robin3$br* st))

          (br-lselect (nth *alt-branch$lselect* br))
          (br-select (nth *alt-branch$select* br))
          (br-lselect-buf (nth *alt-branch$lselect-buf* br)))

       (implies (and (booleanp (nth 0 inputs))
                     (queue10$valid-st q10 data-width)
                     (equal br-lselect '(t))
                     (equal (car br-select) t)
                     (equal br-lselect-buf '(nil)))
                (booleanp (queue10$in-act
                           (round-robin3$q10-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue10$in-act
                                        alt-branch$act1
                                        round-robin3$q10-inputs
                                        round-robin3$br-inputs)))
     :rule-classes :type-prescription))

  (local
   (defthm round-robin3$rewrite-to-q10-in-act-1
     (b* ((q10 (nth *round-robin3$q10* st))
          (br (nth *round-robin3$br* st))

          (br-lselect (nth *alt-branch$lselect* br))
          (br-select (nth *alt-branch$select* br))
          (br-lselect-buf (nth *alt-branch$lselect-buf* br)))

       (implies
        (and (booleanp x)
             (equal x (nth 0 inputs))
             (queue10$valid-st q10 data-width)
             (equal br-lselect '(t))
             (equal (car br-select) t)
             (equal br-lselect-buf '(nil)))
        (equal (joint-act x
                          (queue10$ready-in- q10)
                          (car (nthcdr (+ *round-robin3$go-branch-offset*
                                          data-width)
                                       inputs)))
               (queue10$in-act
                (round-robin3$q10-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue10$valid-st=>natp-data-width
                                        queue10$in-act
                                        alt-branch$act1
                                        round-robin3$q10-inputs
                                        round-robin3$br-inputs)))))

  (local
   (defthm round-robin3$rewrite-to-q10-in-act-2
     (b* ((q10 (nth *round-robin3$q10* st))
          (br (nth *round-robin3$br* st))

          (br-lselect (nth *alt-branch$lselect* br))
          (br-select (nth *alt-branch$select* br))
          (br-lselect-buf (nth *alt-branch$lselect-buf* br)))

       (implies
        (and (equal (nth 0 inputs) t)
             (queue10$valid-st q10 data-width)
             (equal br-lselect '(t))
             (booleanp (car br-select))
             (car br-select)
             (not (queue10$ready-in- q10))
             (equal br-lselect-buf '(nil)))
        (equal (f-bool
                (car (nthcdr (+ *round-robin3$go-branch-offset*
                                data-width)
                             inputs)))
               (queue10$in-act
                (round-robin3$q10-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue10$valid-st=>natp-data-width
                                        queue10$in-act
                                        alt-branch$act1
                                        round-robin3$q10-inputs
                                        round-robin3$br-inputs)))))

  (local
   (defthm booleanp-round-robin3$q10-out-act
     (b* ((q8 (nth *round-robin3$q8* st))
          (q10 (nth *round-robin3$q10* st))
          (me (nth *round-robin3$me* st))

          (me-lselect (nth *alt-merge$lselect* me))
          (me-select (nth *alt-merge$select* me))
          (me-lselect-buf (nth *alt-merge$lselect-buf* me)))

       (implies (and (booleanp (nth 1 inputs))
                     (queue8$valid-st q8 data-width)
                     (queue10$valid-st q10 data-width)
                     (equal me-lselect '(t))
                     (equal (car me-select) t)
                     (equal me-lselect-buf '(nil)))
                (booleanp (queue10$out-act
                           (round-robin3$q10-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue10$out-act
                                        alt-merge$act1
                                        round-robin3$q10-inputs
                                        round-robin3$me-inputs)))
     :rule-classes :type-prescription))

  (local
   (defthm round-robin3$rewrite-to-q10-out-act-1
     (b* ((q8 (nth *round-robin3$q8* st))
          (q10 (nth *round-robin3$q10* st))
          (me (nth *round-robin3$me* st))

          (me-lselect (nth *alt-merge$lselect* me))
          (me-select (nth *alt-merge$select* me))
          (me-lselect-buf (nth *alt-merge$lselect-buf* me)))

       (implies
        (and (booleanp x)
             (equal x (nth 1 inputs))
             (queue8$valid-st q8 data-width)
             (queue10$valid-st q10 data-width)
             (equal me-lselect '(t))
             (equal (car me-select) t)
             (equal me-lselect-buf '(nil)))
        (equal (joint-act (queue10$ready-out q10)
                          x
                          (nth 0 (nthcdr (+ *round-robin3$go-merge-offset*
                                            data-width)
                                         inputs)))
               (queue10$out-act
                (round-robin3$q10-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue10$valid-st=>natp-data-width
                                        queue10$out-act
                                        alt-merge$act1
                                        round-robin3$q10-inputs
                                        round-robin3$me-inputs)))))

  (local
   (defthm round-robin3$rewrite-to-q10-out-act-2
     (b* ((q8 (nth *round-robin3$q8* st))
          (q10 (nth *round-robin3$q10* st))
          (me (nth *round-robin3$me* st))

          (me-lselect (nth *alt-merge$lselect* me))
          (me-select (nth *alt-merge$select* me))
          (me-lselect-buf (nth *alt-merge$lselect-buf* me)))

       (implies
        (and (booleanp x)
             (equal x (nth 1 inputs))
             (queue8$valid-st q8 data-width)
             (queue10$valid-st q10 data-width)
             (equal me-lselect '(t))
             (queue10$ready-out q10)
             (equal me-lselect-buf '(nil)))
        (equal (joint-act (car me-select)
                          x
                          (nth 0 (nthcdr (+ *round-robin3$go-merge-offset*
                                            data-width)
                                         inputs)))
               (queue10$out-act
                (round-robin3$q10-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        f-and3
                                        queue10$valid-st=>natp-data-width
                                        queue10$out-act
                                        alt-merge$act1
                                        round-robin3$q10-inputs
                                        round-robin3$me-inputs)))))

  (local
   (defthm round-robin3$rewrite-to-q10-out-act-3
     (b* ((q8 (nth *round-robin3$q8* st))
          (q10 (nth *round-robin3$q10* st))
          (me (nth *round-robin3$me* st))

          (me-lselect (nth *alt-merge$lselect* me))
          (me-select (nth *alt-merge$select* me))
          (me-lselect-buf (nth *alt-merge$lselect-buf* me)))

       (implies
        (and (booleanp x)
             (equal x (nth 1 inputs))
             (queue8$valid-st q8 data-width)
             (queue10$valid-st q10 data-width)
             (equal me-lselect '(t))
             (booleanp (car me-select))
             (car me-select)
             (queue10$ready-out q10)
             (equal me-lselect-buf '(nil)))
        (equal (joint-act t
                          x
                          (nth 0 (nthcdr (+ *round-robin3$go-merge-offset*
                                            data-width)
                                         inputs)))
               (queue10$out-act
                (round-robin3$q10-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        f-and3
                                        queue10$valid-st=>natp-data-width
                                        queue10$out-act
                                        alt-merge$act1
                                        round-robin3$q10-inputs
                                        round-robin3$me-inputs)))))

  (defthm round-robin3$inv-preserved
    (implies (and (round-robin3$input-format inputs data-width)
                  (round-robin3$valid-st st data-width)
                  (round-robin3$inv st))
             (round-robin3$inv (round-robin3$step inputs st data-width)))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              queue8$valid-st=>natp-data-width
                              queue8$extracted-step
                              queue10$extracted-step
                              round-robin3$input-format
                              round-robin3$valid-st
                              round-robin3$inv
                              round-robin3$step
                              round-robin3$in-act
                              round-robin3$out-act
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
                             (nfix
                              nthcdr
                              len-nthcdr
                              append
                              pairlis$
                              strip-cars
                              true-listp
                              default-car
                              default-cdr
                              default-+-1
                              default-+-2
                              take-of-too-many
                              open-v-threefix)))))
  )

;; The extracted next-state function for RR3.  Note that this function avoids
;; exploring the internal computation of RR3.

(defund round-robin3$extracted-step (inputs st data-width)
  (b* ((data-in (round-robin3$data-in inputs data-width))
       (extracted-st (round-robin3$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (round-robin3$out-act inputs st data-width) t)
      (cond
       ((equal (round-robin3$in-act inputs st data-width) t)
        (cons data-in (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (round-robin3$in-act inputs st data-width) t)
          (cons data-in extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm round-robin3$q8-and-q10-get-$data-in-rewrite
     (implies (bvp (round-robin3$data-in inputs data-width))
              (and (equal (queue8$data-in
                           (round-robin3$q8-inputs inputs st data-width)
                           data-width)
                          (round-robin3$data-in inputs data-width))
                   (equal (queue10$data-in
                           (round-robin3$q10-inputs inputs st data-width)
                           data-width)
                          (round-robin3$data-in inputs data-width))))
     :hints (("Goal"
              :in-theory (enable queue8$data-in
                                 queue10$data-in
                                 round-robin3$q8-inputs
                                 round-robin3$q10-inputs)))))

  (local
   (defthm cons-interleave
     (implies (consp l1)
              (equal (cons (car l1)
                           (interleave l2 (cdr l1)))
                     (interleave l1 l2)))))

  (local
   (defthmd take-interleave-1
     (implies (and (equal (len l1) (len l2))
                   (natp m)
                   (<= m (len l1))
                   (equal m (1+ n)))
              (equal (take (+ m n) (interleave l1 l2))
                     (interleave (take m l1) (take n l2))))))

  (local
   (defthmd take-interleave-2
     (implies (and (equal (len l1) (1+ (len l2)))
                   (natp m)
                   (<= m (len l1))
                   (equal m n))
              (equal (take (+ m n) (interleave l1 l2))
                     (interleave (take m l1) (take n l2))))))

  (local
   (defthm take-interleave-1-instance
     (implies (and (equal (len l1) (len l2))
                   (true-listp l1)
                   (equal m (+ -1 (len l1) (len l2)))
                   (equal n (1- (len l2))))
              (equal (take m (interleave l1 l2))
                     (interleave l1 (take n l2))))
     :hints (("Goal"
              :use (:instance take-interleave-1
                              (m (- m n)))))))

  (local
   (defthm take-interleave-2-instance
     (implies (and (equal (len l1) (1+ (len l2)))
                   (true-listp l2)
                   (equal m (1- (len l1)))
                   (equal n (+ -1 (len l1) (len l2))))
              (equal (take n (interleave l1 l2))
                     (interleave (take m l1) l2)))
     :hints (("Goal"
              :use (:instance take-interleave-2
                              (n (- n m)))))))

  (defthm round-robin3$extracted-step-correct
    (b* ((next-st (round-robin3$step inputs st data-width)))
      (implies (and (round-robin3$input-format inputs data-width)
                    (round-robin3$valid-st st data-width)
                    (round-robin3$inv st))
               (equal (round-robin3$extract next-st)
                      (round-robin3$extracted-step inputs st data-width))))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              queue8$valid-st=>natp-data-width
                              queue8$extracted-step
                              queue10$extracted-step
                              round-robin3$extracted-step
                              round-robin3$input-format
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
                             (nfix
                              nthcdr
                              len-nthcdr
                              pairlis$
                              strip-cars
                              not
                              default-car
                              default-cdr
                              default-+-1
                              default-+-2)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Extract the accepted input sequence

(defun round-robin3$in-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (round-robin3$in-act inputs st data-width) t)
          (append (round-robin3$in-seq
                   (cdr inputs-lst)
                   (round-robin3$step inputs st data-width)
                   data-width
                   (1- n))
                  (list (round-robin3$data-in inputs data-width)))
        (round-robin3$in-seq (cdr inputs-lst)
                             (round-robin3$step inputs st data-width)
                             data-width
                             (1- n))))))

;; Extract the valid output sequence

(defun round-robin3$out-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (round-robin3$out-act inputs st data-width) t)
          (append (round-robin3$out-seq
                   (cdr inputs-lst)
                   (round-robin3$step inputs st data-width)
                   data-width
                   (1- n))
                  (list (round-robin3$data-out st)))
        (round-robin3$out-seq (cdr inputs-lst)
                              (round-robin3$step inputs st data-width)
                              data-width
                              (1- n))))))

;; Input-output sequence simulator

(defund round-robin3$in-out-seq-sim (data-width n state)
  (declare (xargs :guard (and (natp data-width)
                              (natp n))
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals (round-robin3$ins-len data-width))
       ((mv inputs-lst state)
        (signal-vals-gen num-signals n state nil))
       (full '(t))
       (empty '(nil))
       (invalid-data (make-list data-width :initial-element '(x)))
       (q4-0 (list empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data))
       (q4-1 (list empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data))
       (q8 (list q4-0 q4-1))
       (q5-0 (list empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data))
       (q5-1 (list empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data))
       (q10 (list q5-0 q5-1))
       (br (list full '(nil)
                 empty '(x)))
       (me (list full '(nil)
                 empty '(x)))
       (st (list q8 q10 br me)))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-lst
                   (round-robin3$in-seq inputs-lst st data-width n))))
      (list (cons 'out-seq
                  (v-to-nat-lst
                   (round-robin3$out-seq inputs-lst st data-width n)))))
     state)))

;; Prove that round-robin3$valid-st is an invariant.

(defthm round-robin3$valid-st-preserved
  (implies (and (round-robin3$input-format inputs data-width)
                (round-robin3$valid-st st data-width))
           (round-robin3$valid-st
            (round-robin3$step inputs st data-width)
            data-width))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            round-robin3$valid-st
                            round-robin3$step)
                           ()))))

(encapsulate
  ()

  (local
   (defthm nth-interleave-1
     (implies (and (equal (len l1) (len l2))
                   (natp m)
                   (< m (len l2)))
              (equal (nth m l2)
                     (nth (+ 1 m m) (interleave l1 l2))))
     :hints (("Goal" :in-theory (enable nth)))
     :rule-classes nil))

  (local
   (defthm nth-interleave-2
     (implies (and (equal (len l1) (1+ (len l2)))
                   (natp m)
                   (< m (len l1)))
              (equal (nth m l1)
                     (nth (+ m m) (interleave l1 l2))))
     :hints (("Goal" :in-theory (enable nth)))
     :rule-classes nil))

  (local
   (defthm len-0-is-atom
     (equal (equal (len x) 0)
            (atom x))))

  (local
   (defthm nth-interleave-1-instance-1
     (implies (and (equal (len l1)
                          (len (queue8$extract st)))
                   (equal m (1- (len (queue8$extract st))))
                   (equal n (+ -1
                               (len l1)
                               (len (queue8$extract st)))))
              (equal (nth m (queue8$extract st))
                     (nth n (interleave l1 (queue8$extract st)))))
     :hints (("Goal" :use (:instance nth-interleave-1
                                     (l2 (queue8$extract st)))))))

  (local
   (defthm nth-interleave-1-instance-2
     (implies (and (equal (len l1)
                          (len (queue10$extract st)))
                   (equal m (1- (len (queue10$extract st))))
                   (equal n (+ -1
                               (len l1)
                               (len (queue10$extract st)))))
              (equal (nth m (queue10$extract st))
                     (nth n (interleave l1 (queue10$extract st)))))
     :hints (("Goal" :use (:instance nth-interleave-1
                                     (l2 (queue10$extract st)))))))

  (local
   (defthm nth-interleave-2-instance-1
     (implies (and (equal (len (queue8$extract st))
                          (1+ (len l2)))
                   (equal m (1- (len (queue8$extract st))))
                   (equal n (+ -1
                               (len (queue8$extract st))
                               (len l2))))
              (equal (nth m (queue8$extract st))
                     (nth n (interleave (queue8$extract st)
                                        l2))))
     :hints (("Goal" :use (:instance nth-interleave-2
                                     (l1 (queue8$extract st)))))))

  (local
   (defthm nth-interleave-2-instance-2
     (implies (and (equal (len (queue10$extract st))
                          (1+ (len l2)))
                   (equal m (1- (len (queue10$extract st))))
                   (equal n (+ -1
                               (len (queue10$extract st))
                               (len l2))))
              (equal (nth m (queue10$extract st))
                     (nth n (interleave (queue10$extract st)
                                        l2))))
     :hints (("Goal" :use (:instance nth-interleave-2
                                     (l1 (queue10$extract st)))))))

  (defthm round-robin3$extract-lemma
    (implies (and (round-robin3$input-format inputs data-width)
                  (round-robin3$valid-st st data-width)
                  (round-robin3$inv st)
                  (equal n (1- (len (round-robin3$extract st))))
                  (round-robin3$out-act inputs st data-width))
             (equal (append (take n (round-robin3$extract st))
                            (list (round-robin3$data-out st)))
                    (round-robin3$extract st)))
    :hints (("Goal"
             :do-not-induct t
             :use round-robin3$valid-st=>natp-data-width
             :in-theory (e/d (get-field
                              f-and3
                              queue8$data-out-rewrite
                              queue10$data-out-rewrite
                              round-robin3$input-format
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
                             (nfix
                              nthcdr
                              len-nthcdr
                              if*
                              append
                              pairlis$
                              strip-cars
                              default-car
                              default-cdr
                              default-+-1
                              default-+-2)))))
  )

(in-out-stream-lemma round-robin3 :inv t)

