;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; April 2018

(in-package "ADE")

(include-book "alt-branch")
(include-book "alt-merge")
(include-book "queue4-as-link")
(include-book "queue5-as-link")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of RR2
;;; 2. Specify the Final State of RR2 After An N-Step Execution
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of RR2
;;
;; Construct a DE module generator for a round-robin circuit, RR2, using the
;; link-joint model.  Prove the value and state lemmas for this module
;; generator.

(defconst *round-robin2$go-num* (+ *queue4$go-num*
                                   *queue5$go-num*
                                   *alt-branch$go-num*
                                   *alt-merge$go-num*))
(defconst *round-robin2$st-len* 4)

(defconst *round-robin2$go-branch-offset*
  (+ 2 *queue4$go-num* *queue5$go-num*))

(defconst *round-robin2$go-merge-offset*
  (+ 2 *queue4$go-num* *queue5$go-num* *alt-branch$go-num*))

(defun round-robin2$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun round-robin2$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (round-robin2$data-ins-len data-width)
     *round-robin2$go-num*))

;; DE module generator of RR2.  The ALT-BRANCH joint in RR2 accepts input data
;; and places them alternately into two queues.  The ALT-MERGE joint takes data
;; alternately from two queues and delivers them as outputs.

(module-generator
 round-robin2* (data-width)
 (si 'round-robin2 data-width)
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 data-width)
                                    (sis 'go 0 *round-robin2$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-width))
 '(q4 q5 br me)
 (list
  ;; LINKS
  ;; 4-link queue Q4
  (list 'q4
        (list* 'q4-ready-in- 'q4-ready-out
               (sis 'q4-data-out 0 data-width))
        (si 'queue4 data-width)
        (list* 'br-act0 'me-act0
               (append (sis 'data 0 data-width)
                       (sis 'go 0 *queue4$go-num*))))

  ;; 5-link queue Q5
  (list 'q5
        (list* 'q5-ready-in- 'q5-ready-out
               (sis 'q5-data-out 0 data-width))
        (si 'queue5 data-width)
        (list* 'br-act1 'me-act1
               (append (sis 'data 0 data-width)
                       (sis 'go
                            *queue4$go-num*
                            *queue5$go-num*))))

  ;; JOINTS
  ;; Alt-Branch
  (list 'br
        (list* 'in-act 'br-act0 'br-act1
               (sis 'data 0 data-width))
        (si 'alt-branch data-width)
        (list* 'full-in 'q4-ready-in- 'q5-ready-in-
               (append (sis 'data-in 0 data-width)
                       (sis 'go
                            (+ *queue4$go-num*
                               *queue5$go-num*)
                            *alt-branch$go-num*))))

  ;; Alt-Merge
  (list 'me
        (list* 'out-act 'me-act0 'me-act1
               (sis 'data-out 0 data-width))
        (si 'alt-merge data-width)
        (list* 'q4-ready-out 'q5-ready-out 'empty-out-
               (append (sis 'q4-data-out 0 data-width)
                       (sis 'q5-data-out 0 data-width)
                       (sis 'go
                            (+ *queue4$go-num*
                               *queue5$go-num*
                               *alt-branch$go-num*)
                            *alt-merge$go-num*)))))

 :guard (natp data-width))

(make-event
 `(progn
    ,@(state-accessors-gen 'round-robin2 '(q4 q5 br me) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of RR2.

(defun round-robin2$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (round-robin2* data-width)
        (union$ (queue4$netlist data-width)
                (queue5$netlist data-width)
                (alt-branch$netlist data-width)
                (alt-merge$netlist data-width)
                :test 'equal)))

;; Recognizer for RR2

(defund round-robin2& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (and (equal (assoc (si 'round-robin2 data-width) netlist)
              (round-robin2* data-width))
       (b* ((netlist (delete-to-eq (si 'round-robin2 data-width) netlist)))
         (and (queue4& netlist data-width)
              (queue5& netlist data-width)
              (alt-branch& netlist data-width)
              (alt-merge& netlist data-width)))))

;; Sanity check

(local
 (defthmd check-round-robin2$netlist-64
   (and (net-syntax-okp (round-robin2$netlist 64))
        (net-arity-okp (round-robin2$netlist 64))
        (round-robin2& (round-robin2$netlist 64) 64))))

;; Constraints on the state of RR2

(defund round-robin2$st-format (st data-width)
  (b* ((q4 (get-field *round-robin2$q4* st))
       (q5 (get-field *round-robin2$q5* st)))
    (and (< 0 data-width)
         (queue4$st-format q4 data-width)
         (queue5$st-format q5 data-width))))

(defthm round-robin2$st-format=>posp-data-width
  (implies (round-robin2$st-format st data-width)
           (posp data-width))
  :hints (("Goal" :in-theory (enable round-robin2$st-format)))
  :rule-classes :forward-chaining)

(defund round-robin2$valid-st (st data-width)
  (b* ((q4 (get-field *round-robin2$q4* st))
       (q5 (get-field *round-robin2$q5* st))
       (br (get-field *round-robin2$br* st))
       (me (get-field *round-robin2$me* st)))
    (and (queue4$valid-st q4 data-width)
         (queue5$valid-st q5 data-width)

         (alt-branch$valid-st br)
         (alt-merge$valid-st me))))

(defthmd round-robin2$valid-st=>natp-data-width
  (implies (round-robin2$valid-st st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable round-robin2$valid-st
                                     queue4$valid-st=>natp-data-width)))
  :rule-classes :forward-chaining)

;; Extract the input and output signals from RR2

(progn
  ;; Extract the input data

  (defun round-robin2$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 2 inputs)))

  (defthm len-round-robin2$data-in
    (equal (len (round-robin2$data-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable round-robin2$data-in))

  ;; Extract the inputs for joint ALT-BRANCH

  (defund round-robin2$br-inputs (inputs st data-width)
    (b* ((full-in (nth 0 inputs))
         (data-in (round-robin2$data-in inputs data-width))
         (go-signals (nthcdr (round-robin2$data-ins-len data-width) inputs))

         (br-go-signals (take *alt-branch$go-num*
                              (nthcdr (+ *queue4$go-num*
                                         *queue5$go-num*)
                                      go-signals)))

         (q4 (get-field *round-robin2$q4* st))
         (q5 (get-field *round-robin2$q5* st))

         (q4-ready-in- (queue4$ready-in- q4))
         (q5-ready-in- (queue5$ready-in- q5)))

      (list* full-in q4-ready-in- q5-ready-in-
             (append data-in br-go-signals))))

  ;; Extract the inputs for joint ALT-MERGE

  (defund round-robin2$me-inputs (inputs st data-width)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (round-robin2$data-ins-len data-width) inputs))

         (me-go-signals (nthcdr (+ *queue4$go-num*
                                   *queue5$go-num*
                                   *alt-branch$go-num*)
                                go-signals))

         (q4 (get-field *round-robin2$q4* st))
         (q5 (get-field *round-robin2$q5* st))

         (q4-ready-out (queue4$ready-out q4))
         (q4-data-out (queue4$data-out q4))
         (q5-ready-out (queue5$ready-out q5))
         (q5-data-out (queue5$data-out q5)))

      (list* q4-ready-out q5-ready-out empty-out-
             (append q4-data-out q5-data-out me-go-signals))))

  ;; Extract the inputs for link Q4'

  (defund round-robin2$q4-inputs (inputs st data-width)
    (b* ((data-in (round-robin2$data-in inputs data-width))
         (go-signals (nthcdr (round-robin2$data-ins-len data-width) inputs))

         (q4-go-signals (take *queue4$go-num* go-signals))

         (br (get-field *round-robin2$br* st))
         (me (get-field *round-robin2$me* st))

         (br-inputs (round-robin2$br-inputs inputs st data-width))
         (me-inputs (round-robin2$me-inputs inputs st data-width))

         (br-act0 (alt-branch$act0 br-inputs br data-width))
         (me-act0 (alt-merge$act0 me-inputs me data-width)))

      (list* br-act0 me-act0
             (append (v-threefix data-in)
                     q4-go-signals))))

  ;; Extract the inputs for link Q5'

  (defund round-robin2$q5-inputs (inputs st data-width)
    (b* ((data-in (round-robin2$data-in inputs data-width))
         (go-signals (nthcdr (round-robin2$data-ins-len data-width) inputs))

         (q5-go-signals (take *queue5$go-num*
                              (nthcdr *queue4$go-num*
                                      go-signals)))

         (br (get-field *round-robin2$br* st))
         (me (get-field *round-robin2$me* st))

         (br-inputs (round-robin2$br-inputs inputs st data-width))
         (me-inputs (round-robin2$me-inputs inputs st data-width))

         (br-act1 (alt-branch$act1 br-inputs br data-width))
         (me-act1 (alt-merge$act1 me-inputs me data-width)))

      (list* br-act1 me-act1
             (append (v-threefix data-in)
                     q5-go-signals))))

  ;; Extract the "in-act" signal

  (defund round-robin2$in-act (inputs st data-width)
    (b* ((br-inputs (round-robin2$br-inputs inputs st data-width))
         (br (get-field *round-robin2$br* st)))
      (alt-branch$act br-inputs br data-width)))

  ;; Extract the "out-act" signal

  (defund round-robin2$out-act (inputs st data-width)
    (b* ((me-inputs (round-robin2$me-inputs inputs st data-width))
         (me (get-field *round-robin2$me* st)))
      (alt-merge$act me-inputs me data-width)))

  ;; Extract the output data

  (defund round-robin2$data-out (st)
    (b* ((q4 (get-field *round-robin2$q4* st))
         (q5 (get-field *round-robin2$q5* st))
         (me (get-field *round-robin2$me* st))

         (q4-data-out (queue4$data-out q4))
         (q5-data-out (queue5$data-out q5))

         (me-select (get-field *alt-merge$select* me)))
      (fv-if (car me-select)
             q5-data-out
             q4-data-out)))

  (defthm len-round-robin2$data-out-1
    (implies (round-robin2$st-format st data-width)
             (equal (len (round-robin2$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable round-robin2$st-format
                                       round-robin2$data-out))))

  (defthm len-round-robin2$data-out-2
    (implies (round-robin2$valid-st st data-width)
             (equal (len (round-robin2$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable round-robin2$valid-st
                                       round-robin2$data-out))))

  (defthm bvp-round-robin2$data-out
    (implies (and (round-robin2$valid-st st data-width)
                  (round-robin2$out-act inputs st data-width))
             (bvp (round-robin2$data-out st)))
    :hints (("Goal" :in-theory (enable f-and3
                                       f-and
                                       joint-act
                                       round-robin2$valid-st
                                       round-robin2$out-act
                                       round-robin2$data-out
                                       round-robin2$me-inputs
                                       queue4$valid-st=>natp-data-width
                                       alt-merge$valid-st
                                       alt-merge$act
                                       alt-merge$act0
                                       alt-merge$act1))))
  )

(not-primp-lemma round-robin2) ;; Prove that RR2 is not a DE primitive.

;; The value lemma for RR2

(defthmd round-robin2$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (round-robin2& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *round-robin2$go-num*)
                  (round-robin2$st-format st data-width))
             (equal (se (si 'round-robin2 data-width) inputs st netlist)
                    (list* (round-robin2$in-act inputs st data-width)
                           (round-robin2$out-act inputs st data-width)
                           (round-robin2$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :expand (se (si 'round-robin2 data-width)
                       (list* full-in empty-out-
                              (append data-in go-signals))
                       st
                       netlist)
           :in-theory (e/d (de-rules
                            not-primp-round-robin2
                            round-robin2&
                            round-robin2*$destructure
                            round-robin2$data-in
                            queue4$value
                            queue5$value
                            alt-branch$value
                            alt-merge$value
                            round-robin2$st-format
                            round-robin2$in-act
                            round-robin2$out-act
                            round-robin2$data-out
                            round-robin2$br-inputs
                            round-robin2$me-inputs)
                           ((round-robin2*)
                            de-module-disabled-rules)))))

;; This function specifies the next state of RR2.

(defun round-robin2$step (inputs st data-width)
  (b* ((q4 (get-field *round-robin2$q4* st))
       (q5 (get-field *round-robin2$q5* st))
       (br (get-field *round-robin2$br* st))
       (me (get-field *round-robin2$me* st))

       (q4-inputs (round-robin2$q4-inputs inputs st data-width))
       (q5-inputs (round-robin2$q5-inputs inputs st data-width))
       (br-inputs (round-robin2$br-inputs inputs st data-width))
       (me-inputs (round-robin2$me-inputs inputs st data-width)))

    (list
     ;; Q4'
     (queue4$step q4-inputs q4 data-width)
     ;; Q5'
     (queue5$step q5-inputs q5 data-width)
     ;; Joint alt-branch
     (alt-branch$step br-inputs br data-width)
     ;; Joint alt-merge
     (alt-merge$step me-inputs me data-width))))

(defthm len-of-round-robin2$step
  (equal (len (round-robin2$step inputs st data-width))
         *round-robin2$st-len*))

;; The state lemma for RR2

(defthmd round-robin2$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (round-robin2& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *round-robin2$go-num*)
                  (round-robin2$st-format st data-width))
             (equal (de (si 'round-robin2 data-width) inputs st netlist)
                    (round-robin2$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :expand (de (si 'round-robin2 data-width)
                       (list* full-in empty-out-
                              (append data-in go-signals))
                       st
                       netlist)
           :in-theory (e/d (de-rules
                            not-primp-round-robin2
                            round-robin2&
                            round-robin2*$destructure
                            round-robin2$st-format
                            round-robin2$data-in
                            round-robin2$q4-inputs
                            round-robin2$q5-inputs
                            round-robin2$br-inputs
                            round-robin2$me-inputs
                            queue4$value queue4$state
                            queue5$value queue5$state
                            alt-branch$value alt-branch$state
                            alt-merge$value alt-merge$state)
                           ((round-robin2*)
                            de-module-disabled-rules)))))

(in-theory (disable round-robin2$step))

;; ======================================================================

;; 2. Specify the Final State of RR2 After An N-Step Execution

;; RR2 simulator

(progn
  (defun round-robin2$map-to-links (st)
    (b* ((q4 (get-field *round-robin2$q4* st))
         (q5 (get-field *round-robin2$q5* st))
         (br (get-field *round-robin2$br* st))
         (me (get-field *round-robin2$me* st)))
      (append (list (cons 'alt-branch (alt-branch$map-to-links br)))
              (list (cons 'Q4 (queue4$map-to-links q4)))
              (list (cons 'Q5 (queue5$map-to-links q5)))
              (list (cons 'alt-merge (alt-merge$map-to-links me))))))

  (defun round-robin2$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (round-robin2$map-to-links (car x))
            (round-robin2$map-to-links-list (cdr x)))))

  (defund round-robin2$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (round-robin2$ins-len data-width))
         ((mv inputs-lst state)
          (signal-vals-gen num-signals n state nil))
         ;;(- (cw "~x0~%" inputs-lst))
         (full '(t))
         (empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (q4 (list empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data))
         (q5 (list empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data))
         (br (list full '(nil)
                   empty '(x)))
         (me (list full '(nil)
                   empty '(x)))
         (st (list q4 q5 br me)))
      (mv (pretty-list
           (remove-dup-neighbors
            (round-robin2$map-to-links-list
             (de-sim-list (si 'round-robin2 data-width)
                          inputs-lst
                          st
                          (round-robin2$netlist data-width))))
           0)
          state)))
  )

;; Conditions on the inputs

(defund round-robin2$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (round-robin2$data-in inputs data-width))
       (go-signals (nthcdr (round-robin2$data-ins-len data-width) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *round-robin2$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(defthmd len-of-round-robin2$inputs
  (implies (round-robin2$input-format inputs data-width)
           (equal (len inputs) (round-robin2$ins-len data-width)))
  :hints (("Goal" :in-theory (enable round-robin2$input-format))))

(local
 (defthm round-robin2$input-format=>q4$input-format
   (implies (and (round-robin2$input-format inputs data-width)
                 (round-robin2$valid-st st data-width))
            (queue4$input-format
             (round-robin2$q4-inputs inputs st data-width)
             (nth *round-robin2$q4* st)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             f-and3
                             queue4$input-format
                             queue4$in-act
                             queue4$out-act
                             queue4$data-in
                             alt-branch$valid-st
                             alt-branch$act
                             alt-branch$act0
                             alt-merge$valid-st
                             alt-merge$act
                             alt-merge$act0
                             round-robin2$input-format
                             round-robin2$valid-st
                             round-robin2$data-in
                             round-robin2$q4-inputs
                             round-robin2$br-inputs
                             round-robin2$me-inputs)
                            (nfix
                             nthcdr
                             b-not
                             take-of-too-many))))))

(local
 (defthm round-robin2$input-format=>q5$input-format
   (implies (and (round-robin2$input-format inputs data-width)
                 (round-robin2$valid-st st data-width))
            (queue5$input-format
             (round-robin2$q5-inputs inputs st data-width)
             (nth *round-robin2$q5* st)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             f-and3
                             queue5$input-format
                             queue5$in-act
                             queue5$out-act
                             queue5$data-in
                             alt-branch$valid-st
                             alt-branch$act
                             alt-branch$act1
                             alt-merge$valid-st
                             alt-merge$act
                             alt-merge$act1
                             round-robin2$input-format
                             round-robin2$valid-st
                             round-robin2$data-in
                             round-robin2$q5-inputs
                             round-robin2$br-inputs
                             round-robin2$me-inputs)
                            (nfix
                             nthcdr
                             b-not
                             take-of-too-many))))))

(local
 (defthm round-robin2$input-format=>br$input-format
   (implies (and (round-robin2$input-format inputs data-width)
                 (round-robin2$valid-st st data-width))
            (alt-branch$input-format
             (round-robin2$br-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (alt-branch$input-format
                             alt-branch$data-in
                             round-robin2$input-format
                             round-robin2$valid-st
                             round-robin2$data-in
                             round-robin2$br-inputs)
                            (nfix
                             nthcdr
                             take-of-too-many))))))

(local
 (defthm round-robin2$input-format=>me$input-format
   (implies (and (round-robin2$input-format inputs data-width)
                 (round-robin2$valid-st st data-width))
            (alt-merge$input-format
             (round-robin2$me-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :use len-of-round-robin2$inputs
            :in-theory (e/d (queue4$valid-st=>natp-data-width
                             alt-merge$input-format
                             alt-merge$data-in0
                             alt-merge$data-in1
                             round-robin2$input-format
                             round-robin2$valid-st
                             round-robin2$me-inputs)
                            (nthcdr
                             take-of-too-many))))))

(simulate-lemma round-robin2)

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

;; The extraction function for RR2 that extracts the future output sequence
;; from the current state.

(defund round-robin2$extract (st)
  (b* ((q4 (get-field *round-robin2$q4* st))
       (q5 (get-field *round-robin2$q5* st))
       (me (get-field *round-robin2$me* st))

       (a-seq (queue4$extract q4))
       (b-seq (queue5$extract q5))

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

(defthm round-robin2$extract-not-empty
  (implies (and (round-robin2$out-act inputs st data-width)
                (round-robin2$valid-st st data-width))
           (< 0 (len (round-robin2$extract st))))
  :hints (("Goal"
           :in-theory (e/d (f-and3
                            f-and
                            joint-act
                            alt-merge$act
                            alt-merge$act0
                            alt-merge$act1
                            round-robin2$me-inputs
                            round-robin2$valid-st
                            round-robin2$extract
                            round-robin2$out-act)
                           (nfix))))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund round-robin2$inv (st)
    (b* ((q4 (get-field *round-robin2$q4* st))
         (q5 (get-field *round-robin2$q5* st))
         (br (get-field *round-robin2$br* st))
         (me (get-field *round-robin2$me* st))

         (a-seq (queue4$extract q4))
         (b-seq (queue5$extract q5))

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
   (defthm round-robin2$q4+q5-in-act-nil
     (implies (not (nth 0 inputs))
              (and
               (not (queue4$in-act
                     (round-robin2$q4-inputs inputs st data-width)))
               (not (queue5$in-act
                     (round-robin2$q5-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (e/d (get-field
                                      queue4$in-act
                                      queue5$in-act
                                      alt-branch$act0
                                      alt-branch$act1
                                      round-robin2$q4-inputs
                                      round-robin2$q5-inputs
                                      round-robin2$br-inputs)
                                     ())))))

  (local
   (defthm round-robin2$q4-in-act-nil-1
     (b* ((br (nth *round-robin2$br* st))

          (br-lselect (nth *alt-branch$lselect* br))
          (br-select (nth *alt-branch$select* br))
          (br-lselect-buf (nth *alt-branch$lselect-buf* br)))

       (implies (and (alt-branch$valid-st br)
                     (or (and (equal br-lselect '(t))
                              (car br-select))
                         (equal br-lselect-buf '(t))))
                (not (queue4$in-act
                      (round-robin2$q4-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        f-or3
                                        queue4$in-act
                                        alt-branch$valid-st
                                        alt-branch$act0
                                        round-robin2$q4-inputs)))))

  (local
   (defthm round-robin2$q4-in-act-nil-2
     (implies (and (queue4$valid-st (nth *round-robin2$q4* st) data-width)
                   (queue4$ready-in- (nth *round-robin2$q4* st)))
              (not (queue4$in-act
                    (round-robin2$q4-inputs inputs st data-width))))
     :hints (("Goal" :in-theory (e/d (get-field
                                      f-or3
                                      queue4$valid-st
                                      queue4$ready-in-
                                      queue4$in-act
                                      alt-branch$act0
                                      round-robin2$q4-inputs
                                      round-robin2$br-inputs)
                                     ())))))

  (local
   (defthm round-robin2$q4-out-act-nil-1
     (b* ((me (nth *round-robin2$me* st))

          (me-lselect (nth *alt-merge$lselect* me))
          (me-select (nth *alt-merge$select* me))
          (me-lselect-buf (nth *alt-merge$lselect-buf* me)))

       (implies (and (alt-merge$valid-st me)
                     (or (and (equal me-lselect '(t))
                              (car me-select))
                         (equal me-lselect-buf '(t))))
                (not (queue4$out-act
                      (round-robin2$q4-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        f-and3
                                        queue4$out-act
                                        alt-merge$valid-st
                                        alt-merge$act0
                                        round-robin2$q4-inputs)))))

  (local
   (defthm round-robin2$q4-out-act-nil-2
     (implies (and (queue4$valid-st (nth *round-robin2$q4* st) data-width)
                   (not (queue4$ready-out (nth *round-robin2$q4* st))))
              (not (queue4$out-act
                    (round-robin2$q4-inputs inputs st data-width))))
     :hints (("Goal" :in-theory (e/d (get-field
                                      f-and3
                                      queue4$valid-st
                                      queue4$ready-out
                                      queue4$out-act
                                      alt-merge$act0
                                      round-robin2$q4-inputs
                                      round-robin2$me-inputs)
                                     ())))))

  (local
   (defthm round-robin2$q5-in-act-nil-1
     (b* ((br (nth *round-robin2$br* st))

          (br-lselect (nth *alt-branch$lselect* br))
          (br-select (nth *alt-branch$select* br))
          (br-lselect-buf (nth *alt-branch$lselect-buf* br)))

       (implies (and (alt-branch$valid-st br)
                     (or (and (equal br-lselect '(t))
                              (not (car br-select)))
                         (equal br-lselect-buf '(t))))
                (not (queue5$in-act
                      (round-robin2$q5-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        f-or3
                                        queue5$in-act
                                        alt-branch$valid-st
                                        alt-branch$act1
                                        round-robin2$q5-inputs)))))

  (local
   (defthm round-robin2$q5-in-act-nil-2
     (implies (and (queue5$valid-st (nth *round-robin2$q5* st) data-width)
                   (queue5$ready-in- (nth *round-robin2$q5* st)))
              (not (queue5$in-act
                    (round-robin2$q5-inputs inputs st data-width))))
     :hints (("Goal" :in-theory (e/d (get-field
                                      f-or3
                                      queue5$valid-st
                                      queue5$ready-in-
                                      queue5$in-act
                                      alt-branch$act1
                                      round-robin2$q5-inputs
                                      round-robin2$br-inputs)
                                     ())))))

  (local
   (defthm round-robin2$q5-out-act-nil-1
     (b* ((me (nth *round-robin2$me* st))

          (me-lselect (nth *alt-merge$lselect* me))
          (me-select (nth *alt-merge$select* me))
          (me-lselect-buf (nth *alt-merge$lselect-buf* me)))

       (implies (and (alt-merge$valid-st me)
                     (or (and (equal me-lselect '(t))
                              (not (car me-select)))
                         (equal me-lselect-buf '(t))))
                (not (queue5$out-act
                      (round-robin2$q5-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        f-and3
                                        queue5$out-act
                                        alt-merge$valid-st
                                        alt-merge$act1
                                        round-robin2$q5-inputs)))))

  (local
   (defthm round-robin2$q5-out-act-nil-2
     (implies (and (queue5$valid-st (nth *round-robin2$q5* st) data-width)
                   (not (queue5$ready-out (nth *round-robin2$q5* st))))
              (not (queue5$out-act
                    (round-robin2$q5-inputs inputs st data-width))))
     :hints (("Goal" :in-theory (e/d (get-field
                                      f-and3
                                      queue5$valid-st
                                      queue5$ready-out
                                      queue5$out-act
                                      alt-merge$act1
                                      round-robin2$q5-inputs
                                      round-robin2$me-inputs)
                                     ())))))

  (local
   (defthm booleanp-round-robin2$q4-in-act
     (b* ((q4 (nth *round-robin2$q4* st))
          (br (nth *round-robin2$br* st))

          (br-lselect (nth *alt-branch$lselect* br))
          (br-select (nth *alt-branch$select* br))
          (br-lselect-buf (nth *alt-branch$lselect-buf* br)))

       (implies (and (booleanp (nth 0 inputs))
                     (queue4$valid-st q4 data-width)
                     (equal br-lselect '(t))
                     (not (car br-select))
                     (equal br-lselect-buf '(nil)))
                (booleanp (queue4$in-act
                           (round-robin2$q4-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue4$in-act
                                        alt-branch$act0
                                        round-robin2$q4-inputs
                                        round-robin2$br-inputs)))
     :rule-classes :type-prescription))

  (local
   (defthm round-robin2$rewrite-to-q4-in-act-1
     (b* ((q4 (nth *round-robin2$q4* st))
          (br (nth *round-robin2$br* st))

          (br-lselect (nth *alt-branch$lselect* br))
          (br-select (nth *alt-branch$select* br))
          (br-lselect-buf (nth *alt-branch$lselect-buf* br)))

       (implies (and (booleanp x)
                     (equal x (nth 0 inputs))
                     (queue4$valid-st q4 data-width)
                     (equal br-lselect '(t))
                     (not (car br-select))
                     (equal br-lselect-buf '(nil)))
                (equal (joint-act
                        x
                        (queue4$ready-in- q4)
                        (car (nthcdr (+ *round-robin2$go-branch-offset*
                                        data-width)
                                     inputs)))
                       (queue4$in-act
                        (round-robin2$q4-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue4$valid-st=>natp-data-width
                                        queue4$in-act
                                        alt-branch$act0
                                        round-robin2$q4-inputs
                                        round-robin2$br-inputs)))))

  (local
   (defthm round-robin2$rewrite-to-q4-in-act-2
     (b* ((q4 (nth *round-robin2$q4* st))
          (br (nth *round-robin2$br* st))

          (br-lselect (nth *alt-branch$lselect* br))
          (br-select (nth *alt-branch$select* br))
          (br-lselect-buf (nth *alt-branch$lselect-buf* br)))

       (implies (and (booleanp x)
                     (equal x (nth 0 inputs))
                     (queue4$valid-st q4 data-width)
                     (equal br-lselect '(t))
                     (not (queue4$ready-in- q4))
                     (equal br-lselect-buf '(nil)))
                (equal (joint-act
                        x
                        (car br-select)
                        (car (nthcdr (+ *round-robin2$go-branch-offset*
                                        data-width)
                                     inputs)))
                       (queue4$in-act
                        (round-robin2$q4-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        f-or3
                                        queue4$valid-st=>natp-data-width
                                        queue4$in-act
                                        alt-branch$act0
                                        round-robin2$q4-inputs
                                        round-robin2$br-inputs)))))

  (local
   (defthm round-robin2$rewrite-to-q4-in-act-3
     (b* ((q4 (nth *round-robin2$q4* st))
          (br (nth *round-robin2$br* st))

          (br-lselect (nth *alt-branch$lselect* br))
          (br-select (nth *alt-branch$select* br))
          (br-lselect-buf (nth *alt-branch$lselect-buf* br)))

       (implies (and (equal (nth 0 inputs) t)
                     (queue4$valid-st q4 data-width)
                     (equal br-lselect '(t))
                     (not (car br-select))
                     (not (queue4$ready-in- q4))
                     (equal br-lselect-buf '(nil)))
                (equal (f-bool
                        (car (nthcdr (+ *round-robin2$go-branch-offset*
                                        data-width)
                                     inputs)))
                       (queue4$in-act
                        (round-robin2$q4-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue4$valid-st=>natp-data-width
                                        queue4$in-act
                                        alt-branch$act0
                                        round-robin2$q4-inputs
                                        round-robin2$br-inputs)))))

  (local
   (defthm booleanp-round-robin2$q4-out-act
     (b* ((q4 (nth *round-robin2$q4* st))
          (q5 (nth *round-robin2$q5* st))
          (me (nth *round-robin2$me* st))

          (me-lselect (nth *alt-merge$lselect* me))
          (me-select (nth *alt-merge$select* me))
          (me-lselect-buf (nth *alt-merge$lselect-buf* me)))

       (implies (and (booleanp (nth 1 inputs))
                     (queue4$valid-st q4 data-width)
                     (queue5$valid-st q5 data-width)
                     (equal me-lselect '(t))
                     (not (car me-select))
                     (equal me-lselect-buf '(nil)))
                (booleanp (queue4$out-act
                           (round-robin2$q4-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue4$out-act
                                        alt-merge$act0
                                        round-robin2$q4-inputs
                                        round-robin2$me-inputs)))
     :rule-classes :type-prescription))

  (local
   (defthm round-robin2$rewrite-to-q4-out-act-1
     (b* ((q4 (nth *round-robin2$q4* st))
          (q5 (nth *round-robin2$q5* st))
          (me (nth *round-robin2$me* st))

          (me-lselect (nth *alt-merge$lselect* me))
          (me-select (nth *alt-merge$select* me))
          (me-lselect-buf (nth *alt-merge$lselect-buf* me)))

       (implies (and (booleanp x)
                     (equal x (nth 1 inputs))
                     (queue4$valid-st q4 data-width)
                     (queue5$valid-st q5 data-width)
                     (equal me-lselect '(t))
                     (not (car me-select))
                     (equal me-lselect-buf '(nil)))
                (equal (joint-act
                        (queue4$ready-out q4)
                        x
                        (nth 0 (nthcdr (+ *round-robin2$go-merge-offset*
                                          data-width)
                                       inputs)))
                       (queue4$out-act
                        (round-robin2$q4-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue4$valid-st=>natp-data-width
                                        queue4$out-act
                                        alt-merge$act0
                                        round-robin2$q4-inputs
                                        round-robin2$me-inputs)))))

  (local
   (defthm round-robin2$rewrite-to-q4-out-act-2
     (b* ((q4 (nth *round-robin2$q4* st))
          (q5 (nth *round-robin2$q5* st))
          (me (nth *round-robin2$me* st))

          (me-lselect (nth *alt-merge$lselect* me))
          (me-select (nth *alt-merge$select* me))
          (me-lselect-buf (nth *alt-merge$lselect-buf* me)))

       (implies (and (booleanp x)
                     (equal x (nth 1 inputs))
                     (queue4$valid-st q4 data-width)
                     (queue5$valid-st q5 data-width)
                     (equal me-lselect '(t))
                     (not (car me-select))
                     (queue4$ready-out q4)
                     (equal me-lselect-buf '(nil)))
                (equal (joint-act
                        t
                        x
                        (nth 0 (nthcdr (+ *round-robin2$go-merge-offset*
                                          data-width)
                                       inputs)))
                       (queue4$out-act
                        (round-robin2$q4-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        f-and3
                                        queue4$valid-st=>natp-data-width
                                        queue4$out-act
                                        alt-merge$act0
                                        round-robin2$q4-inputs
                                        round-robin2$me-inputs)))))

  (local
   (defthm booleanp-round-robin2$q5-in-act
     (b* ((q5 (nth *round-robin2$q5* st))
          (br (nth *round-robin2$br* st))

          (br-lselect (nth *alt-branch$lselect* br))
          (br-select (nth *alt-branch$select* br))
          (br-lselect-buf (nth *alt-branch$lselect-buf* br)))

       (implies (and (booleanp (nth 0 inputs))
                     (queue5$valid-st q5 data-width)
                     (equal br-lselect '(t))
                     (equal (car br-select) t)
                     (equal br-lselect-buf '(nil)))
                (booleanp (queue5$in-act
                           (round-robin2$q5-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue5$in-act
                                        alt-branch$act1
                                        round-robin2$q5-inputs
                                        round-robin2$br-inputs)))
     :rule-classes :type-prescription))

  (local
   (defthm round-robin2$rewrite-to-q5-in-act-1
     (b* ((q5 (nth *round-robin2$q5* st))
          (br (nth *round-robin2$br* st))

          (br-lselect (nth *alt-branch$lselect* br))
          (br-select (nth *alt-branch$select* br))
          (br-lselect-buf (nth *alt-branch$lselect-buf* br)))

       (implies (and (booleanp x)
                     (equal x (nth 0 inputs))
                     (queue5$valid-st q5 data-width)
                     (equal br-lselect '(t))
                     (equal (car br-select) t)
                     (equal br-lselect-buf '(nil)))
                (equal (joint-act
                        x
                        (queue5$ready-in- q5)
                        (car (nthcdr (+ *round-robin2$go-branch-offset*
                                        data-width)
                                     inputs)))
                       (queue5$in-act
                        (round-robin2$q5-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue5$valid-st=>natp-data-width
                                        queue5$in-act
                                        alt-branch$act1
                                        round-robin2$q5-inputs
                                        round-robin2$br-inputs)))))

  (local
   (defthm round-robin2$rewrite-to-q5-in-act-2
     (b* ((q5 (nth *round-robin2$q5* st))
          (br (nth *round-robin2$br* st))

          (br-lselect (nth *alt-branch$lselect* br))
          (br-select (nth *alt-branch$select* br))
          (br-lselect-buf (nth *alt-branch$lselect-buf* br)))

       (implies (and (equal (nth 0 inputs) t)
                     (queue5$valid-st q5 data-width)
                     (equal br-lselect '(t))
                     (booleanp (car br-select))
                     (car br-select)
                     (not (queue5$ready-in- q5))
                     (equal br-lselect-buf '(nil)))
                (equal (f-bool
                        (car (nthcdr (+ *round-robin2$go-branch-offset*
                                        data-width)
                                     inputs)))
                       (queue5$in-act
                        (round-robin2$q5-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue5$valid-st=>natp-data-width
                                        queue5$in-act
                                        alt-branch$act1
                                        round-robin2$q5-inputs
                                        round-robin2$br-inputs)))))

  (local
   (defthm booleanp-round-robin2$q5-out-act
     (b* ((q4 (nth *round-robin2$q4* st))
          (q5 (nth *round-robin2$q5* st))
          (me (nth *round-robin2$me* st))

          (me-lselect (nth *alt-merge$lselect* me))
          (me-select (nth *alt-merge$select* me))
          (me-lselect-buf (nth *alt-merge$lselect-buf* me)))

       (implies (and (booleanp (nth 1 inputs))
                     (queue4$valid-st q4 data-width)
                     (queue5$valid-st q5 data-width)
                     (equal me-lselect '(t))
                     (equal (car me-select) t)
                     (equal me-lselect-buf '(nil)))
                (booleanp (queue5$out-act
                           (round-robin2$q5-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue5$out-act
                                        alt-merge$act1
                                        round-robin2$q5-inputs
                                        round-robin2$me-inputs)))
     :rule-classes :type-prescription))

  (local
   (defthm round-robin2$rewrite-to-q5-out-act-1
     (b* ((q4 (nth *round-robin2$q4* st))
          (q5 (nth *round-robin2$q5* st))
          (me (nth *round-robin2$me* st))

          (me-lselect (nth *alt-merge$lselect* me))
          (me-select (nth *alt-merge$select* me))
          (me-lselect-buf (nth *alt-merge$lselect-buf* me)))

       (implies (and (booleanp x)
                     (equal x (nth 1 inputs))
                     (queue4$valid-st q4 data-width)
                     (queue5$valid-st q5 data-width)
                     (equal me-lselect '(t))
                     (equal (car me-select) t)
                     (equal me-lselect-buf '(nil)))
                (equal (joint-act
                        (queue5$ready-out q5)
                        x
                        (nth 0 (nthcdr (+ *round-robin2$go-merge-offset*
                                          data-width)
                                       inputs)))
                       (queue5$out-act
                        (round-robin2$q5-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue5$valid-st=>natp-data-width
                                        queue5$out-act
                                        alt-merge$act1
                                        round-robin2$q5-inputs
                                        round-robin2$me-inputs)))))

  (local
   (defthm round-robin2$rewrite-to-q5-out-act-2
     (b* ((q4 (nth *round-robin2$q4* st))
          (q5 (nth *round-robin2$q5* st))
          (me (nth *round-robin2$me* st))

          (me-lselect (nth *alt-merge$lselect* me))
          (me-select (nth *alt-merge$select* me))
          (me-lselect-buf (nth *alt-merge$lselect-buf* me)))

       (implies (and (booleanp x)
                     (equal x (nth 1 inputs))
                     (queue4$valid-st q4 data-width)
                     (queue5$valid-st q5 data-width)
                     (equal me-lselect '(t))
                     (queue5$ready-out q5)
                     (equal me-lselect-buf '(nil)))
                (equal (joint-act
                        (car me-select)
                        x
                        (nth 0 (nthcdr (+ *round-robin2$go-merge-offset*
                                          data-width)
                                       inputs)))
                       (queue5$out-act
                        (round-robin2$q5-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        f-and3
                                        queue5$valid-st=>natp-data-width
                                        queue5$out-act
                                        alt-merge$act1
                                        round-robin2$q5-inputs
                                        round-robin2$me-inputs)))))

  (local
   (defthm round-robin2$rewrite-to-q5-out-act-3
     (b* ((q4 (nth *round-robin2$q4* st))
          (q5 (nth *round-robin2$q5* st))
          (me (nth *round-robin2$me* st))

          (me-lselect (nth *alt-merge$lselect* me))
          (me-select (nth *alt-merge$select* me))
          (me-lselect-buf (nth *alt-merge$lselect-buf* me)))

       (implies (and (booleanp x)
                     (equal x (nth 1 inputs))
                     (queue4$valid-st q4 data-width)
                     (queue5$valid-st q5 data-width)
                     (equal me-lselect '(t))
                     (booleanp (car me-select))
                     (car me-select)
                     (queue5$ready-out q5)
                     (equal me-lselect-buf '(nil)))
                (equal (joint-act
                        t
                        x
                        (nth 0 (nthcdr (+ *round-robin2$go-merge-offset*
                                          data-width)
                                       inputs)))
                       (queue5$out-act
                        (round-robin2$q5-inputs inputs st data-width)))))
     :hints (("Goal" :in-theory (enable get-field
                                        f-and3
                                        queue5$valid-st=>natp-data-width
                                        queue5$out-act
                                        alt-merge$act1
                                        round-robin2$q5-inputs
                                        round-robin2$me-inputs)))))

  (defthm round-robin2$inv-preserved
    (implies (and (round-robin2$input-format inputs data-width)
                  (round-robin2$valid-st st data-width)
                  (round-robin2$inv st))
             (round-robin2$inv (round-robin2$step inputs st data-width)))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              queue4$valid-st=>natp-data-width
                              queue4$extracted-step
                              queue5$extracted-step
                              round-robin2$input-format
                              round-robin2$valid-st
                              round-robin2$inv
                              round-robin2$step
                              round-robin2$in-act
                              round-robin2$out-act
                              round-robin2$br-inputs
                              round-robin2$me-inputs
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

;; The extracted next-state function for RR2.  Note that this function avoids
;; exploring the internal computation of RR2.

(defund round-robin2$extracted-step (inputs st data-width)
  (b* ((data-in (round-robin2$data-in inputs data-width))
       (extracted-st (round-robin2$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (round-robin2$out-act inputs st data-width) t)
      (cond
       ((equal (round-robin2$in-act inputs st data-width) t)
        (cons data-in (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (round-robin2$in-act inputs st data-width) t)
          (cons data-in extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm round-robin2$q4-and-q5-get-$data-in-rewrite
     (implies (bvp (round-robin2$data-in inputs data-width))
              (and (equal (queue4$data-in
                           (round-robin2$q4-inputs inputs st data-width)
                           data-width)
                          (round-robin2$data-in inputs data-width))
                   (equal (queue5$data-in
                           (round-robin2$q5-inputs inputs st data-width)
                           data-width)
                          (round-robin2$data-in inputs data-width))))
     :hints (("Goal"
              :in-theory (enable queue4$data-in
                                 queue5$data-in
                                 round-robin2$q4-inputs
                                 round-robin2$q5-inputs)))))

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

  (defthm round-robin2$extracted-step-correct
    (b* ((next-st (round-robin2$step inputs st data-width)))
      (implies (and (round-robin2$input-format inputs data-width)
                    (round-robin2$valid-st st data-width)
                    (round-robin2$inv st))
               (equal (round-robin2$extract next-st)
                      (round-robin2$extracted-step inputs st data-width))))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              queue4$valid-st=>natp-data-width
                              queue4$extracted-step
                              queue5$extracted-step
                              round-robin2$extracted-step
                              round-robin2$input-format
                              round-robin2$valid-st
                              round-robin2$inv
                              round-robin2$step
                              round-robin2$in-act
                              round-robin2$out-act
                              round-robin2$extract
                              round-robin2$br-inputs
                              round-robin2$me-inputs
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

(defun round-robin2$in-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (round-robin2$in-act inputs st data-width) t)
          (append (round-robin2$in-seq
                   (cdr inputs-lst)
                   (round-robin2$step inputs st data-width)
                   data-width
                   (1- n))
                  (list (round-robin2$data-in inputs data-width)))
        (round-robin2$in-seq (cdr inputs-lst)
                             (round-robin2$step inputs st data-width)
                             data-width
                             (1- n))))))

;; Extract the valid output sequence

(defun round-robin2$out-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (round-robin2$out-act inputs st data-width) t)
          (append (round-robin2$out-seq
                   (cdr inputs-lst)
                   (round-robin2$step inputs st data-width)
                   data-width
                   (1- n))
                  (list (round-robin2$data-out st)))
        (round-robin2$out-seq (cdr inputs-lst)
                              (round-robin2$step inputs st data-width)
                              data-width
                              (1- n))))))

;; Input-output sequence simulator

(defund round-robin2$in-out-seq-sim (data-width n state)
  (declare (xargs :guard (and (natp data-width)
                              (natp n))
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals (round-robin2$ins-len data-width))
       ((mv inputs-lst state)
        (signal-vals-gen num-signals n state nil))
       (full '(t))
       (empty '(nil))
       (invalid-data (make-list data-width :initial-element '(x)))
       (q4 (list empty invalid-data
                 empty invalid-data
                 empty invalid-data
                 empty invalid-data))
       (q5 (list empty invalid-data
                 empty invalid-data
                 empty invalid-data
                 empty invalid-data
                 empty invalid-data))
       (br (list full '(nil)
                 empty '(x)))
       (me (list full '(nil)
                 empty '(x)))
       (st (list q4 q5 br me)))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-lst
                   (round-robin2$in-seq inputs-lst st data-width n))))
      (list (cons 'out-seq
                  (v-to-nat-lst
                   (round-robin2$out-seq inputs-lst st data-width n)))))
     state)))

;; Prove that round-robin2$valid-st is an invariant.

(defthm round-robin2$valid-st-preserved
  (implies (and (round-robin2$input-format inputs data-width)
                (round-robin2$valid-st st data-width))
           (round-robin2$valid-st
            (round-robin2$step inputs st data-width)
            data-width))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            round-robin2$valid-st
                            round-robin2$step)
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
                          (len (queue4$extract st)))
                   (equal m (1- (len (queue4$extract st))))
                   (equal n (+ -1
                               (len l1)
                               (len (queue4$extract st)))))
              (equal (nth m (queue4$extract st))
                     (nth n (interleave l1 (queue4$extract st)))))
     :hints (("Goal" :use (:instance nth-interleave-1
                                     (l2 (queue4$extract st)))))))

  (local
   (defthm nth-interleave-1-instance-2
     (implies (and (equal (len l1)
                          (len (queue5$extract st)))
                   (equal m (1- (len (queue5$extract st))))
                   (equal n (+ -1
                               (len l1)
                               (len (queue5$extract st)))))
              (equal (nth m (queue5$extract st))
                     (nth n (interleave l1 (queue5$extract st)))))
     :hints (("Goal" :use (:instance nth-interleave-1
                                     (l2 (queue5$extract st)))))))

  (local
   (defthm nth-interleave-2-instance-1
     (implies (and (equal (len (queue4$extract st))
                          (1+ (len l2)))
                   (equal m (1- (len (queue4$extract st))))
                   (equal n (+ -1
                               (len (queue4$extract st))
                               (len l2))))
              (equal (nth m (queue4$extract st))
                     (nth n (interleave (queue4$extract st)
                                        l2))))
     :hints (("Goal" :use (:instance nth-interleave-2
                                     (l1 (queue4$extract st)))))))

  (local
   (defthm nth-interleave-2-instance-2
     (implies (and (equal (len (queue5$extract st))
                          (1+ (len l2)))
                   (equal m (1- (len (queue5$extract st))))
                   (equal n (+ -1
                               (len (queue5$extract st))
                               (len l2))))
              (equal (nth m (queue5$extract st))
                     (nth n (interleave (queue5$extract st)
                                        l2))))
     :hints (("Goal" :use (:instance nth-interleave-2
                                     (l1 (queue5$extract st)))))))

  (defthm round-robin2$extract-lemma
    (implies (and (round-robin2$input-format inputs data-width)
                  (round-robin2$valid-st st data-width)
                  (round-robin2$inv st)
                  (equal n (1- (len (round-robin2$extract st))))
                  (round-robin2$out-act inputs st data-width))
             (equal (append (take n (round-robin2$extract st))
                            (list (round-robin2$data-out st)))
                    (round-robin2$extract st)))
    :hints (("Goal"
             :do-not-induct t
             :use round-robin2$valid-st=>natp-data-width
             :in-theory (e/d (get-field
                              f-and3
                              queue4$data-out-rewrite
                              queue5$data-out-rewrite
                              round-robin2$input-format
                              round-robin2$valid-st
                              round-robin2$inv
                              round-robin2$extract
                              round-robin2$out-act
                              round-robin2$data-out
                              round-robin2$me-inputs
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

(in-out-stream-lemma round-robin2 :inv t)

