;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "arb-merge2")
(include-book "../fifo/queue9-l")
(include-book "../fifo/queue11-l")

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "std/lists/sets" :dir :system))

(local (in-theory (disable nth 3v-fix)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of INTERL-LL
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of INTERL-LL
;;
;; Construct a DE module generator for circuits performing the
;; first-come-first-served arbitrated merge using the link-joint model.  These
;; circuits consist of a 9-link queue and a 11-link queue connected to the two
;; input ports of an arbitrated merge.  INTERL-LL is designed as a left
;; half-complex link.

(defconst *interl-ll$select-num* *arb-merge$select-num*)
(defconst *interl-ll$prim-go-num* 2)
(defconst *interl-ll$go-num* (+ *interl-ll$prim-go-num*
                                *queue9-l$go-num*
                                *queue11-l$go-num*
                                *arb-merge$go-num*))

(defun interl-ll$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 3 (* 2 (mbe :logic (nfix data-size)
                 :exec  data-size))))

(defun interl-ll$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (interl-ll$data-ins-len data-size)
     *interl-ll$select-num*
     *interl-ll$go-num*))

;; DE module generator of INTERL-LL

(module-generator
 interl-ll* (data-size)
 (si 'interl-ll data-size)
 (list* 'in0-act 'in1-act 'empty-out-
        (append (sis 'data0-in 0 data-size)
                (sis 'data1-in 0 data-size)
                (cons 'select (sis 'go 0 *interl-ll$go-num*))))
 (list* 'ready-in0- 'ready-in1- 'out-act
        (sis 'data-out 0 data-size))
 '(q9-l q11-l arb-merge)
 (list
  ;; LINKS
  ;; 9-link queue Q9-L
  (list 'q9-l
        (list* 'ready-in0- 'q9-l-ready-out
               (sis 'q9-l-data-out 0 data-size))
        (si 'queue9-l data-size)
        (list* 'in0-act 'out-act0
               (append (sis 'data0-in 0 data-size)
                       (sis 'go
                            *interl-ll$prim-go-num*
                            *queue9-l$go-num*))))

  ;; 11-link queue Q11-L
  (list 'q11-l
        (list* 'ready-in1- 'q11-l-ready-out
               (sis 'q11-l-data-out 0 data-size))
        (si 'queue11-l data-size)
        (list* 'in1-act 'out-act1
               (append (sis 'data1-in 0 data-size)
                       (sis 'go
                            (+ *interl-ll$prim-go-num*
                               *queue9-l$go-num*)
                            *queue11-l$go-num*))))

  ;; JOINT
  ;; Arb-merge
  (list 'arb-merge
        (list* 'out-act 'out-act0 'out-act1
               (sis 'data-out 0 data-size))
        (si 'arb-merge data-size)
        (list* 'q9-l-ready-out 'q11-l-ready-out 'empty-out-
               (append (sis 'q9-l-data-out 0 data-size)
                       (sis 'q11-l-data-out 0 data-size)
                       (cons 'select
                             (sis 'go
                                  (+ *interl-ll$prim-go-num*
                                     *queue9-l$go-num*
                                     *queue11-l$go-num*)
                                  *arb-merge$go-num*))))))

 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'interl-ll
                           '(q9-l q11-l arb-merge)
                           0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; INTERL-LL.

(defund interl-ll$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (interl-ll* data-size)
        (union$ (queue9-l$netlist data-size)
                (queue11-l$netlist data-size)
                (arb-merge$netlist data-size)
                :test 'equal)))

;; Recognizer for INTERL-LL

(defund interl-ll& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'interl-ll data-size) netlist)))
    (and (equal (assoc (si 'interl-ll data-size) netlist)
                (interl-ll* data-size))
         (joint-cntl& subnetlist)
         (queue9-l& subnetlist data-size)
         (queue11-l& subnetlist data-size)
         (arb-merge& subnetlist data-size))))

;; Sanity check

(local
 (defthmd check-interl-ll$netlist-64
   (and (net-syntax-okp (interl-ll$netlist 64))
        (net-arity-okp (interl-ll$netlist 64))
        (interl-ll& (interl-ll$netlist 64) 64))))

;; Constraints on the state of INTERL-LL

(defund interl-ll$st-format (st data-size)
  (b* ((q9-l (nth *interl-ll$q9-l* st))
       (q11-l (nth *interl-ll$q11-l* st))
       (arb-merge (nth *interl-ll$arb-merge* st)))
    (and (< 0 data-size)
         (queue9-l$st-format q9-l data-size)
         (queue11-l$st-format q11-l data-size)
         (arb-merge$st-format arb-merge))))

(defthm interl-ll$st-format=>constraint
  (implies (interl-ll$st-format st data-size)
           (posp data-size))
  :hints (("Goal" :in-theory (enable interl-ll$st-format)))
  :rule-classes :forward-chaining)

(defund interl-ll$valid-st (st data-size)
  (b* ((q9-l (nth *interl-ll$q9-l* st))
       (q11-l (nth *interl-ll$q11-l* st))
       (arb-merge (nth *interl-ll$arb-merge* st)))
    (and (< 0 data-size)
         (queue9-l$valid-st q9-l data-size)
         (queue11-l$valid-st q11-l data-size)
         (arb-merge$valid-st arb-merge))))

(defthmd interl-ll$valid-st=>constraint
  (implies (interl-ll$valid-st st data-size)
           (posp data-size))
  :hints (("Goal" :in-theory (enable queue9-l$valid-st=>constraint
                                     interl-ll$valid-st)))
  :rule-classes :forward-chaining)

(defthmd interl-ll$valid-st=>st-format
  (implies (interl-ll$valid-st st data-size)
           (interl-ll$st-format st data-size))
  :hints (("Goal" :in-theory (e/d (queue9-l$valid-st=>st-format
                                   queue11-l$valid-st=>st-format
                                   arb-merge$valid-st=>st-format
                                   interl-ll$st-format
                                   interl-ll$valid-st)
                                  ()))))

;; Extract the input and output signals for INTERL-LL

(progn
  ;; Extract the "in0-act" signal

  (defund interl-ll$in0-act (inputs)
    (nth 0 inputs))

  ;; Extract the "in1-act" signal

  (defund interl-ll$in1-act (inputs)
    (nth 1 inputs))

  ;; Extract the 1st input data item

  (defun interl-ll$data0-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (mbe :logic (nfix data-size)
               :exec  data-size)
          (nthcdr 3 inputs)))

  (defthm len-interl-ll$data0-in
    (equal (len (interl-ll$data0-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable interl-ll$data0-in))

  ;; Extract the 2nd input data item

  (defun interl-ll$data1-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (b* ((size (mbe :logic (nfix data-size)
                     :exec  data-size)))
      (take size
            (nthcdr (+ 3 size) inputs))))

  (defthm len-interl-ll$data1-in
    (equal (len (interl-ll$data1-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable interl-ll$data1-in))

  ;; Extract the "ready-in0-" signal

  (defund interl-ll$ready-in0- (st)
    (b* ((q9-l (nth *interl-ll$q9-l* st)))
      (queue9-l$ready-in- q9-l)))

  (defthm booleanp-interl-ll$ready-in0-
    (implies (interl-ll$valid-st st data-size)
             (booleanp (interl-ll$ready-in0- st)))
    :hints (("Goal" :in-theory (enable interl-ll$valid-st
                                       interl-ll$ready-in0-)))
    :rule-classes (:rewrite :type-prescription))

  ;; Extract the "ready-in1-" signal

  (defund interl-ll$ready-in1- (st)
    (b* ((q11-l (nth *interl-ll$q11-l* st)))
      (queue11-l$ready-in- q11-l)))

  (defthm booleanp-interl-ll$ready-in1-
    (implies (interl-ll$valid-st st data-size)
             (booleanp (interl-ll$ready-in1- st)))
    :hints (("Goal" :in-theory (enable interl-ll$valid-st
                                       interl-ll$ready-in1-)))
    :rule-classes (:rewrite :type-prescription))

  ;; Extract the inputs for joint ARB-MERGE

  (defund interl-ll$arb-merge-inputs (inputs st data-size)
    (b* ((empty-out- (nth 2 inputs))
         (select     (nth (interl-ll$data-ins-len data-size) inputs))
         (go-signals (nthcdr (+ (interl-ll$data-ins-len data-size)
                                *interl-ll$select-num*)
                             inputs))

         (arb-merge-go-signals (take *arb-merge$go-num*
                                     (nthcdr (+ *interl-ll$prim-go-num*
                                                *queue9-l$go-num*
                                                *queue11-l$go-num*)
                                             go-signals)))

         (q9-l (nth *interl-ll$q9-l* st))
         (q11-l (nth *interl-ll$q11-l* st))

         (q9-l-ready-out (queue9-l$ready-out q9-l))
         (q9-l-data-out (queue9-l$data-out q9-l))
         (q11-l-ready-out (queue11-l$ready-out q11-l))
         (q11-l-data-out (queue11-l$data-out q11-l)))
      (list* q9-l-ready-out q11-l-ready-out empty-out-
             (append q9-l-data-out q11-l-data-out
                     (cons select arb-merge-go-signals)))))

  ;; Extract the "out-act0" signal

  (defund interl-ll$out-act0 (inputs st data-size)
    (b* ((arb-merge-inputs (interl-ll$arb-merge-inputs inputs st data-size))
         (arb-merge (nth *interl-ll$arb-merge* st)))
      (arb-merge$act0 arb-merge-inputs arb-merge data-size)))

  (defthm interl-ll$out-act0-inactive
    (implies (equal (nth 2 inputs) t)
             (not (interl-ll$out-act0 inputs st data-size)))
    :hints (("Goal" :in-theory (enable interl-ll$arb-merge-inputs
                                       interl-ll$out-act0))))

  ;; Extract the "out-act1" signal

  (defund interl-ll$out-act1 (inputs st data-size)
    (b* ((arb-merge-inputs (interl-ll$arb-merge-inputs inputs st data-size))
         (arb-merge (nth *interl-ll$arb-merge* st)))
      (arb-merge$act1 arb-merge-inputs arb-merge data-size)))

  (defthm interl-ll$out-act1-inactive
    (implies (equal (nth 2 inputs) t)
             (not (interl-ll$out-act1 inputs st data-size)))
    :hints (("Goal" :in-theory (enable interl-ll$arb-merge-inputs
                                       interl-ll$out-act1))))

  (defthm interl-ll$out-act-mutually-exclusive
    (implies (and (interl-ll$valid-st st data-size)
                  (interl-ll$out-act0 inputs st data-size))
             (not (interl-ll$out-act1 inputs st data-size)))
    :hints (("Goal" :in-theory (enable interl-ll$valid-st
                                       interl-ll$arb-merge-inputs
                                       interl-ll$out-act0
                                       interl-ll$out-act1))))

  ;; Extract the "out-act" signal

  (defund interl-ll$out-act (inputs st data-size)
    (f-or (interl-ll$out-act0 inputs st data-size)
          (interl-ll$out-act1 inputs st data-size)))

  (defthm interl-ll$out-act-inactive
    (implies (equal (nth 2 inputs) t)
             (not (interl-ll$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable interl-ll$out-act))))

  ;; Extract the inputs for link Q9-L

  (defund interl-ll$q9-l-inputs (inputs st data-size)
    (b* ((in0-act (interl-ll$in0-act inputs))
         (data0-in (interl-ll$data0-in inputs data-size))
         (go-signals (nthcdr (+ (interl-ll$data-ins-len data-size)
                                *interl-ll$select-num*)
                             inputs))

         (q9-l-go-signals (take *queue9-l$go-num*
                                (nthcdr *interl-ll$prim-go-num*
                                        go-signals)))

         (arb-merge (nth *interl-ll$arb-merge* st))

         (arb-merge-inputs (interl-ll$arb-merge-inputs inputs st data-size))
         (out-act0 (arb-merge$act0 arb-merge-inputs arb-merge data-size)))

      (list* in0-act out-act0
             (append data0-in q9-l-go-signals))))

  ;; Extract the inputs for link Q11-L

  (defund interl-ll$q11-l-inputs (inputs st data-size)
    (b* ((in1-act (interl-ll$in1-act inputs))
         (data1-in (interl-ll$data1-in inputs data-size))
         (go-signals (nthcdr (+ (interl-ll$data-ins-len data-size)
                                *interl-ll$select-num*)
                             inputs))

         (q11-l-go-signals (take *queue11-l$go-num*
                                 (nthcdr (+ *interl-ll$prim-go-num*
                                            *queue9-l$go-num*)
                                         go-signals)))

         (arb-merge (nth *interl-ll$arb-merge* st))

         (arb-merge-inputs (interl-ll$arb-merge-inputs inputs st data-size))
         (out-act1 (arb-merge$act1 arb-merge-inputs arb-merge data-size)))

      (list* in1-act out-act1
             (append data1-in q11-l-go-signals))))

  ;; Extract the output data

  (defund interl-ll$data-out (inputs st data-size)
    (b* ((arb-merge-inputs (interl-ll$arb-merge-inputs inputs st data-size))
         (arb-merge (nth *interl-ll$arb-merge* st)))
      (arb-merge$data-out arb-merge-inputs arb-merge data-size)))

  (defthm len-interl-ll$data-out-1
    (implies (interl-ll$st-format st data-size)
             (equal (len (interl-ll$data-out inputs st data-size))
                    data-size))
    :hints (("Goal" :in-theory (enable interl-ll$st-format
                                       interl-ll$data-out))))

  (defthm len-interl-ll$data-out-2
    (implies (interl-ll$valid-st st data-size)
             (equal (len (interl-ll$data-out inputs st data-size))
                    data-size))
    :hints (("Goal" :in-theory (enable queue9-l$valid-st=>constraint
                                       interl-ll$valid-st
                                       interl-ll$data-out))))

  (defun interl-ll$outputs (inputs st data-size)
    (list* (interl-ll$ready-in0- st)
           (interl-ll$ready-in1- st)
           (interl-ll$out-act inputs st data-size)
           (interl-ll$data-out inputs st data-size)))
  )

;; The value lemma for INTERL-LL

(defthm interl-ll$value
  (b* ((inputs (list* in0-act in1-act empty-out-
                      (append data0-in data1-in
                              (cons select go-signals)))))
    (implies (and (interl-ll& netlist data-size)
                  (true-listp data0-in)
                  (equal (len data0-in) data-size)
                  (true-listp data1-in)
                  (equal (len data1-in) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *interl-ll$go-num*)
                  (interl-ll$st-format st data-size))
             (equal (se (si 'interl-ll data-size) inputs st netlist)
                    (interl-ll$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'interl-ll data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            interl-ll&
                            interl-ll*$destructure
                            interl-ll$st-format
                            arb-merge$act
                            interl-ll$arb-merge-inputs
                            interl-ll$ready-in0-
                            interl-ll$ready-in1-
                            interl-ll$in0-act
                            interl-ll$in1-act
                            interl-ll$out-act0
                            interl-ll$out-act1
                            interl-ll$out-act
                            interl-ll$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of INTERL-LL.

(defun interl-ll$step (inputs st data-size)
  (b* ((q9-l        (nth *interl-ll$q9-l* st))
       (q11-l       (nth *interl-ll$q11-l* st))
       (arb-merge (nth *interl-ll$arb-merge* st))

       (q9-l-inputs (interl-ll$q9-l-inputs inputs st data-size))
       (q11-l-inputs (interl-ll$q11-l-inputs inputs st data-size))
       (arb-merge-inputs (interl-ll$arb-merge-inputs inputs st data-size)))
    (list
      ;; Q9-L
     (queue9-l$step q9-l-inputs q9-l data-size)
     ;; Q11-L
     (queue11-l$step q11-l-inputs q11-l data-size)
     ;; Joint arb-merge
     (arb-merge$step arb-merge-inputs arb-merge data-size))))

;; The state lemma for INTERL-LL

(defthm interl-ll$state
  (b* ((inputs (list* in0-act in1-act empty-out-
                      (append data0-in data1-in
                              (cons select go-signals)))))
    (implies (and (interl-ll& netlist data-size)
                  (true-listp data0-in)
                  (equal (len data0-in) data-size)
                  (true-listp data1-in)
                  (equal (len data1-in) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *interl-ll$go-num*)
                  (interl-ll$st-format st data-size))
             (equal (de (si 'interl-ll data-size) inputs st netlist)
                    (interl-ll$step inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'interl-ll data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            interl-ll&
                            interl-ll*$destructure
                            interl-ll$st-format
                            interl-ll$data0-in
                            interl-ll$data1-in
                            interl-ll$q9-l-inputs
                            interl-ll$q11-l-inputs
                            interl-ll$arb-merge-inputs
                            interl-ll$in0-act
                            interl-ll$in1-act)
                           (de-module-disabled-rules)))))

(in-theory (disable interl-ll$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund interl-ll$input-format (inputs st data-size)
  (b* ((in0-act    (interl-ll$in0-act inputs))
       (in1-act    (interl-ll$in1-act inputs))
       (empty-out- (nth 2 inputs))
       (data0-in   (interl-ll$data0-in inputs data-size))
       (data1-in   (interl-ll$data1-in inputs data-size))
       (select     (nth (interl-ll$data-ins-len data-size) inputs))
       (go-signals (nthcdr (+ (interl-ll$data-ins-len data-size)
                              *interl-ll$select-num*)
                           inputs))

       (ready-in0- (interl-ll$ready-in0- st))
       (ready-in1- (interl-ll$ready-in1- st)))
    (and
     (if ready-in0-
         (not in0-act)
       (booleanp in0-act))
     (if ready-in1-
         (not in1-act)
       (booleanp in1-act))
     (booleanp empty-out-)
     (or (not in0-act) (bvp data0-in))
     (or (not in1-act) (bvp data1-in))
     (true-listp go-signals)
     (= (len go-signals) *interl-ll$go-num*)
     (equal inputs
            (list* in0-act in1-act empty-out-
                   (append data0-in data1-in (cons select go-signals)))))))

(local (in-theory (enable booleanp-car-of-bv)))

(local
 (defthm booleanp-cadr-of-bv
   (implies (bvp x)
            (booleanp (cadr x)))
   :hints (("Goal" :in-theory (enable bvp)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm booleanp-caddr-of-bv
   (implies (bvp x)
            (booleanp (caddr x)))
   :hints (("Goal" :in-theory (enable bvp)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm interl-ll$input-format=>q9-l$input-format
   (implies (and (interl-ll$input-format inputs st data-size)
                 (interl-ll$valid-st st data-size))
            (queue9-l$input-format
             (interl-ll$q9-l-inputs inputs st data-size)
             (nth *interl-ll$q9-l* st)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (f-and4
                             f-and5
                             queue9-l$input-format
                             queue9-l$in-act
                             queue9-l$out-act
                             queue9-l$data-in
                             arb-merge$valid-st
                             arb-merge$act0
                             interl-ll$input-format
                             interl-ll$valid-st
                             interl-ll$ready-in0-
                             interl-ll$q9-l-inputs
                             interl-ll$arb-merge-inputs
                             interl-ll$in0-act)
                            (nfix
                             link$st-format))))))

(local
 (defthm interl-ll$input-format=>q11-l$input-format
   (implies (and (interl-ll$input-format inputs st data-size)
                 (interl-ll$valid-st st data-size))
            (queue11-l$input-format
             (interl-ll$q11-l-inputs inputs st data-size)
             (nth *interl-ll$q11-l* st)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (f-and4
                             f-and5
                             queue11-l$input-format
                             queue11-l$in-act
                             queue11-l$out-act
                             queue11-l$data-in
                             arb-merge$valid-st
                             arb-merge$act1
                             interl-ll$input-format
                             interl-ll$valid-st
                             interl-ll$ready-in1-
                             interl-ll$q11-l-inputs
                             interl-ll$arb-merge-inputs
                             interl-ll$in1-act)
                            (nfix
                             link$st-format))))))

(local
 (defthm interl-ll$input-format=>arb-merge$input-format
   (implies (and (interl-ll$input-format inputs st data-size)
                 (interl-ll$valid-st st data-size))
            (arb-merge$input-format
             (interl-ll$arb-merge-inputs inputs st data-size)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (open-nth
                             queue9-l$valid-st=>constraint
                             arb-merge$input-format
                             arb-merge$data0-in
                             arb-merge$data1-in
                             interl-ll$input-format
                             interl-ll$valid-st
                             interl-ll$arb-merge-inputs)
                            ())))))

(defthm booleanp-interl-ll$in0-act
  (implies (interl-ll$input-format inputs st data-size)
           (booleanp (interl-ll$in0-act inputs)))
  :hints (("Goal" :in-theory (enable interl-ll$input-format
                                     interl-ll$in0-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-interl-ll$in1-act
  (implies (interl-ll$input-format inputs st data-size)
           (booleanp (interl-ll$in1-act inputs)))
  :hints (("Goal" :in-theory (enable interl-ll$input-format
                                     interl-ll$in1-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-interl-ll$out0-act
  (implies (and (interl-ll$input-format inputs st data-size)
                (interl-ll$valid-st st data-size))
           (booleanp (interl-ll$out-act0 inputs st data-size)))
  :hints (("Goal" :in-theory (enable f-and4
                                     f-and5
                                     arb-merge$valid-st
                                     arb-merge$act0
                                     interl-ll$input-format
                                     interl-ll$valid-st
                                     interl-ll$arb-merge-inputs
                                     interl-ll$out-act0
                                     interl-ll$out-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-interl-ll$out1-act
  (implies (and (interl-ll$input-format inputs st data-size)
                (interl-ll$valid-st st data-size))
           (booleanp (interl-ll$out-act1 inputs st data-size)))
  :hints (("Goal" :in-theory (enable f-and4
                                     f-and5
                                     arb-merge$valid-st
                                     arb-merge$act1
                                     interl-ll$input-format
                                     interl-ll$valid-st
                                     interl-ll$arb-merge-inputs
                                     interl-ll$out-act1
                                     interl-ll$out-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-interl-ll$out-act
  (implies (and (interl-ll$input-format inputs st data-size)
                (interl-ll$valid-st st data-size))
           (booleanp (interl-ll$out-act inputs st data-size)))
  :hints (("Goal" :in-theory (enable interl-ll$out-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-interl-ll$data-out
  (implies (and (interl-ll$input-format inputs st data-size)
                (interl-ll$valid-st st data-size)
                (interl-ll$out-act inputs st data-size))
           (bvp (interl-ll$data-out inputs st data-size)))
  :hints (("Goal"
           :in-theory (enable f-and4
                              f-and5
                              arb-merge$valid-st
                              arb-merge$act0
                              arb-merge$act1
                              arb-merge$data0-in
                              arb-merge$data1-in
                              arb-merge$data-out
                              interl-ll$input-format
                              interl-ll$valid-st
                              interl-ll$out-act0
                              interl-ll$out-act1
                              interl-ll$out-act
                              interl-ll$arb-merge-inputs
                              interl-ll$data-out))))

(simulate-lemma interl-ll :clink t)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction functions for INTERL-LL

(defund interl-ll$extract0 (st)
  (b* ((q9-l (nth *interl-ll$q9-l* st)))
    (queue9-l$extract q9-l)))

(defund interl-ll$extract1 (st)
  (b* ((q11-l (nth *interl-ll$q11-l* st)))
    (queue11-l$extract q11-l)))

(defthm interl-ll$extract0-not-empty
  (implies (and (interl-ll$out-act0 inputs st data-size)
                (interl-ll$valid-st st data-size))
           (< 0 (len (interl-ll$extract0 st))))
  :hints (("Goal"
           :in-theory (e/d (f-and
                            f-and4
                            f-and5
                            3v-fix
                            arb-merge$valid-st
                            arb-merge$act0
                            interl-ll$arb-merge-inputs
                            interl-ll$valid-st
                            interl-ll$extract0
                            interl-ll$out-act0)
                           ())))
  :rule-classes :linear)

(defthm interl-ll$extract1-not-empty
  (implies (and (interl-ll$out-act1 inputs st data-size)
                (interl-ll$valid-st st data-size))
           (< 0 (len (interl-ll$extract1 st))))
  :hints (("Goal"
           :in-theory (e/d (f-and
                            f-and4
                            f-and5
                            3v-fix
                            arb-merge$valid-st
                            arb-merge$act1
                            interl-ll$arb-merge-inputs
                            interl-ll$valid-st
                            interl-ll$extract1
                            interl-ll$out-act1)
                           ())))
  :rule-classes :linear)

;; The extracted next-state functions for INTERL-LL.  Note that these functions
;; avoid exploring the internal computation of INTERL-LL.

(defund interl-ll$extracted0-step (inputs st data-size)
  (b* ((data (interl-ll$data0-in inputs data-size))
       (extracted-st (interl-ll$extract0 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (interl-ll$out-act0 inputs st data-size) t)
      (cond
       ((equal (interl-ll$in0-act inputs) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (interl-ll$in0-act inputs) t)
          (cons data extracted-st))
         (t extracted-st))))))

(defund interl-ll$extracted1-step (inputs st data-size)
  (b* ((data (interl-ll$data1-in inputs data-size))
       (extracted-st (interl-ll$extract1 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (interl-ll$out-act1 inputs st data-size) t)
      (cond
       ((equal (interl-ll$in1-act inputs) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (interl-ll$in1-act inputs) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm interl-ll$q9-l-data-in-rewrite
     (equal (queue9-l$data-in
             (interl-ll$q9-l-inputs inputs st data-size)
             data-size)
            (interl-ll$data0-in inputs data-size))
     :hints (("Goal"
              :in-theory (enable queue9-l$data-in
                                 interl-ll$data0-in
                                 interl-ll$q9-l-inputs)))))

  (local
   (defthm interl-ll$q11-l-data-in-rewrite
     (equal (queue11-l$data-in
             (interl-ll$q11-l-inputs inputs st data-size)
             data-size)
            (interl-ll$data1-in inputs data-size))
     :hints (("Goal"
              :in-theory (enable queue11-l$data-in
                                 interl-ll$data1-in
                                 interl-ll$q11-l-inputs)))))

  (local
   (defthm interl-ll$q9-l-in-act-rewrite
     (equal (queue9-l$in-act (interl-ll$q9-l-inputs inputs st data-size))
            (interl-ll$in0-act inputs))
     :hints (("Goal" :in-theory (enable queue9-l$in-act
                                        interl-ll$in0-act
                                        interl-ll$q9-l-inputs)))))

  (local
   (defthm interl-ll$q9-l-out-act-rewrite
     (equal (queue9-l$out-act (interl-ll$q9-l-inputs inputs st data-size))
            (interl-ll$out-act0 inputs st data-size))
     :hints (("Goal" :in-theory (enable queue9-l$out-act
                                        interl-ll$out-act0
                                        interl-ll$q9-l-inputs)))))

  (local
   (defthm interl-ll$q11-l-in-act-rewrite
     (equal (queue11-l$in-act (interl-ll$q11-l-inputs inputs st data-size))
            (interl-ll$in1-act inputs))
     :hints (("Goal" :in-theory (enable queue11-l$in-act
                                        interl-ll$in1-act
                                        interl-ll$q11-l-inputs)))))

  (local
   (defthm interl-ll$q11-l-out-act-rewrite
     (equal (queue11-l$out-act (interl-ll$q11-l-inputs inputs st data-size))
            (interl-ll$out-act1 inputs st data-size))
     :hints (("Goal" :in-theory (enable queue11-l$out-act
                                        interl-ll$out-act1
                                        interl-ll$q11-l-inputs)))))

  (defthm interl-ll$extracted-step-correct
    (b* ((next-st (interl-ll$step inputs st data-size)))
      (implies (and (interl-ll$input-format inputs st data-size)
                    (interl-ll$valid-st st data-size))
               (and (equal (interl-ll$extract0 next-st)
                           (interl-ll$extracted0-step inputs st data-size))
                    (equal (interl-ll$extract1 next-st)
                           (interl-ll$extracted1-step inputs st data-size)))))
    :hints (("Goal"
             :in-theory (e/d (queue9-l$extracted-step
                              queue11-l$extracted-step
                              interl-ll$extracted0-step
                              interl-ll$extracted1-step
                              interl-ll$valid-st
                              interl-ll$step
                              interl-ll$extract0
                              interl-ll$extract1)
                             ()))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that interl-ll$valid-st is an invariant.

(defthm interl-ll$valid-st-preserved
  (implies (and (interl-ll$input-format inputs st data-size)
                (interl-ll$valid-st st data-size))
           (interl-ll$valid-st (interl-ll$step inputs st data-size)
                               data-size))
  :hints (("Goal"
           :in-theory (e/d (interl-ll$valid-st
                            interl-ll$step)
                           ()))))

(encapsulate
  ()

  (local
   (defthm interl-ll$data-out-rewrite-1
     (implies (and (interl-ll$valid-st st data-size)
                   (interl-ll$out-act0 inputs st data-size))
              (equal (interl-ll$data-out inputs st data-size)
                     (queue9-l$data-out (nth *interl-ll$q9-l* st))))
     :hints (("Goal"
              :in-theory (enable f-and4
                                 f-and5
                                 queue9-l$valid-st=>constraint
                                 arb-merge$valid-st
                                 arb-merge$act0
                                 arb-merge$act1
                                 arb-merge$data0-in
                                 arb-merge$data-out
                                 interl-ll$valid-st
                                 interl-ll$arb-merge-inputs
                                 interl-ll$out-act0
                                 interl-ll$data-out)))))

  (local
   (defthm interl-ll$data-out-rewrite-2
     (implies (and (interl-ll$input-format inputs st data-size)
                   (interl-ll$valid-st st data-size)
                   (interl-ll$out-act1 inputs st data-size))
              (equal (interl-ll$data-out inputs st data-size)
                     (queue11-l$data-out (nth *interl-ll$q11-l* st))))
     :hints (("Goal"
              :in-theory (enable f-and4
                                 f-and5
                                 queue11-l$valid-st=>constraint
                                 arb-merge$valid-st
                                 arb-merge$act0
                                 arb-merge$act1
                                 arb-merge$data1-in
                                 arb-merge$data-out
                                 interl-ll$input-format
                                 interl-ll$valid-st
                                 interl-ll$arb-merge-inputs
                                 interl-ll$out-act1
                                 interl-ll$data-out)))))

  (local
   (defthm interl-ll$out-act0-rewrite
     (equal (interl-ll$out-act0 inputs st data-size)
            (queue9-l$out-act (interl-ll$q9-l-inputs inputs st data-size)))
     :hints (("Goal" :in-theory (enable queue9-l$out-act
                                        interl-ll$out-act0
                                        interl-ll$q9-l-inputs)))))

  (local
   (defthm interl-ll$out-act1-rewrite
     (equal (interl-ll$out-act1 inputs st data-size)
            (queue11-l$out-act (interl-ll$q11-l-inputs inputs st data-size)))
     :hints (("Goal" :in-theory (enable queue11-l$out-act
                                        interl-ll$out-act1
                                        interl-ll$q11-l-inputs)))))

  (defthm interl-ll$extract0-lemma
    (implies (and (interl-ll$input-format inputs st data-size)
                  (interl-ll$valid-st st data-size)
                  (interl-ll$out-act0 inputs st data-size))
             (equal (list (interl-ll$data-out inputs st data-size))
                    (nthcdr (1- (len (interl-ll$extract0 st)))
                            (interl-ll$extract0 st))))
    :hints (("Goal"
             :use interl-ll$input-format=>q9-l$input-format
             :in-theory (e/d (interl-ll$valid-st
                              interl-ll$extract0)
                             (interl-ll$input-format=>q9-l$input-format)))))

  (defthm interl-ll$extract1-lemma
    (implies (and (interl-ll$input-format inputs st data-size)
                  (interl-ll$valid-st st data-size)
                  (interl-ll$out-act1 inputs st data-size))
             (equal (list (interl-ll$data-out inputs st data-size))
                    (nthcdr (1- (len (interl-ll$extract1 st)))
                            (interl-ll$extract1 st))))
    :hints (("Goal"
             :use interl-ll$input-format=>q11-l$input-format
             :in-theory (e/d (interl-ll$valid-st
                              interl-ll$extract1)
                             (interl-ll$input-format=>q11-l$input-format)))))
  )

;; Extract the accepted input sequences

(seq-gen interl-ll in0 in0-act -1
         (interl-ll$data0-in inputs data-size)
         :clink t)

(seq-gen interl-ll in1 in1-act -1
         (interl-ll$data1-in inputs data-size)
         :clink t)

;; Extract the valid output sequence

(seq-gen interl-ll out out-act 2
         (interl-ll$data-out inputs st data-size)
         :netlist-data (nthcdr 3 outputs)
         :partial-clink t)

;; The multi-step input-output relationship

;; Let in0-seq and in1-seq represent two input sequences connected to Q9-L and
;; Q11-L, respectively.  We might expect the output sequence is any
;; interleaving of in0-seq and in1-seq.  More generally, our formalization also
;; takes into account that the initial state may contain some valid data and
;; there can be some valid data remaining in the final state.  We then prove
;; that for any interleaving x of two data sequences remaining in the final
;; state, the concatenation of x and the output sequence must be a member of
;; (seq0 x seq1); where seq0 is the concatenation of in0-seq and the data
;; sequence in Q9-L at the intial state, and seq1 is the concatenation of
;; in1-seq and the data sequence in Q11-L at the intial state.

(progn
  (defthm member-append-interleave-1-instance
    (implies (and (member (append a b) (interleave y z))
                  (equal y++x1 (append y x1))
                  (true-listp x1)
                  (true-listp z))
             (member (append a b x1)
                     (interleave y++x1 z)))
    :hints (("Goal"
             :use (:instance member-append-interleave-1
                             (x (append a b))))))

  (defthm member-append-interleave-2-instance
    (implies (and (member (append a b) (interleave y z))
                  (equal z++x1 (append z x1))
                  (true-listp x1)
                  (true-listp y))
             (member (append a b x1)
                     (interleave y z++x1)))
    :hints (("Goal"
             :use (:instance member-append-interleave-2
                             (x (append a b))))))

  (defthmd interl-ll$dataflow-correct
    (b* ((extracted0-st (interl-ll$extract0 st))
         (extracted1-st (interl-ll$extract1 st))
         (final-st (interl-ll$run inputs-seq st data-size n))
         (final-extracted0-st (interl-ll$extract0 final-st))
         (final-extracted1-st (interl-ll$extract1 final-st)))
      (implies
       (and (interl-ll$input-format-n inputs-seq st data-size n)
            (interl-ll$valid-st st data-size)
            (member x (interleave final-extracted0-st final-extracted1-st)))
       (member
        (append x (interl-ll$out-seq inputs-seq st data-size n))
        (interleave (append (interl-ll$in0-seq inputs-seq st data-size n)
                            extracted0-st)
                    (append (interl-ll$in1-seq inputs-seq st data-size n)
                            extracted1-st)))))
    :hints (("Goal" :in-theory (enable member-of-true-list-list-is-true-list
                                       interl-ll$out-act
                                       interl-ll$extracted0-step
                                       interl-ll$extracted1-step))))

  (defthmd interl-ll$functionally-correct
    (b* ((extracted0-st (interl-ll$extract0 st))
         (extracted1-st (interl-ll$extract1 st))
         (final-st (de-n (si 'interl-ll data-size) inputs-seq st netlist n))
         (final-extracted0-st (interl-ll$extract0 final-st))
         (final-extracted1-st (interl-ll$extract1 final-st)))
      (implies
       (and (interl-ll& netlist data-size)
            (interl-ll$input-format-n inputs-seq st data-size n)
            (interl-ll$valid-st st data-size)
            (member x (interleave final-extracted0-st final-extracted1-st)))
       (member
        (append x (interl-ll$out-seq-netlist
                   inputs-seq st netlist data-size n))
        (interleave (append (interl-ll$in0-seq-netlist
                             inputs-seq st netlist data-size n)
                            extracted0-st)
                    (append (interl-ll$in1-seq-netlist
                             inputs-seq st netlist data-size n)
                            extracted1-st)))))
    :hints (("Goal"
             :use interl-ll$dataflow-correct
             :in-theory (enable interl-ll$valid-st=>st-format
                                interl-ll$de-n))))
  )

;; Simulators for INTERL-LL

;; (progn
;;   (defun interl-ll$map-to-links (st)
;;     (b* ((q9-l (nth *interl-ll$q9-l* st))
;;          (q11-l (nth *interl-ll$q11-l* st))
;;          (arb-merge (nth *interl-ll$arb-merge* st)))
;;       (append (list (cons 'q9-l (queue9-l$map-to-links q9-l)))
;;               (list (cons 'q11-l (queue11-l$map-to-links q11-l)))
;;               (list (cons 'arb-merge (arb-merge$map-to-links arb-merge))))))

;;   (defun interl-ll$map-to-links-list (x)
;;     (if (atom x)
;;         nil
;;       (cons (interl-ll$map-to-links (car x))
;;             (interl-ll$map-to-links-list (cdr x)))))

;;   (defund interl-ll$st-gen (data-size)
;;     (declare (xargs :guard (natp data-size)))
;;     (b* ((full '(t))
;;          (empty '(nil))
;;          (q9-l (queue9-l$st-gen data-size))
;;          (q11-l (queue11-l$st-gen data-size))
;;          (arb-merge (list (list full '((nil) (nil)))
;;                           (list empty '((x) (x))))))
;;       (list q9-l q11-l arb-merge)))

;;   (defund interl-ll$ins-and-st-test (data-size n state)
;;     (declare (xargs :guard (and (natp data-size)
;;                                 (natp n))
;;                     :verify-guards nil
;;                     :stobjs state))
;;     (b* ((num-signals (interl-ll$ins-len data-size))
;;          ((mv inputs-seq state)
;;           (signal-vals-gen num-signals n state nil))
;;          (st (interl-ll$st-gen data-size)))
;;       (mv (and (interl-ll$input-format-n inputs-seq st data-size n)
;;                (interl-ll$valid-st st data-size))
;;           state)))

;;   (local
;;    (defthm interl-ll$ins-and-st-test-ok
;;      (interl-ll$ins-and-st-test 4 10 state)))

;;   (defund interl-ll$sim (data-size n state)
;;     (declare (xargs :guard (and (natp data-size)
;;                                 (natp n))
;;                     :verify-guards nil
;;                     :stobjs state))
;;     (b* ((num-signals (interl-ll$ins-len data-size))
;;          ((mv inputs-seq state)
;;           (signal-vals-gen num-signals n state nil))
;;          (st (interl-ll$st-gen data-size)))
;;       (mv (pretty-list
;;            (remove-dup-neighbors
;;             (interl-ll$map-to-links-list
;;              (de-sim-trace (si 'interl-ll data-size)
;;                            inputs-seq
;;                            st
;;                            (interl-ll$netlist data-size))))
;;            0)
;;           state)))

;;   (defund interl-ll$in-out-sim (data-size n state)
;;     (declare (xargs :guard (and (natp data-size)
;;                                 (natp n))
;;                     :verify-guards nil
;;                     :stobjs state))
;;     (b* ((num-signals (interl-ll$ins-len data-size))
;;          ((mv inputs-seq state)
;;           (signal-vals-gen num-signals n state nil))
;;          (st (interl-ll$st-gen data-size)))
;;       (mv
;;        (append
;;         (list (cons 'in0-seq
;;                     (v-to-nat-lst
;;                      (interl-ll$in0-seq inputs-seq st data-size n))))
;;         (list (cons 'in1-seq
;;                     (v-to-nat-lst
;;                      (interl-ll$in1-seq inputs-seq st data-size n))))
;;         (list (cons 'out-seq
;;                     (v-to-nat-lst
;;                      (interl-ll$out-seq inputs-seq st data-size n)))))
;;        state)))
;;   )

