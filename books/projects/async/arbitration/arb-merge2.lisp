;; Copyright (C) 2019, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "../link-joint")
(include-book "../tv-if")
(include-book "../vector-module")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth 3v-fix)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of ARB-MERGE
;;; 2. Specify and Prove a State Invariant
;;; 3. Properties of ARB-MERGE

;; ======================================================================

;; 1. DE Module Generator of ARB-MERGE
;;
;; Construct a DE module generator for a first-come-first-served (FCFS)
;; arbitrated merge model using the link-joint model.  Prove the value and
;; state lemmas for this module generator.

;; If two input sources are available at "approximately" the same time, the
;; arbitrated merge will RANDOMLY decide which source to service first.  The
;; merge will memorize this decision and use it as an indicator for servicing
;; the other source next.  Once the other source is serviced, the decision
;; information will be erased from the merge and the process will start over.
;; In our modeling, we use an oracle signal "select" to perform random
;; selections when necessary.

(defconst *arb-merge$select-num* 1)
(defconst *arb-merge$go-num* 2)

(defun arb-merge$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 3 (* 2 (mbe :logic (nfix data-size)
                 :exec  data-size))))

(defun arb-merge$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (arb-merge$data-ins-len data-size)
     *arb-merge$select-num*
     *arb-merge$go-num*))

;; DE module generator of ARB-MERGE

(module-generator
 arb-merge* (data-size)
 (si 'arb-merge data-size)
 (list* 'full-in0 'full-in1 'empty-out-
        (append (sis 'data0-in 0 data-size)
                (sis 'data1-in 0 data-size)
                (cons 'select ;; An oracle signal performing random selections
                      (sis 'go 0 *arb-merge$go-num*))))
 (list* 'act 'act0 'act1
        (sis 'data-out 0 data-size))
 '(arb arb-buf)
 (list
  ;; LINKS
  ;; Arb
  (list 'arb
        '(arb-status memoir-out grant-out selection-out)
        (si 'link 3)
        '(buf-act grant/merge-act memoir-in grant-in selection-in))

  ;; Arb-buf
  (list 'arb-buf
        '(arb-buf-status memoir-buf-out grant-buf-out selection-buf-out)
        (si 'link 3)
        '(grant/merge-act buf-act memoir-buf-in grant-buf-in selection-buf-in))

  ;; JOINTS
  ;; arb-merge
  '(g0 (b-select) b-bool (select))
  '(g1 (b-select~) b-not (b-select))
  (list 'g2 '(go-arb-merge) 'b-bool (list (si 'go 0)))
  '(g3 (memoir-out~) b-not (memoir-out))
  '(g4 (grant-out~) b-not (grant-out))
  '(g5 (selection-out~) b-not (selection-out))
  '(g6 (empty-in0-) b-not (full-in0))
  '(g7 (empty-in1-) b-not (full-in1))
  '(g8 (empty-out) b-not (empty-out-))
  '(g9 (arb-buf-status~) b-not (arb-buf-status))

  '(h0 (grant-ready) b-and3 (grant-out~ arb-status arb-buf-status~))
  '(h1 (grant0) b-and3 (grant-ready full-in0 empty-in1-))
  '(h2 (grant1) b-and3 (grant-ready empty-in0- full-in1))
  '(h3 (grant0-arb) b-and4 (grant-ready full-in0 full-in1 b-select~))
  '(h4 (grant1-arb) b-and4 (grant-ready full-in0 full-in1 b-select))
  '(h5 (merge-ready)
       b-and5
       (grant-out arb-status arb-buf-status~ empty-out go-arb-merge))
  '(h6 (merge0) b-and4 (merge-ready full-in0 memoir-out~ selection-out~))
  '(h7 (merge1) b-and4 (merge-ready full-in1 memoir-out~ selection-out))
  '(h8 (merge0-arb) b-and4 (merge-ready full-in0 memoir-out selection-out~))
  '(h9 (merge1-arb) b-and4 (merge-ready full-in1 memoir-out selection-out))

  '(h10 (grant-act) b-or4 (grant0 grant1 grant0-arb grant1-arb))
  '(h11 (act0) b-or (merge0 merge0-arb))
  '(h12 (act1) b-or (merge1 merge1-arb))
  '(h13 (act) b-or (act0 act1))
  '(h14 (grant/merge-act) b-or (grant-act act))
  '(memoir (memoir-buf-in) b-or (grant0-arb grant1-arb))
  '(grant (grant-buf-in) b-nor (merge0 merge1))
  '(selection (selection-buf-in) b-or3 (grant1 grant1-arb merge0-arb))
  (list 'arb-merge-data-op
        (sis 'data-out 0 data-size)
        (si 'tv-if (tree-number (make-tree data-size)))
        (cons 'act1
              (append (sis 'data1-in 0 data-size)
                      (sis 'data0-in 0 data-size))))

  ;; Buffer
  (list 'buf-cntl
        '(buf-act)
        'joint-cntl
        (list 'arb-buf-status 'arb-status (si 'go 1)))
  (list 'buf-op
        '(memoir-in grant-in selection-in)
        (si 'v-buf 3)
        '(memoir-buf-out grant-buf-out selection-buf-out)))

 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'arb-merge '(arb arb-buf) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; ARB-MERGE.

(defund arb-merge$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (arb-merge* data-size)
        (union$ (link$netlist 3)
                *joint-cntl*
                (v-buf$netlist 3)
                (tv-if$netlist (make-tree data-size))
                :test 'equal)))

;; Recognizer for ARB-MERGE

(defund arb-merge& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'arb-merge data-size) netlist)))
    (and (equal (assoc (si 'arb-merge data-size) netlist)
                (arb-merge* data-size))
         (link& subnetlist 3)
         (joint-cntl& subnetlist)
         (v-buf& subnetlist 3)
         (tv-if& subnetlist (make-tree data-size)))))

;; Sanity check

(local
 (defthmd check-arb-merge$netlist-64
   (and (net-syntax-okp (arb-merge$netlist 64))
        (net-arity-okp (arb-merge$netlist 64))
        (arb-merge& (arb-merge$netlist 64) 64))))

;; Constraints on the state of ARB-MERGE

(defund arb-merge$st-format (st)
  (b* ((arb (nth *arb-merge$arb* st))
       (arb-buf (nth *arb-merge$arb-buf* st)))
    (and (link$st-format arb 3)
         (link$st-format arb-buf 3))))

;; Constraints on the state of ARB-MERGE

(defund arb-merge$valid-st (st)
  (b* ((arb (nth *arb-merge$arb* st))
       (arb-buf (nth *arb-merge$arb-buf* st)))
    (and (link$valid-st arb 3)
         (link$valid-st arb-buf 3))))

(defthmd arb-merge$valid-st=>st-format
  (implies (arb-merge$valid-st st)
           (arb-merge$st-format st))
  :hints (("Goal" :in-theory (e/d (arb-merge$st-format
                                   arb-merge$valid-st)
                                  (link$st-format)))))

;; Extract the input and output signals for ARB-MERGE

(progn
  ;; Extract the 1st input data item

  (defun arb-merge$data0-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (mbe :logic (nfix data-size)
               :exec  data-size)
          (nthcdr 3 inputs)))

  (defthm len-arb-merge$data0-in
    (equal (len (arb-merge$data0-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable arb-merge$data0-in))

  ;; Extract the 2nd input data item

  (defun arb-merge$data1-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (b* ((size (mbe :logic (nfix data-size)
                     :exec  data-size)))
      (take size
            (nthcdr (+ 3 size) inputs))))

  (defthm len-arb-merge$data1-in
    (equal (len (arb-merge$data1-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable arb-merge$data1-in))

  ;; Extract the "act0" signal

  (defund arb-merge$act0 (inputs st data-size)
    (b* ((full-in0   (nth 0 inputs))
         (empty-out- (nth 2 inputs))
         (go-signals (nthcdr (+ (arb-merge$data-ins-len data-size)
                                *arb-merge$select-num*)
                             inputs))

         (go-arb-merge (nth 0 go-signals))

         (arb (nth *arb-merge$arb* st))
         (arb.s (nth *link$s* arb))
         (arb.d (nth *link$d* arb))
         (memoir-out (car (v-threefix (strip-cars arb.d))))
         (grant-out (cadr (v-threefix (strip-cars arb.d))))
         (selection-out (caddr (v-threefix (strip-cars arb.d))))
         (arb-buf (nth *arb-merge$arb-buf* st))
         (arb-buf.s (nth *link$s* arb-buf))

         (merge-ready (f-and5 grant-out
                              (car arb.s)
                              (f-not (car arb-buf.s))
                              (f-not empty-out-)
                              (f-bool go-arb-merge)))
         (merge0 (f-and4 merge-ready
                         full-in0
                         (f-not memoir-out)
                         (f-not selection-out)))
         (merge0-arb (f-and4 merge-ready
                             full-in0
                             memoir-out
                             (f-not selection-out))))

      (f-or merge0 merge0-arb)))

  (defthm arb-merge$act0-inactive
    (implies (or (not (nth 0 inputs))
                 (equal (nth 2 inputs) t))
             (not (arb-merge$act0 inputs st data-size)))
    :hints (("Goal" :in-theory (enable f-and4 f-and5 arb-merge$act0))))

  ;; Extract the "act1" signal

  (defund arb-merge$act1 (inputs st data-size)
    (b* ((full-in1   (nth 1 inputs))
         (empty-out- (nth 2 inputs))
         (go-signals (nthcdr (+ (arb-merge$data-ins-len data-size)
                                *arb-merge$select-num*)
                             inputs))

         (go-arb-merge (nth 0 go-signals))

         (arb (nth *arb-merge$arb* st))
         (arb.s (nth *link$s* arb))
         (arb.d (nth *link$d* arb))
         (memoir-out (car (v-threefix (strip-cars arb.d))))
         (grant-out (cadr (v-threefix (strip-cars arb.d))))
         (selection-out (caddr (v-threefix (strip-cars arb.d))))
         (arb-buf (nth *arb-merge$arb-buf* st))
         (arb-buf.s (nth *link$s* arb-buf))

         (merge-ready (f-and5 grant-out
                              (car arb.s)
                              (f-not (car arb-buf.s))
                              (f-not empty-out-)
                              (f-bool go-arb-merge)))
         (merge1 (f-and4 merge-ready
                         full-in1
                         (f-not memoir-out)
                         selection-out))
         (merge1-arb (f-and4 merge-ready
                             full-in1
                             memoir-out
                             selection-out)))

      (f-or merge1 merge1-arb)))

  (defthm arb-merge$act1-inactive
    (implies (or (not (nth 1 inputs))
                 (equal (nth 2 inputs) t))
             (not (arb-merge$act1 inputs st data-size)))
    :hints (("Goal" :in-theory (enable f-and4 f-and5 arb-merge$act1))))

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

  (defthm arb-merge$act-mutually-exclusive
    (implies (and (booleanp (nth 0 inputs))
                  (booleanp (nth 1 inputs))
                  (arb-merge$valid-st st)
                  (arb-merge$act0 inputs st data-size))
             (not (arb-merge$act1 inputs st data-size)))
    :hints (("Goal" :in-theory (enable f-and4
                                       f-and5
                                       arb-merge$valid-st
                                       arb-merge$act0
                                       arb-merge$act1))))

  ;; Extract the "act" signal

  (defund arb-merge$act (inputs st data-size)
    (f-or (arb-merge$act0 inputs st data-size)
          (arb-merge$act1 inputs st data-size)))

  (defthm arb-merge$act-inactive
    (implies (or (and (not (nth 0 inputs))
                      (not (nth 1 inputs)))
                 (equal (nth 2 inputs) t))
             (not (arb-merge$act inputs st data-size)))
    :hints (("Goal" :in-theory (enable arb-merge$act))))

  ;; Extract the output data

  (defund arb-merge$data-out (inputs st data-size)
    (b* ((data0-in (arb-merge$data0-in inputs data-size))
         (data1-in (arb-merge$data1-in inputs data-size))
         (act1 (arb-merge$act1 inputs st data-size)))
      (fv-if act1 data1-in data0-in)))

  (defthm len-arb-merge$data-out
    (equal (len (arb-merge$data-out inputs st data-size))
           (nfix data-size))
    :hints (("Goal" :in-theory (enable arb-merge$data-out))))
  )

;; The value lemma for ARB-MERGE

(defthm arb-merge$value
  (b* ((inputs (list* full-in0 full-in1 empty-out-
                      (append data0-in data1-in
                              (cons select go-signals)))))
    (implies (and (posp data-size)
                  (arb-merge& netlist data-size)
                  (true-listp data0-in)
                  (equal (len data0-in) data-size)
                  (true-listp data1-in)
                  (equal (len data1-in) data-size)
                  (equal (len go-signals) *arb-merge$go-num*)
                  (arb-merge$st-format st))
             (equal (se (si 'arb-merge data-size) inputs st netlist)
                    (list* (arb-merge$act inputs st data-size)
                           (arb-merge$act0 inputs st data-size)
                           (arb-merge$act1 inputs st data-size)
                           (arb-merge$data-out inputs st data-size)))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'arb-merge data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            arb-merge&
                            arb-merge*$destructure
                            arb-merge$st-format
                            arb-merge$act
                            arb-merge$act0
                            arb-merge$act1
                            arb-merge$data0-in
                            arb-merge$data1-in
                            arb-merge$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of ARB-MERGE.

(defun arb-merge$step (inputs st data-size)
  (b* ((full-in0   (nth 0 inputs))
       (full-in1   (nth 1 inputs))
       (empty-out- (nth 2 inputs))
       (select     (nth (arb-merge$data-ins-len data-size) inputs))
       (go-signals (nthcdr (+ (arb-merge$data-ins-len data-size)
                              *arb-merge$select-num*)
                           inputs))

       (b-select (f-bool select))
       (go-arb-merge (nth 0 go-signals))
       (go-buf (nth 1 go-signals))

       (arb (nth *arb-merge$arb* st))
       (arb.s (nth *link$s* arb))
       (arb.d (nth *link$d* arb))
       (memoir-out (car (v-threefix (strip-cars arb.d))))
       (grant-out (cadr (v-threefix (strip-cars arb.d))))
       (selection-out (caddr (v-threefix (strip-cars arb.d))))
       (arb-buf (nth *arb-merge$arb-buf* st))
       (arb-buf.s (nth *link$s* arb-buf))
       (arb-buf.d (nth *link$d* arb-buf))

       (grant-ready (f-and3 (f-not grant-out)
                            (car arb.s)
                            (f-not (car arb-buf.s))))
       (grant0 (f-and3 grant-ready full-in0 (f-not full-in1)))
       (grant1 (f-and3 grant-ready (f-not full-in0) full-in1))
       (grant0-arb (f-and4 grant-ready full-in0 full-in1 (f-not b-select)))
       (grant1-arb (f-and4 grant-ready full-in0 full-in1 b-select))
       (grant-act (f-or4 grant0 grant1 grant0-arb grant1-arb))
       (act (arb-merge$act inputs st data-size))
       (grant/merge-act (f-or grant-act act))
       (buf-act (joint-act (car arb-buf.s) (car arb.s) go-buf))

       (memoir-buf-in (f-or grant0-arb grant1-arb))

       (merge-ready (f-and5 grant-out
                            (car arb.s)
                            (f-not (car arb-buf.s))
                            (f-not empty-out-)
                            (f-bool go-arb-merge)))
       (merge0 (f-and4 merge-ready
                       full-in0
                       (f-not memoir-out)
                       (f-not selection-out)))
       (merge1 (f-and4 merge-ready
                       full-in1
                       (f-not memoir-out)
                       selection-out))
       (grant-buf-in (f-nor merge0 merge1))

       (merge0-arb (f-and4 merge-ready
                           full-in0
                           memoir-out
                           (f-not selection-out)))
       (selection-buf-in (f-or3 grant1 grant1-arb merge0-arb))

       (arb-inputs (list* buf-act grant/merge-act (strip-cars arb-buf.d)))
       (arb-buf-inputs (list grant/merge-act buf-act
                             memoir-buf-in grant-buf-in selection-buf-in)))
    (list
     ;; Arb
     (link$step arb-inputs arb 3)
     ;; Arb-buf
     (link$step arb-buf-inputs arb-buf 3))))

;; The state lemma for ARB-MERGE

(progn
  (local
   (defthm list-3v-fix-rewrite-3
     (implies (and (true-listp x)
                   (equal (len x) 3))
              (equal (list (3v-fix (car x))
                           (3v-fix (cadr x))
                           (3v-fix (caddr x)))
                     (v-threefix x)))))

  (defthm arb-merge$state
    (b* ((inputs (list* full-in0 full-in1 empty-out-
                        (append data0-in data1-in
                                (cons select go-signals)))))
      (implies (and (arb-merge& netlist data-size)
                    (equal (len data0-in) data-size)
                    (equal (len data1-in) data-size)
                    (equal (len go-signals) *arb-merge$go-num*)
                    (arb-merge$st-format st))
               (equal (de (si 'arb-merge data-size) inputs st netlist)
                      (arb-merge$step inputs st data-size))))
    :hints (("Goal"
             :do-not-induct t
             :expand (:free (inputs data-size)
                            (de (si 'arb-merge data-size) inputs st netlist))
             :in-theory (e/d (de-rules
                              arb-merge&
                              arb-merge*$destructure
                              arb-merge$st-format
                              arb-merge$act
                              arb-merge$act0
                              arb-merge$act1)
                             (de-module-disabled-rules)))))

  (in-theory (disable arb-merge$step))
  )

;; ======================================================================

;; 2. Specify and Prove a State Invariant

;; Conditions on the inputs

(defund arb-merge$input-format (inputs data-size)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-size))))
  (b* ((full-in0   (nth 0 inputs))
       (full-in1   (nth 1 inputs))
       (empty-out- (nth 2 inputs))
       (data0-in   (arb-merge$data0-in inputs data-size))
       (data1-in   (arb-merge$data1-in inputs data-size))
       (select     (nth (arb-merge$data-ins-len data-size) inputs))
       (go-signals (nthcdr (+ (arb-merge$data-ins-len data-size)
                              *arb-merge$select-num*)
                           inputs)))
    (and
     (booleanp full-in0)
     (booleanp full-in1)
     (booleanp empty-out-)
     (or (not full-in0) (bvp data0-in))
     (or (not full-in1) (bvp data1-in))
     (true-listp go-signals)
     (= (len go-signals) *arb-merge$go-num*)
     (equal inputs
            (list* full-in0 full-in1 empty-out-
                   (append data0-in data1-in (cons select go-signals)))))))

(defthmd arb-merge$value-alt
  (implies (and (posp data-size)
                (arb-merge& netlist data-size)
                (arb-merge$input-format inputs data-size)
                (arb-merge$st-format st))
           (equal (se (si 'arb-merge data-size) inputs st netlist)
                  (list* (arb-merge$act inputs st data-size)
                         (arb-merge$act0 inputs st data-size)
                         (arb-merge$act1 inputs st data-size)
                         (arb-merge$data-out inputs st data-size))))
  :hints (("Goal" :in-theory (enable arb-merge$input-format))))

(defthmd arb-merge$state-alt
  (implies (and (natp data-size)
                (arb-merge& netlist data-size)
                (arb-merge$input-format inputs data-size)
                (arb-merge$st-format st))
           (equal (de (si 'arb-merge data-size) inputs st netlist)
                  (arb-merge$step inputs st data-size)))
  :hints (("Goal" :in-theory (enable arb-merge$input-format))))

;; Prove that arb-merge$st-format is an invariant.

(defthm arb-merge$st-format-preserved
  (implies (arb-merge$st-format st)
           (arb-merge$st-format (arb-merge$step inputs st data-size)))
  :hints (("Goal" :in-theory (enable arb-merge$step
                                     arb-merge$st-format))))

;; Prove that arb-merge$valid-st is an invariant.

(defthm arb-merge$valid-st-preserved
  (implies (and (arb-merge$input-format inputs data-size)
                (arb-merge$valid-st st))
           (arb-merge$valid-st (arb-merge$step inputs st data-size)))
  :hints (("Goal"
           :in-theory (e/d (f-sr
                            f-and3
                            f-and4
                            f-and5
                            arb-merge$input-format
                            arb-merge$valid-st
                            arb-merge$step
                            arb-merge$act
                            arb-merge$act0
                            arb-merge$act1)
                           (nfix
                            arb-merge$act0-inactive
                            arb-merge$act1-inactive
                            arb-merge$act-inactive)))))

;; ======================================================================

;; 3. Properties of ARB-MERGE

(defthmd arb-merge$grant0
  (b* ((full-in0 (nth 0 inputs))
       (full-in1 (nth 1 inputs))

       (arb (nth *arb-merge$arb* st))
       (arb.s (nth *link$s* arb))
       (arb.d (nth *link$d* arb))
       (grant-out (cadr (v-threefix (strip-cars arb.d))))
       (arb-buf (nth *arb-merge$arb-buf* st))
       (arb-buf.s (nth *link$s* arb-buf))

       (next-st (de (si 'arb-merge data-size) inputs st netlist))

       (next-arb (nth *arb-merge$arb* next-st))
       (next-arb.s (nth *link$s* next-arb))
       (next-arb-buf (nth *arb-merge$arb-buf* next-st))
       (next-arb-buf.s (nth *link$s* next-arb-buf))
       (next-arb-buf.d (nth *link$d* next-arb-buf)))
    (implies (and (natp data-size)
                  (arb-merge& netlist data-size)
                  (arb-merge$input-format inputs data-size)
                  (arb-merge$st-format st)
                  (not grant-out)
                  (equal full-in0 t)
                  (not full-in1)
                  (fullp arb.s)
                  (emptyp arb-buf.s))
             (and (emptyp next-arb.s)
                  (fullp next-arb-buf.s)
                  (equal next-arb-buf.d
                         '((nil) (t) (nil)))
                  (not (arb-merge$act0 inputs st data-size))
                  (not (arb-merge$act1 inputs st data-size))
                  (not (arb-merge$act inputs st data-size)))))
  :hints (("Goal" :in-theory (enable f-and4
                                     f-and5
                                     arb-merge$act0
                                     arb-merge$act
                                     arb-merge$state-alt
                                     arb-merge$step))))

(defthmd arb-merge$grant1
  (b* ((full-in0 (nth 0 inputs))
       (full-in1 (nth 1 inputs))

       (arb (nth *arb-merge$arb* st))
       (arb.s (nth *link$s* arb))
       (arb.d (nth *link$d* arb))
       (grant-out (cadr (v-threefix (strip-cars arb.d))))
       (arb-buf (nth *arb-merge$arb-buf* st))
       (arb-buf.s (nth *link$s* arb-buf))

       (next-st (de (si 'arb-merge data-size) inputs st netlist))

       (next-arb (nth *arb-merge$arb* next-st))
       (next-arb.s (nth *link$s* next-arb))
       (next-arb-buf (nth *arb-merge$arb-buf* next-st))
       (next-arb-buf.s (nth *link$s* next-arb-buf))
       (next-arb-buf.d (nth *link$d* next-arb-buf)))
    (implies (and (natp data-size)
                  (arb-merge& netlist data-size)
                  (arb-merge$input-format inputs data-size)
                  (arb-merge$st-format st)
                  (not grant-out)
                  (not full-in0)
                  (equal full-in1 t)
                  (fullp arb.s)
                  (emptyp arb-buf.s))
             (and (emptyp next-arb.s)
                  (fullp next-arb-buf.s)
                  (equal next-arb-buf.d
                         '((nil) (t) (t)))
                  (not (arb-merge$act0 inputs st data-size))
                  (not (arb-merge$act1 inputs st data-size))
                  (not (arb-merge$act inputs st data-size)))))
  :hints (("Goal" :in-theory (enable f-and4
                                     f-and5
                                     arb-merge$act1
                                     arb-merge$act
                                     arb-merge$state-alt
                                     arb-merge$step))))

(defthmd arb-merge$grant-arb
  (b* ((full-in0 (nth 0 inputs))
       (full-in1 (nth 1 inputs))
       (select   (nth (arb-merge$data-ins-len data-size) inputs))

       (b-select (f-bool select))

       (arb (nth *arb-merge$arb* st))
       (arb.s (nth *link$s* arb))
       (arb.d (nth *link$d* arb))
       (grant-out (cadr (v-threefix (strip-cars arb.d))))
       (arb-buf (nth *arb-merge$arb-buf* st))
       (arb-buf.s (nth *link$s* arb-buf))

       (next-st (de (si 'arb-merge data-size) inputs st netlist))

       (next-arb (nth *arb-merge$arb* next-st))
       (next-arb.s (nth *link$s* next-arb))
       (next-arb-buf (nth *arb-merge$arb-buf* next-st))
       (next-arb-buf.s (nth *link$s* next-arb-buf))
       (next-arb-buf.d (nth *link$d* next-arb-buf)))
    (implies (and (natp data-size)
                  (arb-merge& netlist data-size)
                  (arb-merge$input-format inputs data-size)
                  (arb-merge$st-format st)
                  (not grant-out)
                  (equal full-in0 t)
                  (equal full-in1 t)
                  (fullp arb.s)
                  (emptyp arb-buf.s))
             (and (emptyp next-arb.s)
                  (fullp next-arb-buf.s)
                  (equal next-arb-buf.d
                         (list '(t) '(t) (list b-select)))
                  (not (arb-merge$act0 inputs st data-size))
                  (not (arb-merge$act1 inputs st data-size))
                  (not (arb-merge$act inputs st data-size)))))
  :hints (("Goal" :in-theory (enable f-and4
                                     f-and5
                                     arb-merge$act0
                                     arb-merge$act1
                                     arb-merge$act
                                     arb-merge$state-alt
                                     arb-merge$step))))

(defthmd arb-merge$merge0-possibly-arb
  (b* ((full-in0   (nth 0 inputs))
       (empty-out- (nth 2 inputs))
       (go-signals (nthcdr (+ (arb-merge$data-ins-len data-size)
                              *arb-merge$select-num*)
                           inputs))

       (go-arb-merge (nth 0 go-signals))
       (b-go-arb-merge (f-bool go-arb-merge))

       (arb (nth *arb-merge$arb* st))
       (arb.s (nth *link$s* arb))
       (arb.d (nth *link$d* arb))
       (memoir-out (car (v-threefix (strip-cars arb.d))))
       (grant-out (cadr (v-threefix (strip-cars arb.d))))
       (selection-out (caddr (v-threefix (strip-cars arb.d))))
       (arb-buf (nth *arb-merge$arb-buf* st))
       (arb-buf.s (nth *link$s* arb-buf))

       (outputs (se (si 'arb-merge data-size) inputs st netlist))
       (data-out (nthcdr 3 outputs))

       (next-st (de (si 'arb-merge data-size) inputs st netlist))

       (next-arb (nth *arb-merge$arb* next-st))
       (next-arb.s (nth *link$s* next-arb))
       (next-arb-buf (nth *arb-merge$arb-buf* next-st))
       (next-arb-buf.s (nth *link$s* next-arb-buf))
       (next-arb-buf.d (nth *link$d* next-arb-buf)))
    (implies (and (posp data-size)
                  (arb-merge& netlist data-size)
                  (arb-merge$input-format inputs data-size)
                  (arb-merge$valid-st st)
                  b-go-arb-merge
                  (equal grant-out t)
                  (not selection-out)
                  (equal full-in0 t)
                  (not empty-out-)
                  (fullp arb.s)
                  (emptyp arb-buf.s))
             (and (emptyp next-arb.s)
                  (fullp next-arb-buf.s)
                  (equal next-arb-buf.d
                         (list '(nil) (list memoir-out) (list memoir-out)))
                  (equal (arb-merge$act0 inputs st data-size)
                         t)
                  (not (arb-merge$act1 inputs st data-size))
                  (equal (arb-merge$act inputs st data-size)
                         t)
                  (equal data-out
                         (arb-merge$data0-in inputs data-size)))))
  :hints (("Goal"
           :use arb-merge$valid-st=>st-format
           :in-theory (enable arb-merge$input-format
                              arb-merge$valid-st
                              arb-merge$value-alt
                              arb-merge$state-alt
                              arb-merge$act0
                              arb-merge$act1
                              arb-merge$act
                              arb-merge$data-out
                              arb-merge$step))))

(local
 (defthm 3v-fix-of-boolean-is-itself
   (implies (booleanp x)
            (equal (3v-fix x) x))
   :hints (("Goal" :in-theory (enable 3v-fix)))))

(defthmd arb-merge$merge1-possibly-arb
  (b* ((full-in1   (nth 1 inputs))
       (empty-out- (nth 2 inputs))
       (go-signals (nthcdr (+ (arb-merge$data-ins-len data-size)
                              *arb-merge$select-num*)
                           inputs))

       (go-arb-merge (nth 0 go-signals))
       (b-go-arb-merge (f-bool go-arb-merge))

       (arb (nth *arb-merge$arb* st))
       (arb.s (nth *link$s* arb))
       (arb.d (nth *link$d* arb))
       (memoir-out (car (v-threefix (strip-cars arb.d))))
       (grant-out (cadr (v-threefix (strip-cars arb.d))))
       (selection-out (caddr (v-threefix (strip-cars arb.d))))
       (arb-buf (nth *arb-merge$arb-buf* st))
       (arb-buf.s (nth *link$s* arb-buf))

       (outputs (se (si 'arb-merge data-size) inputs st netlist))
       (data-out (nthcdr 3 outputs))

       (next-st (de (si 'arb-merge data-size) inputs st netlist))

       (next-arb (nth *arb-merge$arb* next-st))
       (next-arb.s (nth *link$s* next-arb))
       (next-arb-buf (nth *arb-merge$arb-buf* next-st))
       (next-arb-buf.s (nth *link$s* next-arb-buf))
       (next-arb-buf.d (nth *link$d* next-arb-buf)))
    (implies (and (posp data-size)
                  (arb-merge& netlist data-size)
                  (arb-merge$input-format inputs data-size)
                  (arb-merge$valid-st st)
                  b-go-arb-merge
                  (equal grant-out t)
                  (equal selection-out t)
                  (equal full-in1 t)
                  (not empty-out-)
                  (fullp arb.s)
                  (emptyp arb-buf.s))
             (and (emptyp next-arb.s)
                  (fullp next-arb-buf.s)
                  (equal next-arb-buf.d
                         (list '(nil) (list memoir-out) '(nil)))
                  (not (arb-merge$act0 inputs st data-size))
                  (equal (arb-merge$act1 inputs st data-size)
                         t)
                  (equal (arb-merge$act inputs st data-size)
                         t)
                  (equal data-out
                         (arb-merge$data1-in inputs data-size)))))
  :hints (("Goal"
           :use arb-merge$valid-st=>st-format
           :in-theory (enable arb-merge$input-format
                              arb-merge$valid-st
                              arb-merge$value-alt
                              arb-merge$state-alt
                              arb-merge$act0
                              arb-merge$act1
                              arb-merge$act
                              arb-merge$data-out
                              arb-merge$step))))

