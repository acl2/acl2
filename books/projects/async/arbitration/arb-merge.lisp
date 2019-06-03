;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "../link-joint")
(include-book "../tv-if")
(include-book "../vector-module")

(local (include-book "../list-rewrites"))

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of ARB-MERGE
;;; 2. Specify and Prove a State Invariant
;;; 3. Some Properties of ARB-MERGE

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
        '(arb-status excl-out arb-out)
        (si 'link 2)
        '(buf-act act excl-in arb-in))

  ;; Arb-buf
  (list 'arb-buf
        '(arb-buf-status excl-buf-out arb-buf-out)
        (si 'link 2)
        '(act buf-act excl-buf-in arb-buf-in))

  ;; JOINTS
  ;; Arb-Merge
  '(g0 (b-select) b-bool (select))
  '(g1 (b-select~) b-not (b-select))
  '(g2 (excl-out~) b-not (excl-out))
  '(g3 (arb-out~) b-not (arb-out))
  '(g4 (empty-in0-) b-not (full-in0))
  '(g5 (empty-in1-) b-not (full-in1))

  '(h0 (m-full-in0-1) b-and4 (full-in0 empty-in1- arb-status excl-out~))
  '(h1 (m-full-in0-2) b-and5 (full-in0 full-in1 arb-status excl-out~ b-select~))
  '(h2 (m-full-in0-3) b-and4 (full-in0 arb-status excl-out arb-out~))
  '(h3 (m-full-in0) b-or3 (m-full-in0-1 m-full-in0-2 m-full-in0-3))

  '(h4 (m-full-in1-1) b-and4 (empty-in0- full-in1 arb-status excl-out~))
  '(h5 (m-full-in1-2) b-and5 (full-in0 full-in1 arb-status excl-out~ b-select))
  '(h6 (m-full-in1-3) b-and4 (full-in1 arb-status excl-out arb-out))
  '(h7 (m-full-in1) b-or3 (m-full-in1-1 m-full-in1-2 m-full-in1-3))

  '(h8 (m-empty-out-) b-or (empty-out- arb-buf-status))
  (list 'arb-merge-cntl0
        '(act0)
        'joint-cntl
        (list 'm-full-in0 'm-empty-out- (si 'go 0)))
  (list 'arb-merge-cntl1
        '(act1)
        'joint-cntl
        (list 'm-full-in1 'm-empty-out- (si 'go 0)))
  '(arb-merge-cntl (act) b-or (act0 act1))

  (list 'arb-merge-op0
        (sis 'data-out 0 data-size)
        (si 'tv-if (tree-number (make-tree data-size)))
        (cons 'act1
              (append (sis 'data1-in 0 data-size)
                      (sis 'data0-in 0 data-size))))
  '(i0 (low) vss ())
  '(i1 (high) vdd ())
  '(i2 (reset0) b-and (full-in0 empty-in1-))
  '(i3 (reset1) b-and (empty-in0- full-in1))
  '(i4 (reset) b-or3 (reset0 reset1 excl-out))
  (list 'arb-merge-op1
        '(excl-buf-in arb-buf-in)
        (si 'v-if 2)
        (cons 'reset (append '(low low) '(high b-select~))))

  ;; Buffer
  (list 'buf-cntl
        '(buf-act)
        'joint-cntl
        (list 'arb-buf-status 'arb-status (si 'go 1)))
  (list 'buf-op
        '(excl-in arb-in)
        (si 'v-buf 2)
        '(excl-buf-out arb-buf-out)))

 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'arb-merge '(arb arb-buf) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; ARB-MERGE.

(defund arb-merge$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (arb-merge* data-size)
        (union$ (link$netlist 2)
                *joint-cntl*
                (v-buf$netlist 2)
                (v-if$netlist 2)
                (tv-if$netlist (make-tree data-size))
                :test 'equal)))

;; Recognizer for ARB-MERGE

(defund arb-merge& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'arb-merge data-size) netlist)))
    (and (equal (assoc (si 'arb-merge data-size) netlist)
                (arb-merge* data-size))
         (link& subnetlist 2)
         (joint-cntl& subnetlist)
         (v-buf& subnetlist 2)
         (v-if& subnetlist 2)
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
    (and (link$st-format arb 2)
         (link$st-format arb-buf 2))))

;; Constraints on the state of ARB-MERGE

(defund arb-merge$valid-st (st)
  (b* ((arb (nth *arb-merge$arb* st))
       (arb-buf (nth *arb-merge$arb-buf* st)))
    (and (link$valid-st arb 2)
         (link$valid-st arb-buf 2))))

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
         (full-in1   (nth 1 inputs))
         (empty-out- (nth 2 inputs))
         (select     (nth (arb-merge$data-ins-len data-size) inputs))
         (go-signals (nthcdr (+ (arb-merge$data-ins-len data-size)
                                *arb-merge$select-num*)
                             inputs))

         (b-select (f-bool select))
         (go-arb-merge (nth 0 go-signals))

         (arb (nth *arb-merge$arb* st))
         (arb.s (nth *link$s* arb))
         (arb.d (nth *link$d* arb))
         (excl-out (car (v-threefix (strip-cars arb.d))))
         (arb-out (cadr (v-threefix (strip-cars arb.d))))
         (arb-buf (nth *arb-merge$arb-buf* st))
         (arb-buf.s (nth *link$s* arb-buf))

         (m-full-in0 (f-or3 (f-and4 full-in0
                                    (f-not full-in1)
                                    (car arb.s)
                                    (f-not excl-out))
                            (f-and5 full-in0
                                    full-in1
                                    (car arb.s)
                                    (f-not excl-out)
                                    (f-not b-select))
                            (f-and4 full-in0
                                    (car arb.s)
                                    excl-out
                                    (f-not arb-out))))
         (m-empty-out- (f-or empty-out- (car arb-buf.s))))

      (joint-act m-full-in0 m-empty-out- go-arb-merge)))

  (defthm arb-merge$act0-inactive
    (implies (or (not (nth 0 inputs))
                 (equal (nth 2 inputs) t))
             (not (arb-merge$act0 inputs st data-size)))
    :hints (("Goal" :in-theory (enable f-and4 f-and5 arb-merge$act0))))

  ;; Extract the "act1" signal

  (defund arb-merge$act1 (inputs st data-size)
    (b* ((full-in0   (nth 0 inputs))
         (full-in1   (nth 1 inputs))
         (empty-out- (nth 2 inputs))
         (select     (nth (arb-merge$data-ins-len data-size) inputs))
         (go-signals (nthcdr (+ (arb-merge$data-ins-len data-size)
                                *arb-merge$select-num*)
                             inputs))

         (b-select (f-bool select))
         (go-arb-merge (nth 0 go-signals))

         (arb (nth *arb-merge$arb* st))
         (arb.s (nth *link$s* arb))
         (arb.d (nth *link$d* arb))
         (excl-out (car (v-threefix (strip-cars arb.d))))
         (arb-out (cadr (v-threefix (strip-cars arb.d))))
         (arb-buf (nth *arb-merge$arb-buf* st))
         (arb-buf.s (nth *link$s* arb-buf))

         (m-full-in1 (f-or3 (f-and4 (f-not full-in0)
                                    full-in1
                                    (car arb.s)
                                    (f-not excl-out))
                            (f-and5 full-in0
                                    full-in1
                                    (car arb.s)
                                    (f-not excl-out)
                                    b-select)
                            (f-and4 full-in1
                                    (car arb.s)
                                    excl-out
                                    arb-out)))
         (m-empty-out- (f-or empty-out- (car arb-buf.s))))

      (joint-act m-full-in1 m-empty-out- go-arb-merge)))

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
       (select     (nth (arb-merge$data-ins-len data-size) inputs))
       (go-signals (nthcdr (+ (arb-merge$data-ins-len data-size)
                              *arb-merge$select-num*)
                           inputs))

       (b-select (f-bool select))
       (go-buf (nth 1 go-signals))

       (arb (nth *arb-merge$arb* st))
       (arb.s (nth *link$s* arb))
       (arb.d (nth *link$d* arb))
       (excl-out (car (v-threefix (strip-cars arb.d))))
       (arb-buf (nth *arb-merge$arb-buf* st))
       (arb-buf.s (nth *link$s* arb-buf))
       (arb-buf.d (nth *link$d* arb-buf))

       (act (arb-merge$act inputs st data-size))
       (buf-act (joint-act (car arb-buf.s) (car arb.s) go-buf))

       (reset (f-or3 (f-and full-in0 (f-not full-in1))
                     (f-and (f-not full-in0) full-in1)
                     excl-out))
       (arb-buf-update (fv-if reset '(nil nil) (list t (f-not b-select))))

       (arb-inputs (list* buf-act act (strip-cars arb-buf.d)))
       (arb-buf-inputs (list* act buf-act arb-buf-update)))
    (list
     ;; Arb
     (link$step arb-inputs arb 2)
     ;; Arb-buf
     (link$step arb-buf-inputs arb-buf 2))))

;; The state lemma for ARB-MERGE

(progn
  (local
   (defthm list-3v-fix-rewrite-2
     (implies (and (true-listp x)
                   (equal (len x) 2))
              (equal (list (3v-fix (car x)) (3v-fix (cadr x)))
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
             :use (:instance
                   v-if$value
                   (n 2)
                   (c (f-or3 (f-and full-in0 (f-not full-in1))
                             (f-and (f-not full-in0) full-in1)
                             (3v-fix (car (strip-cars (cadr (car st)))))))
                   (a '(nil nil))
                   (b (list t (f-not (f-bool select))))
                   (st nil)
                   (netlist (delete-to-eq (si 'arb-merge (len data0-in))
                                          netlist)))
             :in-theory (e/d (de-rules
                              arb-merge&
                              arb-merge*$destructure
                              arb-merge$st-format
                              arb-merge$act
                              arb-merge$act0
                              arb-merge$act1
                              list-rewrite-2)
                             (3v-fix
                              de-module-disabled-rules)))))

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
                            f-and4
                            f-and5
                            f-or3
                            f-not
                            arb-merge$input-format
                            arb-merge$valid-st
                            arb-merge$step
                            arb-merge$act
                            arb-merge$act0
                            arb-merge$act1)
                           (arb-merge$act0-inactive
                            arb-merge$act1-inactive
                            arb-merge$act-inactive)))))

;; ======================================================================

;; 3. Some Properties of ARB-MERGE

(defthmd arb-merge$random-select
  (b* ((full-in0   (nth 0 inputs))
       (full-in1   (nth 1 inputs))
       (empty-out- (nth 2 inputs))
       (select     (nth (arb-merge$data-ins-len data-size) inputs))
       (go-signals (nthcdr (+ (arb-merge$data-ins-len data-size)
                              *arb-merge$select-num*)
                           inputs))

       (b-select (f-bool select))
       (go-arb-merge (nth 0 go-signals))

       (arb (nth *arb-merge$arb* st))
       (arb.s (nth *link$s* arb))
       (arb.d (nth *link$d* arb))
       (excl-out (car (v-threefix (strip-cars arb.d))))
       (arb-buf (nth *arb-merge$arb-buf* st))
       (arb-buf.s (nth *link$s* arb-buf))

       (next-st (arb-merge$step inputs st data-size))

       (next-arb-buf (nth *arb-merge$arb-buf* next-st))
       (next-arb-buf.s (nth *link$s* next-arb-buf))
       (next-arb-buf.d (nth *link$d* next-arb-buf)))
    (implies (and (arb-merge$valid-st st)
                  (equal full-in0 t)
                  (equal full-in1 t)
                  (not empty-out-)
                  (fullp arb.s)
                  (emptyp arb-buf.s)
                  go-arb-merge
                  (not excl-out))
             (and (equal (arb-merge$act0 inputs st data-size)
                         (not b-select))
                  (equal (arb-merge$act1 inputs st data-size)
                         b-select)
                  (fullp next-arb-buf.s)
                  (equal next-arb-buf.d
                         (list '(t) (list (not b-select)))))))
  :hints (("Goal" :in-theory (enable f-bool
                                     arb-merge$valid-st
                                     arb-merge$step
                                     arb-merge$act0
                                     arb-merge$act1
                                     arb-merge$act))))

(defthmd arb-merge$select-0
  (b* ((full-in0   (nth 0 inputs))
       (empty-out- (nth 2 inputs))
       (go-signals (nthcdr (+ (arb-merge$data-ins-len data-size)
                              *arb-merge$select-num*)
                           inputs))

       (go-arb-merge (nth 0 go-signals))

       (arb (nth *arb-merge$arb* st))
       (arb.s (nth *link$s* arb))
       (arb.d (nth *link$d* arb))
       (excl-out (car (v-threefix (strip-cars arb.d))))
       (arb-out (cadr (v-threefix (strip-cars arb.d))))
       (arb-buf (nth *arb-merge$arb-buf* st))
       (arb-buf.s (nth *link$s* arb-buf))

       (next-st (arb-merge$step inputs st data-size))

       (next-arb-buf (nth *arb-merge$arb-buf* next-st))
       (next-arb-buf.s (nth *link$s* next-arb-buf))
       (next-arb-buf.d (nth *link$d* next-arb-buf)))
    (implies (and (arb-merge$valid-st st)
                  (equal full-in0 t)
                  (not empty-out-)
                  (fullp arb.s)
                  (emptyp arb-buf.s)
                  go-arb-merge
                  excl-out
                  (not arb-out))
             (and (equal (arb-merge$act0 inputs st data-size)
                         t)
                  (fullp next-arb-buf.s)
                  (equal next-arb-buf.d
                         '((nil) (nil))))))
  :hints (("Goal" :in-theory (enable 3vp
                                     f-or3
                                     f-bool
                                     arb-merge$valid-st
                                     arb-merge$step
                                     arb-merge$act0
                                     arb-merge$act1
                                     arb-merge$act))))

(defthmd arb-merge$select-1
  (b* ((full-in1   (nth 1 inputs))
       (empty-out- (nth 2 inputs))
       (go-signals (nthcdr (+ (arb-merge$data-ins-len data-size)
                              *arb-merge$select-num*)
                           inputs))

       (go-arb-merge (nth 0 go-signals))

       (arb (nth *arb-merge$arb* st))
       (arb.s (nth *link$s* arb))
       (arb.d (nth *link$d* arb))
       (excl-out (car (v-threefix (strip-cars arb.d))))
       (arb-out (cadr (v-threefix (strip-cars arb.d))))
       (arb-buf (nth *arb-merge$arb-buf* st))
       (arb-buf.s (nth *link$s* arb-buf))

       (next-st (arb-merge$step inputs st data-size))

       (next-arb-buf (nth *arb-merge$arb-buf* next-st))
       (next-arb-buf.s (nth *link$s* next-arb-buf))
       (next-arb-buf.d (nth *link$d* next-arb-buf)))
    (implies (and (arb-merge$valid-st st)
                  (equal full-in1 t)
                  (not empty-out-)
                  (fullp arb.s)
                  (emptyp arb-buf.s)
                  go-arb-merge
                  excl-out
                  arb-out)
             (and (equal (arb-merge$act1 inputs st data-size)
                         t)
                  (fullp next-arb-buf.s)
                  (equal next-arb-buf.d
                         '((nil) (nil))))))
  :hints (("Goal" :in-theory (enable 3vp
                                     f-or3
                                     f-bool
                                     arb-merge$valid-st
                                     arb-merge$step
                                     arb-merge$act0
                                     arb-merge$act1
                                     arb-merge$act))))


