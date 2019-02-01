;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; November 2018

(in-package "ADE")

(include-book "../link-joint")
(include-book "../tv-if")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of ALT-MERGE
;;; 2. Specify and Prove a State Invariant

;; ======================================================================

;; 1. DE Module Generator of ALT-MERGE
;;
;; Construct a DE module generator for an alternate merge, ALT-MERGE, using the
;; link-joint model.  Prove the value and state lemmas for this module
;; generator.

(defconst *alt-merge$go-num* 2)
(defconst *alt-merge$st-len* 2)

(defun alt-merge$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 3 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun alt-merge$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (alt-merge$data-ins-len data-width)
     *alt-merge$go-num*))

;; DE module generator of ALT-MERGE

(module-generator
 alt-merge* (data-width)
 (si 'alt-merge data-width)
 (list* 'full-in0 'full-in1 'empty-out-
        (append (sis 'data0-in 0 data-width)
                (sis 'data1-in 0 data-width)
                (sis 'go 0 *alt-merge$go-num*)))
 (list* 'act 'act0 'act1
        (sis 'data-out 0 data-width))
 '(select select-buf)
 (list
  ;; LINKS
  ;; Select
  '(select (select-status select-out)
           link1
           (buf-act act select-in))

  ;; Select-buf
  '(select-buf (select-buf-status select-buf-out)
               link1
               (act buf-act select-buf-in))

  ;; JOINTS
  ;; Alt-Merge
  '(g0 (select-out~) b-not (select-out))
  '(g1 (m-full-in0) b-and3 (full-in0 select-status select-out~))
  '(g2 (m-full-in1) b-and3 (full-in1 select-status select-out))
  '(g3 (m-empty-out-) b-or (empty-out- select-buf-status))
  (list 'alt-merge-cntl0
        '(act0)
        'joint-cntl
        (list 'm-full-in0 'm-empty-out- (si 'go 0)))
  (list 'alt-merge-cntl1
        '(act1)
        'joint-cntl
        (list 'm-full-in1 'm-empty-out- (si 'go 0)))
  '(alt-merge-cntl (act) b-or (act0 act1))

  (list 'alt-merge-op0
        (sis 'data-out 0 data-width)
        (si 'tv-if (tree-number (make-tree data-width)))
        (cons 'select-out
              (append (sis 'data1-in 0 data-width)
                      (sis 'data0-in 0 data-width))))
  '(alt-merge-op1 (select-buf-in) b-not (select-out))

  ;; Buffer
  (list 'buf-cntl
        '(buf-act)
        'joint-cntl
        (list 'select-buf-status 'select-status (si 'go 1)))
  '(buf-op (select-in) b-buf (select-buf-out)))

 (declare (xargs :guard (natp data-width))))

(make-event
 `(progn
    ,@(state-accessors-gen 'alt-merge '(select select-buf) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; ALT-MERGE.

(defund alt-merge$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (alt-merge* data-width)
        (union$ (link1$netlist)
                *joint-cntl*
                (tv-if$netlist (make-tree data-width))
                :test 'equal)))

;; Recognizer for ALT-MERGE

(defund alt-merge& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (b* ((subnetlist (delete-to-eq (si 'alt-merge data-width) netlist)))
    (and (equal (assoc (si 'alt-merge data-width) netlist)
                (alt-merge* data-width))
         (link1& subnetlist)
         (joint-cntl& subnetlist)
         (tv-if& subnetlist (make-tree data-width)))))

;; Sanity check

(local
 (defthmd check-alt-merge$netlist-64
   (and (net-syntax-okp (alt-merge$netlist 64))
        (net-arity-okp (alt-merge$netlist 64))
        (alt-merge& (alt-merge$netlist 64) 64))))

;; Constraints on the state of ALT-MERGE

(defund alt-merge$valid-st (st)
  (b* ((select (get-field *alt-merge$select* st))
       (select-buf (get-field *alt-merge$select-buf* st)))
    (and (link1$valid-st select)
         (link1$valid-st select-buf))))

;; Extract the input and output signals for ALT-MERGE

(progn
  ;; Extract the 1st input data item

  (defun alt-merge$data0-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 3 inputs)))

  (defthm len-alt-merge$data0-in
    (equal (len (alt-merge$data0-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable alt-merge$data0-in))

  ;; Extract the 2nd input data item

  (defun alt-merge$data1-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (b* ((width (mbe :logic (nfix data-width)
                     :exec  data-width)))
      (take width
            (nthcdr (+ 3 width) inputs))))

  (defthm len-alt-merge$data1-in
    (equal (len (alt-merge$data1-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable alt-merge$data1-in))

  ;; Extract the "act0" signal

  (defund alt-merge$act0 (inputs st data-width)
    (b* ((full-in0   (nth 0 inputs))
         (empty-out- (nth 2 inputs))
         (go-signals (nthcdr (alt-merge$data-ins-len data-width) inputs))

         (go-alt-merge (nth 0 go-signals))

         (select (get-field *alt-merge$select* st))
         (select.s (get-field *link1$s* select))
         (select.d (get-field *link1$d* select))
         (select-buf (get-field *alt-merge$select-buf* st))
         (select-buf.s (get-field *link1$s* select-buf))

         (m-full-in0 (f-and3 full-in0 (car select.s) (f-not (car select.d))))
         (m-empty-out- (f-or empty-out- (car select-buf.s))))

      (joint-act m-full-in0 m-empty-out- go-alt-merge)))

  (defthm alt-merge$act0-inactive
    (implies (or (not (nth 0 inputs))
                 (equal (nth 2 inputs) t))
             (not (alt-merge$act0 inputs st data-width)))
    :hints (("Goal" :in-theory (enable f-and3 alt-merge$act0))))

  ;; Extract the "act1" signal

  (defund alt-merge$act1 (inputs st data-width)
    (b* ((full-in1   (nth 1 inputs))
         (empty-out- (nth 2 inputs))
         (go-signals (nthcdr (alt-merge$data-ins-len data-width) inputs))

         (go-alt-merge (nth 0 go-signals))

         (select (get-field *alt-merge$select* st))
         (select.s (get-field *link1$s* select))
         (select.d (get-field *link1$d* select))
         (select-buf (get-field *alt-merge$select-buf* st))
         (select-buf.s (get-field *link1$s* select-buf))

         (m-full-in1 (f-and3 full-in1 (car select.s) (car select.d)))
         (m-empty-out- (f-or empty-out- (car select-buf.s))))

      (joint-act m-full-in1 m-empty-out- go-alt-merge)))

  (defthm alt-merge$act1-inactive
    (implies (or (not (nth 1 inputs))
                 (equal (nth 2 inputs) t))
             (not (alt-merge$act1 inputs st data-width)))
    :hints (("Goal" :in-theory (enable f-and3 alt-merge$act1))))

  ;; Extract the "act" signal

  (defund alt-merge$act (inputs st data-width)
    (f-or (alt-merge$act0 inputs st data-width)
          (alt-merge$act1 inputs st data-width)))

  (defthm alt-merge$act-inactive
    (implies (or (and (not (nth 0 inputs))
                      (not (nth 1 inputs)))
                 (equal (nth 2 inputs) t))
             (not (alt-merge$act inputs st data-width)))
    :hints (("Goal" :in-theory (enable alt-merge$act))))
  )

;; The value lemma for ALT-MERGE

(defthm alt-merge$value
  (b* ((inputs (list* full-in0 full-in1 empty-out-
                      (append data0-in data1-in go-signals)))
       (select (get-field *alt-merge$select* st))
       (select.d (get-field *link1$d* select)))
    (implies (and (posp data-width)
                  (alt-merge& netlist data-width)
                  (true-listp data0-in)
                  (equal (len data0-in) data-width)
                  (true-listp data1-in)
                  (equal (len data1-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *alt-merge$go-num*))
             (equal (se (si 'alt-merge data-width) inputs st netlist)
                    (list* (alt-merge$act inputs st data-width)
                           (alt-merge$act0 inputs st data-width)
                           (alt-merge$act1 inputs st data-width)
                           (fv-if (car select.d) data1-in data0-in)))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'alt-merge data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            alt-merge&
                            alt-merge*$destructure
                            alt-merge$act
                            alt-merge$act0
                            alt-merge$act1)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of ALT-MERGE.

(defun alt-merge$step (inputs st data-width)
  (b* ((go-signals (nthcdr (alt-merge$data-ins-len data-width) inputs))

       (go-buf (nth 1 go-signals))

       (select (get-field *alt-merge$select* st))
       (select.s (get-field *link1$s* select))
       (select.d (get-field *link1$d* select))
       (select-buf (get-field *alt-merge$select-buf* st))
       (select-buf.s (get-field *link1$s* select-buf))
       (select-buf.d (get-field *link1$d* select-buf))

       (act (alt-merge$act inputs st data-width))
       (buf-act (joint-act (car select-buf.s) (car select.s) go-buf))

       (select-inputs (list buf-act act (car select-buf.d)))
       (select-buf-inputs (list act buf-act (f-not (car select.d)))))
    (list
     ;; Select
     (link1$step select-inputs select)
     ;; Select-buf
     (link1$step select-buf-inputs select-buf))))

(defthm len-of-alt-merge$step
  (equal (len (alt-merge$step inputs st data-width))
         *alt-merge$st-len*))

;; The state lemma for ALT-MERGE

(defthm alt-merge$state
  (b* ((inputs (list* full-in0 full-in1 empty-out-
                      (append data0-in data1-in go-signals))))
    (implies (and (alt-merge& netlist data-width)
                  (equal (len data0-in) data-width)
                  (equal (len data1-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *alt-merge$go-num*))
             (equal (de (si 'alt-merge data-width) inputs st netlist)
                    (alt-merge$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'alt-merge data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            alt-merge&
                            alt-merge*$destructure
                            alt-merge$act
                            alt-merge$act0
                            alt-merge$act1)
                           (de-module-disabled-rules)))))

(in-theory (disable alt-merge$step))

;; ======================================================================

;; 2. Specify and Prove a State Invariant

;; Conditions on the inputs

(defund alt-merge$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in0   (nth 0 inputs))
       (full-in1   (nth 1 inputs))
       (empty-out- (nth 2 inputs))
       (data0-in   (alt-merge$data0-in inputs data-width))
       (data1-in   (alt-merge$data1-in inputs data-width))
       (go-signals (nthcdr (alt-merge$data-ins-len data-width) inputs)))
    (and
     (booleanp full-in0)
     (booleanp full-in1)
     (booleanp empty-out-)
     (or (not full-in0) (bvp data0-in))
     (or (not full-in1) (bvp data1-in))
     (true-listp go-signals)
     (= (len go-signals) *alt-merge$go-num*)
     (equal inputs
            (list* full-in0 full-in1 empty-out-
                   (append data0-in data1-in go-signals))))))

(defthm booleanp-alt-merge$act0
  (implies (and (alt-merge$input-format inputs data-width)
                (alt-merge$valid-st st))
           (booleanp (alt-merge$act0 inputs st data-width)))
  :hints (("Goal" :in-theory (enable f-and3
                                     alt-merge$input-format
                                     alt-merge$valid-st
                                     alt-merge$act0)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-alt-merge$act1
  (implies (and (alt-merge$input-format inputs data-width)
                (alt-merge$valid-st st))
           (booleanp (alt-merge$act1 inputs st data-width)))
  :hints (("Goal" :in-theory (enable f-and3
                                     alt-merge$input-format
                                     alt-merge$valid-st
                                     alt-merge$act1)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-alt-merge$act
  (implies (and (alt-merge$input-format inputs data-width)
                (alt-merge$valid-st st))
           (booleanp (alt-merge$act inputs st data-width)))
  :hints (("Goal" :in-theory (enable alt-merge$act)))
  :rule-classes (:rewrite :type-prescription))

(defthm alt-merge$valid-st-preserved
  (implies (and (alt-merge$input-format inputs data-width)
                (alt-merge$valid-st st))
           (alt-merge$valid-st (alt-merge$step inputs st data-width)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            f-sr
                            f-and3
                            alt-merge$input-format
                            alt-merge$valid-st
                            alt-merge$step
                            alt-merge$act
                            alt-merge$act0
                            alt-merge$act1)
                           ()))))

;; A state invariant

(defund alt-merge$inv (st)
  (b* ((select (get-field *alt-merge$select* st))
       (select.s (get-field *link1$s* select))
       (select-buf (get-field *alt-merge$select-buf* st))
       (select-buf.s (get-field *link1$s* select-buf)))
    (not (equal select.s select-buf.s))))

(defthm alt-merge$inv-preserved
  (implies (and (alt-merge$input-format inputs data-width)
                (alt-merge$valid-st st)
                (alt-merge$inv st))
           (alt-merge$inv (alt-merge$step inputs st data-width)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            f-sr
                            alt-merge$input-format
                            alt-merge$valid-st
                            alt-merge$inv
                            alt-merge$step
                            alt-merge$act
                            alt-merge$act0
                            alt-merge$act1)
                           ()))))

