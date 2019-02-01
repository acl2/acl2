;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; November 2018

(in-package "ADE")

(include-book "../link-joint")
(include-book "../vector-module")

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of ALT-BRANCH
;;; 2. Specify and Prove a State Invariant

;; ======================================================================

;; 1. DE Module Generator of ALT-BRANCH
;;
;; Construct a DE module generator for an alternate branch, ALT-BRANCH, using
;; the link-joint model.  Prove the value and state lemmas for this module
;; generator.

(defconst *alt-branch$go-num* 2)
(defconst *alt-branch$st-len* 2)

(defun alt-branch$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 3 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun alt-branch$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (alt-branch$data-ins-len data-width)
     *alt-branch$go-num*))

;; DE module generator of ALT-BRANCH

(module-generator
 alt-branch* (data-width)
 (si 'alt-branch data-width)
 (list* 'full-in 'empty-out0- 'empty-out1-
        (append (sis 'data-in 0 data-width)
                (sis 'go 0 *alt-branch$go-num*)))
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
  ;; Alt-Branch
  '(g0 (select-out~) b-not (select-out))
  '(g1 (m-full-in) b-and (full-in select-status))
  '(g2 (m-empty-out0-) b-or3 (empty-out0- select-buf-status select-out))
  '(g3 (m-empty-out1-) b-or3 (empty-out1- select-buf-status select-out~))
  (list 'alt-branch-cntl0
        '(act0)
        'joint-cntl
        (list 'm-full-in 'm-empty-out0- (si 'go 0)))
  (list 'alt-branch-cntl1
        '(act1)
        'joint-cntl
        (list 'm-full-in 'm-empty-out1- (si 'go 0)))
  '(alt-branch-cntl (act) b-or (act0 act1))

  (list 'alt-branch-op0
        (sis 'data-out 0 data-width)
        (si 'v-buf data-width)
        (sis 'data-in 0 data-width))
  '(alt-branch-op1 (select-buf-in) b-not (select-out))

  ;; Buffer
  (list 'buf-cntl
        '(buf-act)
        'joint-cntl
        (list 'select-buf-status 'select-status (si 'go 1)))
  '(buf-op (select-in) b-buf (select-buf-out)))

 (declare (xargs :guard (natp data-width))))

(make-event
 `(progn
    ,@(state-accessors-gen 'alt-branch '(select select-buf) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; ALT-BRANCH.

(defund alt-branch$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (alt-branch* data-width)
        (union$ (link1$netlist)
                *joint-cntl*
                (v-buf$netlist data-width)
                :test 'equal)))

;; Recognizer for ALT-BRANCH

(defund alt-branch& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (b* ((subnetlist (delete-to-eq (si 'alt-branch data-width) netlist)))
    (and (equal (assoc (si 'alt-branch data-width) netlist)
                (alt-branch* data-width))
         (link1& subnetlist)
         (joint-cntl& subnetlist)
         (v-buf& subnetlist data-width))))

;; Sanity check

(local
 (defthmd check-alt-branch$netlist-64
   (and (net-syntax-okp (alt-branch$netlist 64))
        (net-arity-okp (alt-branch$netlist 64))
        (alt-branch& (alt-branch$netlist 64) 64))))

;; Constraints on the state of ALT-BRANCH

(defund alt-branch$valid-st (st)
  (b* ((select (get-field *alt-branch$select* st))
       (select-buf (get-field *alt-branch$select-buf* st)))
    (and (link1$valid-st select)
         (link1$valid-st select-buf))))

;; Extract the input and output signals for ALT-BRANCH

(progn
  ;; Extract the input data

  (defun alt-branch$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 3 inputs)))

  (defthm len-alt-branch$data-in
    (equal (len (alt-branch$data-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable alt-branch$data-in))

  ;; Extract the "act0" signal

  (defund alt-branch$act0 (inputs st data-width)
    (b* ((full-in     (nth 0 inputs))
         (empty-out0- (nth 1 inputs))
         (go-signals  (nthcdr (alt-branch$data-ins-len data-width) inputs))

         (go-alt-branch (nth 0 go-signals))

         (select (get-field *alt-branch$select* st))
         (select.s (get-field *link1$s* select))
         (select.d (get-field *link1$d* select))
         (select-buf (get-field *alt-branch$select-buf* st))
         (select-buf.s (get-field *link1$s* select-buf))

         (m-full-in (f-and full-in (car select.s)))
         (m-empty-out0- (f-or3 empty-out0- (car select-buf.s) (car select.d))))

      (joint-act m-full-in m-empty-out0- go-alt-branch)))

  (defthm alt-branch$act0-inactive
    (implies (or (not (nth 0 inputs))
                 (equal (nth 1 inputs) t))
             (not (alt-branch$act0 inputs st data-width)))
    :hints (("Goal" :in-theory (enable f-or3 alt-branch$act0))))

  ;; Extract the "act1" signal

  (defund alt-branch$act1 (inputs st data-width)
    (b* ((full-in     (nth 0 inputs))
         (empty-out1- (nth 2 inputs))
         (go-signals  (nthcdr (alt-branch$data-ins-len data-width) inputs))

         (go-alt-branch (nth 0 go-signals))

         (select (get-field *alt-branch$select* st))
         (select.s (get-field *link1$s* select))
         (select.d (get-field *link1$d* select))
         (select-buf (get-field *alt-branch$select-buf* st))
         (select-buf.s (get-field *link1$s* select-buf))

         (m-full-in (f-and full-in (car select.s)))
         (m-empty-out1- (f-or3 empty-out1-
                               (car select-buf.s)
                               (f-not (car select.d)))))

      (joint-act m-full-in m-empty-out1- go-alt-branch)))

  (defthm alt-branch$act1-inactive
    (implies (or (not (nth 0 inputs))
                 (equal (nth 2 inputs) t))
             (not (alt-branch$act1 inputs st data-width)))
    :hints (("Goal" :in-theory (enable f-or3 alt-branch$act1))))

  ;; Extract the "act" signal

  (defund alt-branch$act (inputs st data-width)
    (f-or (alt-branch$act0 inputs st data-width)
          (alt-branch$act1 inputs st data-width)))

  (defthm alt-branch$act-inactive
    (implies (or (not (nth 0 inputs))
                 (and (equal (nth 1 inputs) t)
                      (equal (nth 2 inputs) t)))
             (not (alt-branch$act inputs st data-width)))
    :hints (("Goal" :in-theory (enable alt-branch$act))))
  )

;; The value lemma for ALT-BRANCH

(defthm alt-branch$value
  (b* ((inputs (list* full-in empty-out0- empty-out1-
                      (append data-in go-signals))))
    (implies (and (alt-branch& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *alt-branch$go-num*))
             (equal (se (si 'alt-branch data-width) inputs st netlist)
                    (list* (alt-branch$act inputs st data-width)
                           (alt-branch$act0 inputs st data-width)
                           (alt-branch$act1 inputs st data-width)
                           (v-threefix data-in)))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'alt-branch data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            alt-branch&
                            alt-branch*$destructure
                            alt-branch$act
                            alt-branch$act0
                            alt-branch$act1)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of ALT-BRANCH.

(defun alt-branch$step (inputs st data-width)
  (b* ((go-signals (nthcdr (alt-branch$data-ins-len data-width) inputs))

       (go-buf (nth 1 go-signals))

       (select (get-field *alt-branch$select* st))
       (select.s (get-field *link1$s* select))
       (select.d (get-field *link1$d* select))
       (select-buf (get-field *alt-branch$select-buf* st))
       (select-buf.s (get-field *link1$s* select-buf))
       (select-buf.d (get-field *link1$d* select-buf))

       (act (alt-branch$act inputs st data-width))
       (buf-act (joint-act (car select-buf.s) (car select.s) go-buf))

       (select-inputs (list buf-act act (car select-buf.d)))
       (select-buf-inputs (list act buf-act (f-not (car select.d)))))
    (list
     ;; Select
     (link1$step select-inputs select)
     ;; Select-buf
     (link1$step select-buf-inputs select-buf))))

(defthm len-of-alt-branch$step
  (equal (len (alt-branch$step inputs st data-width))
         *alt-branch$st-len*))

;; The state lemma for ALT-BRANCH

(defthm alt-branch$state
  (b* ((inputs (list* full-in empty-out0- empty-out1-
                      (append data-in go-signals))))
    (implies (and (alt-branch& netlist data-width)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *alt-branch$go-num*))
             (equal (de (si 'alt-branch data-width) inputs st netlist)
                    (alt-branch$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'alt-branch data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            alt-branch&
                            alt-branch*$destructure
                            alt-branch$act
                            alt-branch$act0
                            alt-branch$act1)
                           (de-module-disabled-rules)))))

(in-theory (disable alt-branch$step))

;; ======================================================================

;; 2. Specify and Prove a State Invariant

;; Conditions on the inputs

(defund alt-branch$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in     (nth 0 inputs))
       (empty-out0- (nth 1 inputs))
       (empty-out1- (nth 2 inputs))
       (data-in     (alt-branch$data-in inputs data-width))
       (go-signals  (nthcdr (alt-branch$data-ins-len data-width) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out0-)
     (booleanp empty-out1-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *alt-branch$go-num*)
     (equal inputs
            (list* full-in empty-out0- empty-out1-
                   (append data-in go-signals))))))

(defthm booleanp-alt-branch$act0
  (implies (and (alt-branch$input-format inputs data-width)
                (alt-branch$valid-st st))
           (booleanp (alt-branch$act0 inputs st data-width)))
  :hints (("Goal" :in-theory (enable alt-branch$input-format
                                     alt-branch$valid-st
                                     alt-branch$act0)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-alt-branch$act1
  (implies (and (alt-branch$input-format inputs data-width)
                (alt-branch$valid-st st))
           (booleanp (alt-branch$act1 inputs st data-width)))
  :hints (("Goal" :in-theory (enable alt-branch$input-format
                                     alt-branch$valid-st
                                     alt-branch$act1)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-alt-branch$act
  (implies (and (alt-branch$input-format inputs data-width)
                (alt-branch$valid-st st))
           (booleanp (alt-branch$act inputs st data-width)))
  :hints (("Goal" :in-theory (enable alt-branch$act)))
  :rule-classes (:rewrite :type-prescription))

(defthm alt-branch$valid-st-preserved
  (implies (and (alt-branch$input-format inputs data-width)
                (alt-branch$valid-st st))
           (alt-branch$valid-st
            (alt-branch$step inputs st data-width)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            f-sr
                            alt-branch$input-format
                            alt-branch$valid-st
                            alt-branch$step
                            alt-branch$act
                            alt-branch$act0
                            alt-branch$act1)
                           ()))))

;; A state invariant

(defund alt-branch$inv (st)
  (b* ((select (get-field *alt-branch$select* st))
       (select.s (get-field *link1$s* select))
       (select-buf (get-field *alt-branch$select-buf* st))
       (select-buf.s (get-field *link1$s* select-buf)))
    (not (equal select.s select-buf.s))))

(defthm alt-branch$inv-preserved
  (implies (and (alt-branch$input-format inputs data-width)
                (alt-branch$valid-st st)
                (alt-branch$inv st))
           (alt-branch$inv (alt-branch$step inputs st data-width)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            f-sr
                            alt-branch$input-format
                            alt-branch$valid-st
                            alt-branch$inv
                            alt-branch$step
                            alt-branch$act
                            alt-branch$act0
                            alt-branch$act1)
                           ()))))

