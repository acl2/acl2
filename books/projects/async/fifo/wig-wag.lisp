;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "alt-branch")
(include-book "alt-merge")
(include-book "../store-n")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of WW
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of WW
;;
;; Construct a DE module generator for wig-wag circuits using the link-joint
;; model.  Prove the value and state lemmas for this module generator.

(defconst *wig-wag$go-num* (+ *alt-branch$go-num*
                              *alt-merge$go-num*))

(defun wig-wag$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (mbe :logic (nfix data-size)
            :exec  data-size)))

(defun wig-wag$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (wig-wag$data-ins-len data-size)
     *wig-wag$go-num*))

;; DE module generator of WW.  The ALT-BRANCH joint in WW accepts input data
;; and places them alternately into links L0 and L1.  The ALT-MERGE joint takes
;; data alternately from links L0 and L1 and delivers them as outputs.

(module-generator
 wig-wag* (data-size)
 (si 'wig-wag data-size)
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 data-size)
                                     (sis 'go 0 *wig-wag$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-size))
 '(l0 l1 br me)
 (list
  ;; LINKS
  ;; L0
  (list 'l0
        (list* 'l0-status (sis 'd0-out 0 data-size))
        (si 'link data-size)
        (list* 'br-act0 'me-act0 (sis 'data 0 data-size)))

  ;; L1
  (list 'l1
        (list* 'l1-status (sis 'd1-out 0 data-size))
        (si 'link data-size)
        (list* 'br-act1 'me-act1 (sis 'data 0 data-size)))

  ;; JOINTS
  ;; Alt-Branch
  (list 'br
        (list* 'in-act 'br-act0 'br-act1
               (sis 'data 0 data-size))
        (si 'alt-branch data-size)
        (list* 'full-in 'l0-status 'l1-status
               (append (sis 'data-in 0 data-size)
                       (sis 'go 0 *alt-branch$go-num*))))

  ;; Alt-Merge
  (list 'me
        (list* 'out-act 'me-act0 'me-act1
               (sis 'data-out 0 data-size))
        (si 'alt-merge data-size)
        (list* 'l0-status 'l1-status 'empty-out-
               (append (sis 'd0-out 0 data-size)
                       (sis 'd1-out 0 data-size)
                       (sis 'go *alt-branch$go-num* *alt-merge$go-num*)))))

 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'wig-wag '(l0 l1 br me) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of WW.

(defund wig-wag$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (wig-wag* data-size)
        (union$ (link$netlist data-size)
                (alt-branch$netlist data-size)
                (alt-merge$netlist data-size)
                :test 'equal)))

;; Recognizer for WW

(defund wig-wag& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'wig-wag data-size) netlist)))
    (and (equal (assoc (si 'wig-wag data-size) netlist)
                (wig-wag* data-size))
         (link& subnetlist data-size)
         (alt-branch& subnetlist data-size)
         (alt-merge& subnetlist data-size))))

;; Sanity check

(local
 (defthm check-wig-wag$netlist-64
   (and (net-syntax-okp (wig-wag$netlist 64))
        (net-arity-okp (wig-wag$netlist 64))
        (wig-wag& (wig-wag$netlist 64) 64))))

;; Constraints on the state of WW

(defund wig-wag$st-format (st data-size)
  (b* ((l0 (nth *wig-wag$l0* st))
       (l1 (nth *wig-wag$l1* st)))
    (and (< 0 data-size)
         (link$st-format l0 data-size)
         (link$st-format l1 data-size))))

(defthm wig-wag$st-format=>constraint
  (implies (wig-wag$st-format st data-size)
           (posp data-size))
  :hints (("Goal" :in-theory (enable wig-wag$st-format)))
  :rule-classes :forward-chaining)

(defund wig-wag$valid-st (st data-size)
  (b* ((l0 (nth *wig-wag$l0* st))
       (l1 (nth *wig-wag$l1* st))
       (br (nth *wig-wag$br* st))
       (me (nth *wig-wag$me* st)))
    (and (wig-wag$st-format st data-size)

         (link$valid-st l0 data-size)
         (link$valid-st l1 data-size)

         (alt-branch$valid-st br)
         (alt-merge$valid-st me))))

(defthmd wig-wag$valid-st=>constraint
  (implies (wig-wag$valid-st st data-size)
           (posp data-size))
  :hints (("Goal" :in-theory (enable wig-wag$valid-st)))
  :rule-classes :forward-chaining)

(defthmd wig-wag$valid-st=>st-format
  (implies (wig-wag$valid-st st data-size)
           (wig-wag$st-format st data-size))
  :hints (("Goal" :in-theory (e/d (wig-wag$valid-st)
                                  ()))))

;; Extract the input and output signals for WW

(progn
  ;; Extract the input data

  (defun wig-wag$data-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (mbe :logic (nfix data-size)
               :exec  data-size)
          (nthcdr 2 inputs)))

  (defthm len-wig-wag$data-in
    (equal (len (wig-wag$data-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable wig-wag$data-in))

  ;; Extract the inputs for joint ALT-BRANCH

  (defund wig-wag$br-inputs (inputs st data-size)
    (b* ((full-in (nth 0 inputs))
         (data-in (wig-wag$data-in inputs data-size))
         (go-signals (nthcdr (wig-wag$data-ins-len data-size) inputs))

         (br-go-signals (take *alt-branch$go-num* go-signals))

         (l0 (nth *wig-wag$l0* st))
         (l0.s (nth *link$s* l0))
         (l1 (nth *wig-wag$l1* st))
         (l1.s (nth *link$s* l1)))

      (list* full-in (f-buf (car l0.s)) (f-buf (car l1.s))
             (append data-in br-go-signals))))

  ;; Extract the inputs for joint ALT-MERGE

  (defund wig-wag$me-inputs (inputs st data-size)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (wig-wag$data-ins-len data-size) inputs))

         (me-go-signals (take *alt-merge$go-num*
                              (nthcdr *alt-branch$go-num* go-signals)))

         (l0 (nth *wig-wag$l0* st))
         (l0.s (nth *link$s* l0))
         (l0.d (nth *link$d* l0))
         (l1 (nth *wig-wag$l1* st))
         (l1.s (nth *link$s* l1))
         (l1.d (nth *link$d* l1)))

      (list* (f-buf (car l0.s)) (f-buf (car l1.s)) empty-out-
             (append (v-threefix (strip-cars l0.d))
                     (v-threefix (strip-cars l1.d))
                     me-go-signals))))

  ;; Extract the "in-act" signal

  (defund wig-wag$in-act (inputs st data-size)
    (b* ((br-inputs (wig-wag$br-inputs inputs st data-size))
         (br (nth *wig-wag$br* st)))
      (alt-branch$act br-inputs br data-size)))

  (defthm wig-wag$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (wig-wag$in-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable wig-wag$br-inputs
                                       wig-wag$in-act))))

  ;; Extract the "out-act" signal

  (defund wig-wag$out-act (inputs st data-size)
    (b* ((me-inputs (wig-wag$me-inputs inputs st data-size))
         (me (nth *wig-wag$me* st)))
      (alt-merge$act me-inputs me data-size)))

  (defthm wig-wag$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (wig-wag$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable wig-wag$me-inputs
                                       wig-wag$out-act))))

  ;; Extract the output data

  (defund wig-wag$data-out (st)
    (b* ((l0 (nth *wig-wag$l0* st))
         (l0.d (nth *link$d* l0))
         (l1 (nth *wig-wag$l1* st))
         (l1.d (nth *link$d* l1))
         (me (nth *wig-wag$me* st))
         (me-select (nth *alt-merge$select* me))
         (me-select.d (nth *link1$d* me-select)))
      (fv-if (car me-select.d)
             (strip-cars l1.d)
             (strip-cars l0.d))))

  (defthm len-wig-wag$data-out-1
    (implies (wig-wag$st-format st data-size)
             (equal (len (wig-wag$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable wig-wag$st-format
                                       wig-wag$data-out))))

  (defthm len-wig-wag$data-out-2
    (implies (wig-wag$valid-st st data-size)
             (equal (len (wig-wag$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable wig-wag$valid-st
                                       wig-wag$data-out))))

  (defthm bvp-wig-wag$data-out
    (implies (and (wig-wag$valid-st st data-size)
                  (wig-wag$out-act inputs st data-size))
             (bvp (wig-wag$data-out st)))
    :hints (("Goal" :in-theory (enable f-and3
                                       f-and
                                       joint-act
                                       wig-wag$valid-st
                                       wig-wag$st-format
                                       wig-wag$out-act
                                       wig-wag$data-out
                                       wig-wag$me-inputs
                                       alt-merge$valid-st
                                       alt-merge$act
                                       alt-merge$act0
                                       alt-merge$act1))))

  (defun wig-wag$outputs (inputs st data-size)
    (list* (wig-wag$in-act inputs st data-size)
           (wig-wag$out-act inputs st data-size)
           (wig-wag$data-out st)))
  )

;; The value lemma for WW

(defthm wig-wag$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (wig-wag& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *wig-wag$go-num*)
                  (wig-wag$st-format st data-size))
             (equal (se (si 'wig-wag data-size) inputs st netlist)
                    (wig-wag$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'wig-wag data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            wig-wag&
                            wig-wag*$destructure
                            wig-wag$data-in
                            wig-wag$st-format
                            wig-wag$in-act
                            wig-wag$out-act
                            wig-wag$data-out
                            wig-wag$br-inputs
                            wig-wag$me-inputs)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of WW.

(defun wig-wag$step (inputs st data-size)
  (b* ((data-in (wig-wag$data-in inputs data-size))

       (l0 (nth *wig-wag$l0* st))
       (l1 (nth *wig-wag$l1* st))
       (br (nth *wig-wag$br* st))
       (me (nth *wig-wag$me* st))

       (br-inputs (wig-wag$br-inputs inputs st data-size))
       (me-inputs (wig-wag$me-inputs inputs st data-size))

       (br-act0 (alt-branch$act0 br-inputs br data-size))
       (br-act1 (alt-branch$act1 br-inputs br data-size))
       (me-act0 (alt-merge$act0 me-inputs me data-size))
       (me-act1 (alt-merge$act1 me-inputs me data-size))

       (l0-inputs (list* br-act0 me-act0 data-in))
       (l1-inputs (list* br-act1 me-act1 data-in)))
    (list
     ;; L0
     (link$step l0-inputs l0 data-size)
     ;; L1
     (link$step l1-inputs l1 data-size)

     ;; Joint ALT-BRANCH
     (alt-branch$step br-inputs br data-size)
     ;; Joint ALT-MERGE
     (alt-merge$step me-inputs me data-size))))

;; The state lemma for WW

(defthm wig-wag$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (wig-wag& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *wig-wag$go-num*)
                  (wig-wag$st-format st data-size))
             (equal (de (si 'wig-wag data-size) inputs st netlist)
                    (wig-wag$step inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'wig-wag data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            wig-wag&
                            wig-wag*$destructure
                            wig-wag$st-format
                            wig-wag$data-in
                            wig-wag$br-inputs
                            wig-wag$me-inputs)
                           (de-module-disabled-rules)))))

(in-theory (disable wig-wag$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund wig-wag$input-format (inputs data-size)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-size))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (wig-wag$data-in inputs data-size))
       (go-signals (nthcdr (wig-wag$data-ins-len data-size) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *wig-wag$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(local
 (defthm wig-wag$input-format=>br$input-format
   (implies (and (wig-wag$input-format inputs data-size)
                 (wig-wag$valid-st st data-size))
            (alt-branch$input-format
             (wig-wag$br-inputs inputs st data-size)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (wig-wag$input-format
                             alt-branch$input-format
                             alt-branch$data-in
                             wig-wag$valid-st
                             wig-wag$st-format
                             wig-wag$br-inputs)
                            ())))))

(local
 (defthm wig-wag$input-format=>me$input-format
   (implies (and (wig-wag$input-format inputs data-size)
                 (wig-wag$valid-st st data-size))
            (alt-merge$input-format
             (wig-wag$me-inputs inputs st data-size)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (wig-wag$input-format
                             alt-merge$input-format
                             alt-merge$data0-in
                             alt-merge$data1-in
                             wig-wag$valid-st
                             wig-wag$st-format
                             wig-wag$me-inputs)
                            ())))))

(defthm booleanp-wig-wag$in-act
  (implies (and (wig-wag$input-format inputs data-size)
                (wig-wag$valid-st st data-size))
           (booleanp (wig-wag$in-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (enable wig-wag$valid-st
                              wig-wag$in-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-wig-wag$out-act
  (implies (and (wig-wag$input-format inputs data-size)
                (wig-wag$valid-st st data-size))
           (booleanp (wig-wag$out-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (enable wig-wag$valid-st
                              wig-wag$out-act)))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma wig-wag)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for WW that extracts the future output sequence from
;; the current state.

(defund wig-wag$extract (st)
  (b* ((l0 (nth *wig-wag$l0* st))
       (l1 (nth *wig-wag$l1* st))
       (me (nth *wig-wag$me* st))

       (me-select       (nth *alt-merge$select* me))
       (me-select.s     (nth *link1$s* me-select))
       (me-select.d     (nth *link1$d* me-select))
       (me-select-buf   (nth *alt-merge$select-buf* me))
       (me-select-buf.d (nth *link1$d* me-select-buf))
       (valid-me-select (if (fullp me-select.s)
                            (car me-select.d)
                          (car me-select-buf.d))))

    (if valid-me-select
        (extract-valid-data (list l0 l1))
      (extract-valid-data (list l1 l0)))))

(defthm wig-wag$extract-not-empty
  (implies (and (wig-wag$out-act inputs st data-size)
                (wig-wag$valid-st st data-size))
           (< 0 (len (wig-wag$extract st))))
  :hints (("Goal"
           :in-theory (e/d (f-and3
                            alt-merge$act
                            alt-merge$act0
                            alt-merge$act1
                            wig-wag$me-inputs
                            wig-wag$valid-st
                            wig-wag$extract
                            wig-wag$out-act)
                           ())))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund wig-wag$inv (st)
    (b* ((l0 (nth *wig-wag$l0* st))
         (l0.s (nth *link$s* l0))
         (l1 (nth *wig-wag$l1* st))
         (l1.s (nth *link$s* l1))
         (br (nth *wig-wag$br* st))
         (me (nth *wig-wag$me* st))

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
           (or (and (equal l0.s l1.s)
                    (equal valid-br-select valid-me-select))
               (and (fullp l0.s)
                    (emptyp l1.s)
                    valid-br-select
                    (not valid-me-select))
               (and (emptyp l0.s)
                    (fullp l1.s)
                    (not valid-br-select)
                    valid-me-select)))))

  (local
   (defthm wig-wag$input-format-lemma-1
     (implies (wig-wag$input-format inputs data-size)
              (booleanp (nth 0 inputs)))
     :hints (("Goal" :in-theory (enable wig-wag$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm wig-wag$input-format-lemma-2
     (implies (wig-wag$input-format inputs data-size)
              (booleanp (nth 1 inputs)))
     :hints (("Goal" :in-theory (enable wig-wag$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm wig-wag$input-format-lemma-3
     (implies (and (wig-wag$input-format inputs data-size)
                   (nth 0 inputs))
              (bvp (wig-wag$data-in inputs data-size)))
     :hints (("Goal" :in-theory (enable wig-wag$input-format)))))

  (defthm wig-wag$inv-preserved
    (implies (and (wig-wag$input-format inputs data-size)
                  (wig-wag$valid-st st data-size)
                  (wig-wag$inv st))
             (wig-wag$inv (wig-wag$step inputs st data-size)))
    :hints (("Goal"
             :in-theory (e/d (f-sr
                              wig-wag$valid-st
                              wig-wag$inv
                              wig-wag$step
                              wig-wag$in-act
                              wig-wag$out-act
                              wig-wag$br-inputs
                              wig-wag$me-inputs
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
                             ()))))
  )

;; The extracted next-state function for WW.  Note that this function avoids
;; exploring the internal computation of WW.

(defund wig-wag$extracted-step (inputs st data-size)
  (b* ((data (wig-wag$data-in inputs data-size))
       (extracted-st (wig-wag$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (wig-wag$out-act inputs st data-size) t)
      (cond
       ((equal (wig-wag$in-act inputs st data-size) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (wig-wag$in-act inputs st data-size) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(defthm wig-wag$extracted-step-correct
  (b* ((next-st (wig-wag$step inputs st data-size)))
    (implies (and (wig-wag$input-format inputs data-size)
                  (wig-wag$valid-st st data-size)
                  (wig-wag$inv st))
             (equal (wig-wag$extract next-st)
                    (wig-wag$extracted-step inputs st data-size))))
  :hints (("Goal"
           :in-theory (e/d (f-sr
                            joint-act
                            wig-wag$extracted-step
                            wig-wag$valid-st
                            wig-wag$inv
                            wig-wag$step
                            wig-wag$in-act
                            wig-wag$out-act
                            wig-wag$extract
                            wig-wag$br-inputs
                            wig-wag$me-inputs
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
                           ()))))

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that wig-wag$valid-st is an invariant.

(encapsulate
  ()

  (local
   (defthm wig-wag$br-act0-inactive
     (implies (equal (nth *link$s*
                          (nth *wig-wag$l0* st))
                     '(t))
              (not (alt-branch$act0
                    (wig-wag$br-inputs inputs st data-size)
                    (nth *wig-wag$br* st)
                    data-size)))
     :hints (("Goal"
              :in-theory (enable wig-wag$br-inputs)))))

  (local
   (defthm wig-wag$br-act1-inactive
     (implies (equal (nth *link$s*
                          (nth *wig-wag$l1* st))
                     '(t))
              (not (alt-branch$act1
                    (wig-wag$br-inputs inputs st data-size)
                    (nth *wig-wag$br* st)
                    data-size)))
     :hints (("Goal"
              :in-theory (enable wig-wag$br-inputs)))))

  (local
   (defthm wig-wag$me-act0-inactive
     (implies (equal (nth *link$s*
                          (nth *wig-wag$l0* st))
                     '(nil))
              (not (alt-merge$act0
                    (wig-wag$me-inputs inputs st data-size)
                    (nth *wig-wag$me* st)
                    data-size)))
     :hints (("Goal"
              :in-theory (enable wig-wag$me-inputs)))))

  (local
   (defthm wig-wag$me-act1-inactive
     (implies (equal (nth *link$s*
                          (nth *wig-wag$l1* st))
                     '(nil))
              (not (alt-merge$act1
                    (wig-wag$me-inputs inputs st data-size)
                    (nth *wig-wag$me* st)
                    data-size)))
     :hints (("Goal"
              :in-theory (enable wig-wag$me-inputs)))))

  (local
   (defthm wig-wag$br-acts-inactive
     (b* ((br-inputs (wig-wag$br-inputs inputs st data-size))
          (br (nth *wig-wag$br* st)))
       (implies (not (nth 0 inputs))
                (and (not (alt-branch$act0 br-inputs br data-size))
                     (not (alt-branch$act1 br-inputs br data-size)))))
     :hints (("Goal" :in-theory (enable wig-wag$br-inputs)))))

  (defthm wig-wag$valid-st-preserved
    (implies (and (wig-wag$input-format inputs data-size)
                  (wig-wag$valid-st st data-size))
             (wig-wag$valid-st (wig-wag$step inputs st data-size)
                               data-size))
    :hints (("Goal"
             :use (wig-wag$input-format=>br$input-format
                   wig-wag$input-format=>me$input-format)
             :in-theory (e/d (f-sr
                              wig-wag$input-format
                              wig-wag$valid-st
                              wig-wag$st-format
                              wig-wag$step)
                             (wig-wag$input-format=>br$input-format
                              wig-wag$input-format=>me$input-format)))))
  )

(defthm wig-wag$extract-lemma
  (implies (and (wig-wag$valid-st st data-size)
                (wig-wag$out-act inputs st data-size))
           (equal (list (wig-wag$data-out st))
                  (nthcdr (1- (len (wig-wag$extract st)))
                          (wig-wag$extract st))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable f-and3
                              f-and
                              joint-act
                              wig-wag$valid-st
                              wig-wag$extract
                              wig-wag$out-act
                              wig-wag$data-out
                              wig-wag$me-inputs
                              alt-merge$valid-st
                              alt-merge$act
                              alt-merge$act0
                              alt-merge$act1))))

;; Extract the accepted input sequence

(seq-gen wig-wag in in-act 0
         (wig-wag$data-in inputs data-size))

;; Extract the valid output sequence

(seq-gen wig-wag out out-act 1
         (wig-wag$data-out st)
         :netlist-data (nthcdr 2 outputs))

;; The multi-step input-output relationship

(in-out-stream-lemma wig-wag :inv t)

