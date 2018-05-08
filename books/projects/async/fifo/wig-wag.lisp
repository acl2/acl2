;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; April 2018

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
;;; 2. Specify the Final State of WW After An N-Step Execution
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of WW
;;
;; Construct a DE module generator for a wig-wag circuit, WW, using the
;; link-joint model.  Prove the value and state lemmas for this module
;; generator.

(defconst *wig-wag$go-num* (+ *alt-branch$go-num*
                             *alt-merge$go-num*))
(defconst *wig-wag$st-len* 4)

(defun wig-wag$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun wig-wag$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (wig-wag$data-ins-len data-width)
     *wig-wag$go-num*))

;; DE module generator of WW.  The ALT-BRANCH joint in WW accepts input data
;; and places them alternately into links L0 and L1.  The ALT-MERGE joint takes
;; data alternately from links L0 and L1 and delivers them as outputs.

(module-generator
 wig-wag* (data-width)
 (si 'wig-wag data-width)
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 data-width)
                                     (sis 'go 0 *wig-wag$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-width))
 '(l0 l1 br me)
 (list
  ;; LINKS
  ;; L0
  (list 'l0
        (list* 'l0-status (sis 'd0-out 0 data-width))
        (si 'link data-width)
        (list* 'br-act0 'me-act0 (sis 'data 0 data-width)))

  ;; L1
  (list 'l1
        (list* 'l1-status (sis 'd1-out 0 data-width))
        (si 'link data-width)
        (list* 'br-act1 'me-act1 (sis 'data 0 data-width)))

  ;; JOINTS
  ;; Alt-Branch
  (list 'br
        (list* 'in-act 'br-act0 'br-act1
               (sis 'data 0 data-width))
        (si 'alt-branch data-width)
        (list* 'full-in 'l0-status 'l1-status
               (append (sis 'data-in 0 data-width)
                       (sis 'go 0 *alt-branch$go-num*))))

  ;; Alt-Merge
  (list 'me
        (list* 'out-act 'me-act0 'me-act1
               (sis 'data-out 0 data-width))
        (si 'alt-merge data-width)
        (list* 'l0-status 'l1-status 'empty-out-
               (append (sis 'd0-out 0 data-width)
                       (sis 'd1-out 0 data-width)
                       (sis 'go *alt-branch$go-num* *alt-merge$go-num*)))))

 :guard (natp data-width))

(make-event
 `(progn
    ,@(state-accessors-gen 'wig-wag '(l0 l1 br me) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of WW.

(defun wig-wag$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (wig-wag* data-width)
        (union$ (link$netlist data-width)
                (alt-branch$netlist data-width)
                (alt-merge$netlist data-width)
                :test 'equal)))

;; Recognizer for WW

(defund wig-wag& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (and (equal (assoc (si 'wig-wag data-width) netlist)
              (wig-wag* data-width))
       (b* ((netlist (delete-to-eq (si 'wig-wag data-width) netlist)))
         (and (link& netlist data-width)
              (alt-branch& netlist data-width)
              (alt-merge& netlist data-width)))))

;; Sanity check

(local
 (defthm check-wig-wag$netlist-64
   (and (net-syntax-okp (wig-wag$netlist 64))
        (net-arity-okp (wig-wag$netlist 64))
        (wig-wag& (wig-wag$netlist 64) 64))))

;; Constraints on the state of WW

(defund wig-wag$st-format (st data-width)
  (b* ((l0 (get-field *wig-wag$l0* st))
       (l1 (get-field *wig-wag$l1* st)))
    (and (< 0 data-width)
         (link$st-format l0 data-width)
         (link$st-format l1 data-width))))

(defthm wig-wag$st-format=>posp-data-width
  (implies (wig-wag$st-format st data-width)
           (posp data-width))
  :hints (("Goal" :in-theory (enable wig-wag$st-format)))
  :rule-classes :forward-chaining)

(defund wig-wag$valid-st (st data-width)
  (b* ((l0 (get-field *wig-wag$l0* st))
       (l1 (get-field *wig-wag$l1* st))
       (br (get-field *wig-wag$br* st))
       (me (get-field *wig-wag$me* st)))
    (and (wig-wag$st-format st data-width)

         (link$valid-st l0 data-width)
         (link$valid-st l1 data-width)

         (alt-branch$valid-st br)
         (alt-merge$valid-st me))))

(defthmd wig-wag$valid-st=>posp-data-width
  (implies (wig-wag$valid-st st data-width)
           (posp data-width))
  :hints (("Goal" :in-theory (enable wig-wag$valid-st)))
  :rule-classes :forward-chaining)

;; Extract the input and output signals from WW

(progn
  ;; Extract the input data

  (defun wig-wag$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 2 inputs)))

  (defthm len-wig-wag$data-in
    (equal (len (wig-wag$data-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable wig-wag$data-in))

  ;; Extract the inputs for the alt-branch joint

  (defund wig-wag$br-inputs (inputs st data-width)
    (b* ((full-in (nth 0 inputs))
         (data-in (wig-wag$data-in inputs data-width))
         (go-signals (nthcdr (wig-wag$data-ins-len data-width) inputs))

         (br-go-signals (take *alt-branch$go-num* go-signals))

         (l0 (get-field *wig-wag$l0* st))
         (l0.s (get-field *link$s* l0))
         (l1 (get-field *wig-wag$l1* st))
         (l1.s (get-field *link$s* l1)))

      (list* full-in (f-buf (car l0.s)) (f-buf (car l1.s))
             (append data-in br-go-signals))))

  ;; Extract the inputs for the alt-merge joint

  (defund wig-wag$me-inputs (inputs st data-width)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (wig-wag$data-ins-len data-width) inputs))

         (me-go-signals (nthcdr *alt-branch$go-num* go-signals))

         (l0 (get-field *wig-wag$l0* st))
         (l0.s (get-field *link$s* l0))
         (l0.d (get-field *link$d* l0))
         (l1 (get-field *wig-wag$l1* st))
         (l1.s (get-field *link$s* l1))
         (l1.d (get-field *link$d* l1)))

      (list* (f-buf (car l0.s)) (f-buf (car l1.s)) empty-out-
             (append (v-threefix (strip-cars l0.d))
                     (v-threefix (strip-cars l1.d))
                     me-go-signals))))

  ;; Extract the "in-act" signal

  (defund wig-wag$in-act (inputs st data-width)
    (b* ((br-inputs (wig-wag$br-inputs inputs st data-width))
         (br (get-field *wig-wag$br* st)))
      (alt-branch$act br-inputs br data-width)))

  ;; Extract the "out-act" signal

  (defund wig-wag$out-act (inputs st data-width)
    (b* ((me-inputs (wig-wag$me-inputs inputs st data-width))
         (me (get-field *wig-wag$me* st)))
      (alt-merge$act me-inputs me data-width)))

  ;; Extract the output data

  (defund wig-wag$data-out (st)
    (b* ((l0 (get-field *wig-wag$l0* st))
         (l0.d (get-field *link$d* l0))
         (l1 (get-field *wig-wag$l1* st))
         (l1.d (get-field *link$d* l1))
         (me (get-field *wig-wag$me* st))
         (me-select (get-field *alt-merge$select* me))
         (me-select.d (get-field *link1$d* me-select)))
      (fv-if (car me-select.d)
             (strip-cars l1.d)
             (strip-cars l0.d))))

  (defthm len-wig-wag$data-out-1
    (implies (wig-wag$st-format st data-width)
             (equal (len (wig-wag$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable wig-wag$st-format
                                       wig-wag$data-out))))

  (defthm len-wig-wag$data-out-2
    (implies (wig-wag$valid-st st data-width)
             (equal (len (wig-wag$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable wig-wag$valid-st
                                       wig-wag$data-out))))

  (defthm bvp-wig-wag$data-out
    (implies (and (wig-wag$valid-st st data-width)
                  (wig-wag$out-act inputs st data-width))
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
  )

(not-primp-lemma wig-wag) ;; Prove that WW is not a DE primitive.

;; The value lemma for WW

(defthmd wig-wag$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (wig-wag& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *wig-wag$go-num*)
                  (wig-wag$st-format st data-width))
             (equal (se (si 'wig-wag data-width) inputs st netlist)
                    (list* (wig-wag$in-act inputs st data-width)
                           (wig-wag$out-act inputs st data-width)
                           (wig-wag$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'wig-wag data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            not-primp-wig-wag
                            wig-wag&
                            wig-wag*$destructure
                            wig-wag$data-in
                            alt-branch$value
                            alt-merge$value
                            link$value
                            wig-wag$st-format
                            wig-wag$in-act
                            wig-wag$out-act
                            wig-wag$data-out
                            wig-wag$br-inputs
                            wig-wag$me-inputs)
                           ((wig-wag*)
                            de-module-disabled-rules)))))

;; This function specifies the next state of WW.

(defun wig-wag$step (inputs st data-width)
  (b* ((data-in (wig-wag$data-in inputs data-width))

       (l0 (get-field *wig-wag$l0* st))
       (l1 (get-field *wig-wag$l1* st))
       (br (get-field *wig-wag$br* st))
       (me (get-field *wig-wag$me* st))

       (br-inputs (wig-wag$br-inputs inputs st data-width))
       (me-inputs (wig-wag$me-inputs inputs st data-width))

       (br-act0 (alt-branch$act0 br-inputs br data-width))
       (br-act1 (alt-branch$act1 br-inputs br data-width))
       (me-act0 (alt-merge$act0 me-inputs me data-width))
       (me-act1 (alt-merge$act1 me-inputs me data-width))

       (l0-inputs (list* br-act0 me-act0 data-in))
       (l1-inputs (list* br-act1 me-act1 data-in)))
    (list
     ;; L0
     (link$step l0-inputs l0 data-width)
     ;; L1
     (link$step l1-inputs l1 data-width)

     ;; Joint alt-branch
     (alt-branch$step br-inputs br data-width)
     ;; Joint alt-merge
     (alt-merge$step me-inputs me data-width))))

(defthm len-of-wig-wag$step
  (equal (len (wig-wag$step inputs st data-width))
         *wig-wag$st-len*))

;; The state lemma for WW

(defthmd wig-wag$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (wig-wag& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *wig-wag$go-num*)
                  (wig-wag$st-format st data-width))
             (equal (de (si 'wig-wag data-width) inputs st netlist)
                    (wig-wag$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'wig-wag data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            not-primp-wig-wag
                            wig-wag&
                            wig-wag*$destructure
                            wig-wag$st-format
                            wig-wag$data-in
                            wig-wag$br-inputs
                            wig-wag$me-inputs
                            alt-branch$value alt-branch$state
                            alt-merge$value alt-merge$state
                            link$value link$state)
                           ((wig-wag*)
                            de-module-disabled-rules)))))

(in-theory (disable wig-wag$step))

;; ======================================================================

;; 2. Specify the Final State of WW After An N-Step Execution

;; WW simulator

(progn
  (defun wig-wag$map-to-links (st)
    (b* ((l0 (get-field *wig-wag$l0* st))
         (l1 (get-field *wig-wag$l1* st))
         (br (get-field *wig-wag$br* st))
         (me (get-field *wig-wag$me* st)))
      (append (list (cons 'alt-branch (alt-branch$map-to-links br)))
              (map-to-links (list (list* 'l0 l0)
                                  (list* 'l1 l1)))
              (list (cons 'alt-merge (alt-merge$map-to-links me))))))

  (defun wig-wag$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (wig-wag$map-to-links (car x))
            (wig-wag$map-to-links-list (cdr x)))))

  (defund wig-wag$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (wig-wag$ins-len data-width))
         ((mv inputs-lst state)
          (signal-vals-gen num-signals n state nil))
         ;;(- (cw "~x0~%" inputs-lst))
         (full '(t))
         (empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (br (list (list full '(nil))
                   (list empty '(x))))
         (me (list (list full '(nil))
                   (list empty '(x))))
         (st (list (list empty invalid-data)
                   (list empty invalid-data)
                   br me)))
      (mv (pretty-list
           (remove-dup-neighbors
            (wig-wag$map-to-links-list
             (de-sim-list (si 'wig-wag data-width)
                          inputs-lst
                          st
                          (wig-wag$netlist data-width))))
           0)
          state)))
  )

;; Conditions on the inputs

(defund wig-wag$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (wig-wag$data-in inputs data-width))
       (go-signals (nthcdr (wig-wag$data-ins-len data-width) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *wig-wag$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(defthmd len-of-wig-wag$inputs
  (implies (wig-wag$input-format inputs data-width)
           (equal (len inputs) (wig-wag$ins-len data-width)))
  :hints (("Goal" :in-theory (enable wig-wag$input-format))))

(local
 (defthm wig-wag$input-format=>br$input-format
   (implies (and (wig-wag$input-format inputs data-width)
                 (wig-wag$valid-st st data-width))
            (alt-branch$input-format
             (wig-wag$br-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (wig-wag$input-format
                             alt-branch$input-format
                             alt-branch$data-in
                             wig-wag$valid-st
                             wig-wag$st-format
                             wig-wag$br-inputs)
                            (nthcdr
                             take-of-too-many))))))

(local
 (defthm wig-wag$input-format=>me$input-format
   (implies (and (wig-wag$input-format inputs data-width)
                 (wig-wag$valid-st st data-width))
            (alt-merge$input-format
             (wig-wag$me-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :use len-of-wig-wag$inputs
            :in-theory (e/d (wig-wag$input-format
                             alt-merge$input-format
                             alt-merge$data-in0
                             alt-merge$data-in1
                             wig-wag$valid-st
                             wig-wag$st-format
                             wig-wag$me-inputs)
                            (nthcdr
                             take-of-too-many))))))

(simulate-lemma wig-wag)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for WW that extracts the future output sequence from
;; the current state.

(defund wig-wag$extract (st)
  (b* ((l0 (get-field *wig-wag$l0* st))
       (l1 (get-field *wig-wag$l1* st))
       (me (get-field *wig-wag$me* st))

       (me-select       (get-field *alt-merge$select* me))
       (me-select.s     (get-field *link1$s* me-select))
       (me-select.d     (get-field *link1$d* me-select))
       (me-select-buf   (get-field *alt-merge$select-buf* me))
       (me-select-buf.d (get-field *link1$d* me-select-buf))
       (valid-me-select (if (fullp me-select.s)
                            (car me-select.d)
                          (car me-select-buf.d))))

    (if valid-me-select
        (extract-valid-data (list l0 l1))
      (extract-valid-data (list l1 l0)))))

(defthm wig-wag$extract-not-empty
  (implies (and (wig-wag$out-act inputs st data-width)
                (wig-wag$valid-st st data-width))
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
                           (nfix))))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund wig-wag$inv (st)
    (b* ((l0 (get-field *wig-wag$l0* st))
         (l0.s (get-field *link$s* l0))
         (l1 (get-field *wig-wag$l1* st))
         (l1.s (get-field *link$s* l1))
         (br (get-field *wig-wag$br* st))
         (me (get-field *wig-wag$me* st))

         (br-select       (get-field *alt-branch$select* br))
         (br-select.s     (get-field *link1$s* br-select))
         (br-select.d     (get-field *link1$d* br-select))
         (br-select-buf   (get-field *alt-branch$select-buf* br))
         (br-select-buf.d (get-field *link1$d* br-select-buf))
         (valid-br-select (if (fullp br-select.s)
                              (car br-select.d)
                            (car br-select-buf.d)))

         (me-select       (get-field *alt-merge$select* me))
         (me-select.s     (get-field *link1$s* me-select))
         (me-select.d     (get-field *link1$d* me-select))
         (me-select-buf   (get-field *alt-merge$select-buf* me))
         (me-select-buf.d (get-field *link1$d* me-select-buf))
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

  (defthm wig-wag$inv-preserved
    (implies (and (wig-wag$input-format inputs data-width)
                  (wig-wag$valid-st st data-width)
                  (wig-wag$inv st))
             (wig-wag$inv (wig-wag$step inputs st data-width)))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              wig-wag$input-format
                              wig-wag$valid-st
                              wig-wag$st-format
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
                              alt-merge$act1
                              f-sr)
                             (nfix
                              nthcdr
                              len
                              true-listp
                              take-of-too-many
                              open-v-threefix)))))
  )

;; The extracted next-state function for WW.  Note that this function avoids
;; exploring the internal computation of WW.

(defund wig-wag$extracted-step (inputs st data-width)
  (b* ((data-in (wig-wag$data-in inputs data-width))
       (extracted-st (wig-wag$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (wig-wag$out-act inputs st data-width) t)
      (cond
       ((equal (wig-wag$in-act inputs st data-width) t)
        (cons data-in (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (wig-wag$in-act inputs st data-width) t)
          (cons data-in extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(defthm wig-wag$extracted-step-correct
  (b* ((next-st (wig-wag$step inputs st data-width)))
    (implies (and (wig-wag$input-format inputs data-width)
                  (wig-wag$valid-st st data-width)
                  (wig-wag$inv st))
             (equal (wig-wag$extract next-st)
                    (wig-wag$extracted-step inputs st data-width))))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            f-if
                            wig-wag$extracted-step
                            wig-wag$input-format
                            wig-wag$valid-st
                            wig-wag$st-format
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
                           (nthcdr
                            len-nthcdr
                            3v-fix
                            true-listp
                            pairlis$
                            strip-cars
                            default-car
                            default-cdr
                            default-+-1
                            default-+-2)))))

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Extract the accepted input sequence

(defun wig-wag$in-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (wig-wag$in-act inputs st data-width) t)
          (append (wig-wag$in-seq (cdr inputs-lst)
                                 (wig-wag$step inputs st data-width)
                                 data-width
                                 (1- n))
                  (list (wig-wag$data-in inputs data-width)))
        (wig-wag$in-seq (cdr inputs-lst)
                       (wig-wag$step inputs st data-width)
                       data-width
                       (1- n))))))

;; Extract the valid output sequence

(defun wig-wag$out-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (wig-wag$out-act inputs st data-width) t)
          (append (wig-wag$out-seq (cdr inputs-lst)
                                  (wig-wag$step inputs st data-width)
                                  data-width
                                  (1- n))
                  (list (wig-wag$data-out st)))
        (wig-wag$out-seq (cdr inputs-lst)
                        (wig-wag$step inputs st data-width)
                        data-width
                        (1- n))))))

;; Input-output sequence simulator

(defund wig-wag$in-out-seq-sim (data-width n state)
  (declare (xargs :guard (and (natp data-width)
                              (natp n))
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals (wig-wag$ins-len data-width))
       ((mv inputs-lst state)
        (signal-vals-gen num-signals n state nil))
       (full '(t))
       (empty '(nil))
       (invalid-data (make-list data-width :initial-element '(x)))
       (br (list (list full '(nil))
                 (list empty '(x))))
       (me (list (list full '(nil))
                 (list empty '(x))))
       (st (list (list empty invalid-data)
                 (list empty invalid-data)
                 br me)))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-lst
                   (wig-wag$in-seq inputs-lst st data-width n))))
      (list (cons 'out-seq
                  (v-to-nat-lst
                   (wig-wag$out-seq inputs-lst st data-width n)))))
     state)))

;; Prove that wig-wag$valid-st is an invariant.

(encapsulate
  ()

  (local
   (defthm booleanp-wig-wag$br-act0
     (implies (and (booleanp (nth 0 inputs))
                   (or (equal (nth *link$s*
                                   (nth *wig-wag$l0* st))
                              '(t))
                       (equal (nth *link$s*
                                   (nth *wig-wag$l0* st))
                              '(nil)))
                   (or (equal (nth *link$s*
                                   (nth *wig-wag$l1* st))
                              '(t))
                       (equal (nth *link$s*
                                   (nth *wig-wag$l1* st))
                              '(nil)))
                   (alt-branch$valid-st (nth *wig-wag$br* st)))
              (booleanp
               (alt-branch$act0 (wig-wag$br-inputs inputs st data-width)
                                (nth *wig-wag$br* st)
                                data-width)))
     :hints (("Goal" :in-theory (enable get-field
                                        wig-wag$br-inputs
                                        alt-branch$valid-st
                                        alt-branch$act0
                                        alt-branch$act)))
     :rule-classes :type-prescription))

  (local
   (defthm booleanp-wig-wag$br-act1
     (implies (and (booleanp (nth 0 inputs))
                   (or (equal (nth *link$s*
                                   (nth *wig-wag$l0* st))
                              '(t))
                       (equal (nth *link$s*
                                   (nth *wig-wag$l0* st))
                              '(nil)))
                   (or (equal (nth *link$s*
                                   (nth *wig-wag$l1* st))
                              '(t))
                       (equal (nth *link$s*
                                   (nth *wig-wag$l1* st))
                              '(nil)))
                   (alt-branch$valid-st (nth *wig-wag$br* st)))
              (booleanp
               (alt-branch$act1 (wig-wag$br-inputs inputs st data-width)
                                (nth *wig-wag$br* st)
                                data-width)))
     :hints (("Goal" :in-theory (enable get-field
                                        wig-wag$br-inputs
                                        alt-branch$valid-st
                                        alt-branch$act1
                                        alt-branch$act)))
     :rule-classes :type-prescription))

  (local
   (defthm booleanp-wig-wag$me-act0
     (implies (and (booleanp (nth 1 inputs))
                   (or (equal (nth *link$s*
                                   (nth *wig-wag$l0* st))
                              '(t))
                       (equal (nth *link$s*
                                   (nth *wig-wag$l0* st))
                              '(nil)))
                   (or (equal (nth *link$s*
                                   (nth *wig-wag$l1* st))
                              '(t))
                       (equal (nth *link$s*
                                   (nth *wig-wag$l1* st))
                              '(nil)))
                   (alt-merge$valid-st (nth *wig-wag$me* st)))
              (booleanp
               (alt-merge$act0 (wig-wag$me-inputs inputs st data-width)
                               (nth *wig-wag$me* st)
                               data-width)))
     :hints (("Goal" :in-theory (enable get-field
                                        f-and3
                                        wig-wag$me-inputs
                                        alt-merge$valid-st
                                        alt-merge$act0
                                        alt-merge$act)))
     :rule-classes :type-prescription))

  (local
   (defthm booleanp-wig-wag$me-act1
     (implies (and (booleanp (nth 1 inputs))
                   (or (equal (nth *link$s*
                                   (nth *wig-wag$l0* st))
                              '(t))
                       (equal (nth *link$s*
                                   (nth *wig-wag$l0* st))
                              '(nil)))
                   (or (equal (nth *link$s*
                                   (nth *wig-wag$l1* st))
                              '(t))
                       (equal (nth *link$s*
                                   (nth *wig-wag$l1* st))
                              '(nil)))
                   (alt-merge$valid-st (nth *wig-wag$me* st)))
              (booleanp
               (alt-merge$act1 (wig-wag$me-inputs inputs st data-width)
                               (nth *wig-wag$me* st)
                               data-width)))
     :hints (("Goal" :in-theory (enable get-field
                                        f-and3
                                        wig-wag$me-inputs
                                        alt-merge$valid-st
                                        alt-merge$act1
                                        alt-merge$act)))
     :rule-classes :type-prescription))

  (local
   (defthm wig-wag$br-act0-nil
     (implies (and (equal (nth *link$s*
                               (nth *wig-wag$l0* st))
                          '(t))
                   (alt-branch$valid-st (nth *wig-wag$br* st)))
              (not (alt-branch$act0
                    (wig-wag$br-inputs inputs st data-width)
                    (nth *wig-wag$br* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 f-if
                                 wig-wag$br-inputs
                                 alt-branch$valid-st
                                 alt-branch$act0
                                 alt-branch$act)))))

  (local
   (defthm wig-wag$br-act1-nil
     (implies (and (equal (nth *link$s*
                               (nth *wig-wag$l1* st))
                          '(t))
                   (alt-branch$valid-st (nth *wig-wag$br* st)))
              (not (alt-branch$act1
                    (wig-wag$br-inputs inputs st data-width)
                    (nth *wig-wag$br* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 f-if
                                 wig-wag$br-inputs
                                 alt-branch$valid-st
                                 alt-branch$act1
                                 alt-branch$act)))))

  (local
   (defthm wig-wag$me-act0-nil
     (implies (and (equal (nth *link$s*
                               (nth *wig-wag$l0* st))
                          '(nil))
                   (alt-merge$valid-st (nth *wig-wag$me* st)))
              (not (alt-merge$act0
                    (wig-wag$me-inputs inputs st data-width)
                    (nth *wig-wag$me* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 f-and3
                                 f-if
                                 wig-wag$me-inputs
                                 alt-merge$valid-st
                                 alt-merge$act0
                                 alt-merge$act)))))

  (local
   (defthm wig-wag$me-act1-nil
     (implies (and (equal (nth *link$s*
                               (nth *wig-wag$l1* st))
                          '(nil))
                   (alt-merge$valid-st (nth *wig-wag$me* st)))
              (not (alt-merge$act1
                    (wig-wag$me-inputs inputs st data-width)
                    (nth *wig-wag$me* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 f-and3
                                 f-if
                                 wig-wag$me-inputs
                                 alt-merge$valid-st
                                 alt-merge$act1
                                 alt-merge$act)))))

  (local
   (defthm wig-wag$valid-st-preserved-aux
     (b* ((br-inputs (wig-wag$br-inputs inputs st data-width))
          (br (nth *wig-wag$br* st)))
       (implies (not (nth 0 inputs))
                (and (not (alt-branch$act0 br-inputs br data-width))
                     (not (alt-branch$act1 br-inputs br data-width)))))
     :hints (("Goal" :in-theory (enable wig-wag$br-inputs
                                        alt-branch$act0
                                        alt-branch$act1)))))

  (defthm wig-wag$valid-st-preserved
    (implies (and (wig-wag$input-format inputs data-width)
                  (wig-wag$valid-st st data-width))
             (wig-wag$valid-st (wig-wag$step inputs st data-width)
                               data-width))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              wig-wag$input-format
                              wig-wag$valid-st
                              wig-wag$st-format
                              wig-wag$step
                              wig-wag$in-act
                              wig-wag$out-act
                              alt-branch$act
                              f-sr)
                             (if*
                              nthcdr
                              acl2::true-listp-append)))))
  )

(defthm wig-wag$extract-lemma
  (implies (and (wig-wag$valid-st st data-width)
                (equal n (1- (len (wig-wag$extract st))))
                (wig-wag$out-act inputs st data-width))
           (equal (append
                   (take n (wig-wag$extract st))
                   (list (wig-wag$data-out st)))
                  (wig-wag$extract st)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable f-and3
                              f-and
                              joint-act
                              wig-wag$valid-st
                              wig-wag$st-format
                              wig-wag$extract
                              wig-wag$out-act
                              wig-wag$data-out
                              wig-wag$me-inputs
                              alt-merge$valid-st
                              alt-merge$act
                              alt-merge$act0
                              alt-merge$act1))))

(in-out-stream-lemma wig-wag :inv t)

