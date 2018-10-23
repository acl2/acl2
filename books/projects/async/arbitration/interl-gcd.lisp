;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2018

(in-package "ADE")

(include-book "interl")
(include-book "../gcd/gcd")

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "std/lists/sets" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of INTERL-GCD
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of INTERL-GCD
;;
;; Construct a DE module generator for circuits calculating the Greatest Common
;; Divisor (GCD) of two natural numbers.  There are two mutually exclusive
;; input streams to the GCD submodule that are served on a
;; first-come-first-served basis via an arbitrated merge joint.

(defconst *interl-gcd$select-num* *interl$select-num*)
(defconst *interl-gcd$go-num* (+ *interl$go-num*
                                 *gcd$go-num*))
(defconst *interl-gcd$st-len* 3)

(defun interl-gcd$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 3 (* 4 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun interl-gcd$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (interl-gcd$data-ins-len data-width)
     *interl-gcd$select-num*
     *interl-gcd$go-num*))

;; DE module generator of INTERL-GCD

(module-generator
 interl-gcd* (data-width)
 (si 'interl-gcd data-width)
 (list* 'full-in0 'full-in1 'empty-out-
        (append (sis 'data0-in 0 (* 2 data-width))
                (sis 'data1-in 0 (* 2 data-width))
                (cons 'select (sis 'go 0 *interl-gcd$go-num*))))
 (list* 'in0-act 'in1-act 'out-act
        (sis 'data-out 0 data-width))
 '(l interl gcd)
 (list
  ;; LINK
  ;; L
  (list 'l
        (list* 'l-status (sis 'd-out 0 (* 2 data-width)))
        (si 'link (* 2 data-width))
        (list* 'interl-out-act 'gcd-in-act (sis 'd-in 0 (* 2 data-width))))

  ;; JOINTS
  ;; INTERL
  (list 'interl
        (list* 'in0-act 'in1-act 'interl-out-act
               (sis 'd-in 0 (* 2 data-width)))
        (si 'interl (* 2 data-width))
        (list* 'full-in0 'full-in1 'l-status
               (append (sis 'data0-in 0 (* 2 data-width))
                       (sis 'data1-in 0 (* 2 data-width))
                       (cons 'select (sis 'go 0 *interl$go-num*)))))

  ;; GCD
  (list 'gcd
        (list* 'gcd-in-act 'out-act
               (sis 'data-out 0 data-width))
        (si 'gcd data-width)
        (list* 'l-status 'empty-out-
               (append (sis 'd-out 0 (* 2 data-width))
                       (sis 'go
                            *interl$go-num*
                            *gcd$go-num*)))))

 :guard (natp data-width))

(make-event
 `(progn
    ,@(state-accessors-gen 'interl-gcd '(l interl gcd) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; INTERL-GCD.

(defund interl-gcd$netlist (data-width)
  (declare (xargs :guard (and (natp data-width)
                              (<= 2 data-width))))
  (cons (interl-gcd* data-width)
        (union$ (interl$netlist (* 2 data-width))
                (gcd$netlist data-width)
                :test 'equal)))

;; Recognizer for INTERL-GCD

(defund interl-gcd& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width)
                              (<= 2 data-width))))
  (b* ((subnetlist (delete-to-eq (si 'interl-gcd data-width) netlist)))
    (and (equal (assoc (si 'interl-gcd data-width) netlist)
                (interl-gcd* data-width))
         (link& subnetlist (* 2 data-width))
         (interl& subnetlist (* 2 data-width))
         (gcd& subnetlist data-width))))

;; Sanity check

(local
 (defthmd check-interl-gcd$netlist-64
   (and (net-syntax-okp (interl-gcd$netlist 64))
        (net-arity-okp (interl-gcd$netlist 64))
        (interl-gcd& (interl-gcd$netlist 64) 64))))

;; Constraints on the state of INTERL-GCD

(defund interl-gcd$st-format (st data-width)
  (b* ((l (get-field *interl-gcd$l* st))
       (interl (get-field *interl-gcd$interl* st))
       (gcd (get-field *interl-gcd$gcd* st)))
    (and (link$st-format l (* 2 data-width))
         (interl$st-format interl (* 2 data-width))
         (gcd$st-format gcd data-width))))

(defthm interl-gcd$st-format=>data-width-constraint
  (implies (interl-gcd$st-format st data-width)
           (and (natp data-width)
                (<= 3 data-width)))
  :hints (("Goal" :in-theory (enable interl-gcd$st-format)))
  :rule-classes :forward-chaining)

(defund interl-gcd$valid-st (st data-width)
  (b* ((l (get-field *interl-gcd$l* st))
       (interl (get-field *interl-gcd$interl* st))
       (gcd (get-field *interl-gcd$gcd* st)))
    (and (link$valid-st l (* 2 data-width))
         (interl$valid-st interl (* 2 data-width))
         (gcd$valid-st gcd data-width))))

(defthmd interl-gcd$valid-st=>data-width-constraint
  (implies (interl-gcd$valid-st st data-width)
           (and (natp data-width)
                (<= 3 data-width)))
  :hints (("Goal" :in-theory (enable gcd$valid-st=>data-width-constraint
                                     interl-gcd$valid-st)))
  :rule-classes :forward-chaining)

(defthmd interl-gcd$valid-st=>st-format
  (implies (interl-gcd$valid-st st data-width)
           (interl-gcd$st-format st data-width))
  :hints (("Goal" :in-theory (e/d (interl$valid-st=>st-format
                                   gcd$valid-st=>st-format
                                   interl-gcd$st-format
                                   interl-gcd$valid-st)
                                  (link$st-format)))))

;; Extract the input and output signals for INTERL-GCD

(progn
  ;; Extract the 1st input data item

  (defun interl-gcd$data0-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (* 2 (mbe :logic (nfix data-width)
                    :exec  data-width))
          (nthcdr 3 inputs)))

  (defthm len-interl-gcd$data0-in
    (equal (len (interl-gcd$data0-in inputs data-width))
           (* 2 (nfix data-width))))

  (in-theory (disable interl-gcd$data0-in))

  ;; Extract the 2nd input data item

  (defun interl-gcd$data1-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (b* ((width (* 2 (mbe :logic (nfix data-width)
                          :exec  data-width))))
      (take width
            (nthcdr (+ 3 width) inputs))))

  (defthm len-interl-gcd$data1-in
    (equal (len (interl-gcd$data1-in inputs data-width))
           (* 2 (nfix data-width))))

  (in-theory (disable interl-gcd$data1-in))

  ;; Extract the inputs for joint INTERL

  (defund interl-gcd$interl-inputs (inputs st data-width)
    (b* ((full-in0 (nth 0 inputs))
         (full-in1 (nth 1 inputs))
         (data0-in (interl-gcd$data0-in inputs data-width))
         (data1-in (interl-gcd$data1-in inputs data-width))
         (select   (nth (interl-gcd$data-ins-len data-width) inputs))
         (go-signals (nthcdr (+ (interl-gcd$data-ins-len data-width)
                                *interl-gcd$select-num*)
                             inputs))

         (interl-go-signals (take *interl$go-num* go-signals))

         (l (get-field *interl-gcd$l* st))
         (l.s (get-field *link$s* l)))
      (list* full-in0 full-in1 (f-buf (car l.s))
             (append data0-in data1-in
                     (cons select interl-go-signals)))))

  ;; Extract the "out-act0" signal for joint INTERL

  (defund interl-gcd$interl-out-act0 (inputs st data-width)
    (b* ((interl-inputs (interl-gcd$interl-inputs inputs st data-width))
         (interl (get-field *interl-gcd$interl* st)))
      (interl$out-act0 interl-inputs interl (* 2 data-width))))

  ;; Extract the "out-act1" signal for joint INTERL

  (defund interl-gcd$interl-out-act1 (inputs st data-width)
    (b* ((interl-inputs (interl-gcd$interl-inputs inputs st data-width))
         (interl (get-field *interl-gcd$interl* st)))
      (interl$out-act1 interl-inputs interl (* 2 data-width))))

  (defthm interl-gcd$interl-out-act-mutually-exclusive
    (implies (and (interl-gcd$valid-st st data-width)
                  (interl-gcd$interl-out-act0 inputs st data-width))
             (not (interl-gcd$interl-out-act1 inputs st data-width)))
    :hints (("Goal" :in-theory (enable interl-gcd$valid-st
                                       interl-gcd$interl-out-act0
                                       interl-gcd$interl-out-act1))))

  ;; Extract the "out-act" signal for joint INTERL

  (defund interl-gcd$interl-out-act (inputs st data-width)
    (f-or (interl-gcd$interl-out-act0 inputs st data-width)
          (interl-gcd$interl-out-act1 inputs st data-width)))

  ;; Extract the output data from joint INTERL

  (defund interl-gcd$interl-data-out (inputs st data-width)
    (b* ((interl-inputs (interl-gcd$interl-inputs inputs st data-width))
         (interl (get-field *interl-gcd$interl* st)))
      (interl$data-out interl-inputs interl (* 2 data-width))))

  ;; Extract the inputs for joint GCD

  (defund interl-gcd$gcd-inputs (inputs st data-width)
    (b* ((empty-out- (nth 2 inputs))
         (go-signals (nthcdr (+ (interl-gcd$data-ins-len data-width)
                                *interl-gcd$select-num*)
                             inputs))

         (gcd-go-signals (take *gcd$go-num*
                               (nthcdr *interl$go-num* go-signals)))

         (l (get-field *interl-gcd$l* st))
         (l.s (get-field *link$s* l))
         (l.d (get-field *link$d* l)))

      (list* (f-buf (car l.s)) empty-out-
             (append (v-threefix (strip-cars l.d))
                     gcd-go-signals))))

  ;; Extract the "in0-act" signal

  (defund interl-gcd$in0-act (inputs st data-width)
    (b* ((interl-inputs (interl-gcd$interl-inputs inputs st data-width))
         (interl (get-field *interl-gcd$interl* st)))
      (interl$in0-act interl-inputs interl (* 2 data-width))))

  ;; Extract the "in1-act" signal

  (defund interl-gcd$in1-act (inputs st data-width)
    (b* ((interl-inputs (interl-gcd$interl-inputs inputs st data-width))
         (interl (get-field *interl-gcd$interl* st)))
      (interl$in1-act interl-inputs interl (* 2 data-width))))

  ;; Extract the "out-act" signal

  (defund interl-gcd$out-act (inputs st data-width)
    (gcd$out-act (interl-gcd$gcd-inputs inputs st data-width)
                 (get-field *interl-gcd$gcd* st)
                 data-width))

  ;; Extract the output data

  (defund interl-gcd$data-out (inputs st data-width)
    (gcd$data-out (interl-gcd$gcd-inputs inputs st data-width)
                  (get-field *interl-gcd$gcd* st)
                  data-width))

  (defthm len-interl-gcd$data-out-1
    (implies (interl-gcd$st-format st data-width)
             (equal (len (interl-gcd$data-out inputs st data-width))
                    data-width))
    :hints (("Goal" :in-theory (enable interl-gcd$st-format
                                       interl-gcd$data-out))))

  (defthm len-interl-gcd$data-out-2
    (implies (interl-gcd$valid-st st data-width)
             (equal (len (interl-gcd$data-out inputs st data-width))
                    data-width))
    :hints (("Goal" :in-theory (enable interl-gcd$valid-st
                                       interl-gcd$data-out))))

  (defthm bvp-interl-gcd$data-out
    (implies (and (interl-gcd$valid-st st data-width)
                  (interl-gcd$out-act inputs st data-width))
             (bvp (interl-gcd$data-out inputs st data-width)))
    :hints (("Goal" :in-theory (enable interl-gcd$valid-st
                                       interl-gcd$out-act
                                       interl-gcd$data-out))))

  (defun interl-gcd$outputs (inputs st data-width)
    (list* (interl-gcd$in0-act inputs st data-width)
           (interl-gcd$in1-act inputs st data-width)
           (interl-gcd$out-act inputs st data-width)
           (interl-gcd$data-out inputs st data-width)))
  )

;; Prove that INTERL-GCD is not a DE primitive.

(not-primp-lemma interl-gcd)

;; The value lemma for INTERL-GCD

(encapsulate
  ()

  (local
   (defthm arith-lemma
     (implies (equal m (* 2 n))
              (equal (* 2 m) (* 4 n)))))

  (defthm interl-gcd$value
    (b* ((inputs (list* full-in0 full-in1 empty-out-
                        (append data0-in data1-in
                                (cons select go-signals)))))
      (implies (and (interl-gcd& netlist data-width)
                    (true-listp data0-in)
                    (equal (len data0-in) (* 2 data-width))
                    (true-listp data1-in)
                    (equal (len data1-in) (* 2 data-width))
                    (true-listp go-signals)
                    (equal (len go-signals) *interl-gcd$go-num*)
                    (interl-gcd$st-format st data-width))
               (equal (se (si 'interl-gcd data-width) inputs st netlist)
                      (interl-gcd$outputs inputs st data-width))))
    :hints (("Goal"
             :do-not-induct t
             :expand (:free (inputs data-width)
                            (se (si 'interl-gcd data-width) inputs st netlist))
             :in-theory (e/d (de-rules
                              interl-gcd&
                              interl-gcd*$destructure
                              interl-gcd$st-format
                              interl-gcd$data0-in
                              interl-gcd$data1-in
                              interl-gcd$interl-inputs
                              interl-gcd$gcd-inputs
                              interl-gcd$in0-act
                              interl-gcd$in1-act
                              interl-gcd$out-act
                              interl-gcd$data-out)
                             (de-module-disabled-rules)))))

  ;; This function specifies the next state of INTERL-GCD.

  (defun interl-gcd$step (inputs st data-width)
    (b* ((l (get-field *interl-gcd$l* st))
         (interl (get-field *interl-gcd$interl* st))
         (gcd (get-field *interl-gcd$gcd* st))

         (interl-inputs (interl-gcd$interl-inputs inputs st data-width))
         (gcd-inputs (interl-gcd$gcd-inputs inputs st data-width))

         (interl-out-act (interl$out-act interl-inputs interl (* 2 data-width)))
         (gcd-in-act (gcd$in-act gcd-inputs gcd data-width))

         (d-in (interl$data-out interl-inputs interl (* 2 data-width)))

         (l-inputs (list* interl-out-act gcd-in-act d-in)))
      (list
       ;; L
       (link$step l-inputs l (* 2 data-width))
       ;; Joint INTERL
       (interl$step interl-inputs interl (* 2 data-width))
       ;; Joint GCD
       (gcd$step gcd-inputs gcd data-width))))

  (defthm len-of-interl-gcd$step
    (equal (len (interl-gcd$step inputs st data-width))
           *interl-gcd$st-len*))

  ;; The state lemma for INTERL-GCD

  (defthm interl-gcd$state
    (b* ((inputs (list* full-in0 full-in1 empty-out-
                        (append data0-in data1-in
                                (cons select go-signals)))))
      (implies (and (interl-gcd& netlist data-width)
                    (true-listp data0-in)
                    (equal (len data0-in) (* 2 data-width))
                    (true-listp data1-in)
                    (equal (len data1-in) (* 2 data-width))
                    (true-listp go-signals)
                    (equal (len go-signals) *interl-gcd$go-num*)
                    (interl-gcd$st-format st data-width))
               (equal (de (si 'interl-gcd data-width) inputs st netlist)
                      (interl-gcd$step inputs st data-width))))
    :hints (("Goal"
             :do-not-induct t
             :expand (:free (inputs data-width)
                            (de (si 'interl-gcd data-width) inputs st netlist))
             :in-theory (e/d (de-rules
                              interl-gcd&
                              interl-gcd*$destructure
                              interl-gcd$st-format
                              interl-gcd$data0-in
                              interl-gcd$data1-in
                              interl-gcd$interl-inputs
                              interl-gcd$gcd-inputs
                              interl-gcd$in0-act
                              interl-gcd$in1-act
                              interl-gcd$out-act)
                             (de-module-disabled-rules)))))

  (in-theory (disable interl-gcd$step))
  )

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund interl-gcd$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in0   (nth 0 inputs))
       (full-in1   (nth 1 inputs))
       (empty-out- (nth 2 inputs))
       (data0-in   (interl-gcd$data0-in inputs data-width))
       (data1-in   (interl-gcd$data1-in inputs data-width))
       (select     (nth (interl-gcd$data-ins-len data-width) inputs))
       (go-signals (nthcdr (+ (interl-gcd$data-ins-len data-width)
                              *interl-gcd$select-num*)
                           inputs)))
    (and
     (booleanp full-in0)
     (booleanp full-in1)
     (booleanp empty-out-)
     (or (not full-in0) (bvp data0-in))
     (or (not full-in1) (bvp data1-in))
     (true-listp go-signals)
     (= (len go-signals) *interl-gcd$go-num*)
     (equal inputs
            (list* full-in0 full-in1 empty-out-
                   (append data0-in data1-in (cons select go-signals)))))))

(local
 (defthm interl-gcd$input-format=>interl$input-format
   (implies (and (interl-gcd$input-format inputs data-width)
                 (interl-gcd$valid-st st data-width))
            (interl$input-format
             (interl-gcd$interl-inputs inputs st data-width)
             (* 2 data-width)))
   :hints (("Goal"
            :in-theory (e/d (open-nth
                             gcd$valid-st=>data-width-constraint
                             interl$input-format
                             interl$data0-in
                             interl$data1-in
                             interl-gcd$input-format
                             interl-gcd$valid-st
                             interl-gcd$interl-inputs)
                            ())))))

(local
 (defthm interl-gcd$input-format=>gcd$input-format
   (implies (and (interl-gcd$input-format inputs data-width)
                 (interl-gcd$valid-st st data-width))
            (gcd$input-format
             (interl-gcd$gcd-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (gcd$valid-st=>data-width-constraint
                             gcd$input-format
                             gcd$data-in
                             interl-gcd$input-format
                             interl-gcd$valid-st
                             interl-gcd$gcd-inputs)
                            ())))))

(defthm booleanp-interl-gcd$in0-act
  (implies (and (interl-gcd$input-format inputs data-width)
                (interl-gcd$valid-st st data-width))
           (booleanp (interl-gcd$in0-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (enable interl-gcd$valid-st
                              interl-gcd$in0-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-interl-gcd$in1-act
  (implies (and (interl-gcd$input-format inputs data-width)
                (interl-gcd$valid-st st data-width))
           (booleanp (interl-gcd$in1-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (enable interl-gcd$valid-st
                              interl-gcd$in1-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-interl-gcd$out-act
  (implies (and (interl-gcd$input-format inputs data-width)
                (interl-gcd$valid-st st data-width))
           (booleanp (interl-gcd$out-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (enable interl-gcd$valid-st
                              interl-gcd$out-act)))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma interl-gcd)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The operation of INTERL-GCD over a data sequence

(defun interl-gcd$op-map (x)
  (gcd$op-map x))

;; The extraction functions for INTERL-GCD

(defund interl-gcd$extract0 (st)
  (b* ((interl (get-field *interl-gcd$interl* st)))
    (interl-gcd$op-map (interl$extract0 interl))))

(defund interl-gcd$extract1 (st)
  (b* ((interl (get-field *interl-gcd$interl* st)))
    (interl-gcd$op-map (interl$extract1 interl))))

(defund interl-gcd$extract2 (st)
  (b* ((l (get-field *interl-gcd$l* st))
       (gcd (get-field *interl-gcd$gcd* st)))
    (append (interl-gcd$op-map (extract-valid-data (list l)))
            (gcd$extract gcd))))

(defthm interl-gcd$extract0-not-empty
  (implies (and (interl-gcd$interl-out-act0 inputs st data-width)
                (interl-gcd$valid-st st data-width))
           (< 0 (len (interl-gcd$extract0 st))))
  :hints (("Goal"
           :in-theory (e/d (interl-gcd$interl-out-act0
                            interl-gcd$valid-st
                            interl-gcd$extract0)
                           ())))
  :rule-classes :linear)

(defthm interl-gcd$extract1-not-empty
  (implies (and (interl-gcd$interl-out-act1 inputs st data-width)
                (interl-gcd$valid-st st data-width))
           (< 0 (len (interl-gcd$extract1 st))))
  :hints (("Goal"
           :in-theory (e/d (interl-gcd$interl-out-act1
                            interl-gcd$valid-st
                            interl-gcd$extract1)
                           ())))
  :rule-classes :linear)

(defthm interl-gcd$extract2-not-empty
  (implies (and (interl-gcd$out-act inputs st data-width)
                (interl-gcd$valid-st st data-width))
           (< 0 (len (interl-gcd$extract2 st))))
  :hints (("Goal"
           :in-theory (e/d (interl-gcd$out-act
                            interl-gcd$valid-st
                            interl-gcd$extract2)
                           ())))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund interl-gcd$inv (st)
    (b* ((gcd (get-field *interl-gcd$gcd* st)))
      (gcd$inv gcd)))

  (defthm interl-gcd$inv-preserved
    (implies (and (interl-gcd$input-format inputs data-width)
                  (interl-gcd$valid-st st data-width)
                  (interl-gcd$inv st))
             (interl-gcd$inv (interl-gcd$step inputs st data-width)))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              interl-gcd$valid-st
                              interl-gcd$inv
                              interl-gcd$step)
                             ()))))
  )

;; The extracted next-state functions for INTERL-GCD.  Note that these functions
;; avoid exploring the internal computation of INTERL-GCD.

(defund interl-gcd$extracted0-step (inputs st data-width)
  (b* ((data (gcd$op (interl-gcd$data0-in inputs data-width)))
       (extracted-st (interl-gcd$extract0 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (interl-gcd$interl-out-act0 inputs st data-width) t)
      (cond
       ((equal (interl-gcd$in0-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (interl-gcd$in0-act inputs st data-width) t)
          (cons data extracted-st))
         (t extracted-st))))))

(defund interl-gcd$extracted1-step (inputs st data-width)
  (b* ((data (gcd$op (interl-gcd$data1-in inputs data-width)))
       (extracted-st (interl-gcd$extract1 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (interl-gcd$interl-out-act1 inputs st data-width) t)
      (cond
       ((equal (interl-gcd$in1-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (interl-gcd$in1-act inputs st data-width) t)
          (cons data extracted-st))
         (t extracted-st))))))

(defund interl-gcd$extracted2-step (inputs st data-width)
  (b* ((data (gcd$op (interl-gcd$interl-data-out inputs st data-width)))
       (extracted-st (interl-gcd$extract2 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (interl-gcd$out-act inputs st data-width) t)
      (cond
       ((equal (interl-gcd$interl-out-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (interl-gcd$interl-out-act inputs st data-width) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(progn
  (local
   (defthm take-of-gcd$op-map
     (equal (take n (gcd$op-map l))
            (gcd$op-map (take n l)))
     :hints (("Goal" :in-theory (enable repeat)))))

  (local
   (defthm interl-gcd-aux-1
     (b* ((interl-inputs (interl-gcd$interl-inputs inputs st data-width)))
       (implies (natp data-width)
                (equal (interl$data0-in interl-inputs (* 2 data-width))
                       (take (* 2 data-width)
                             (nthcdr 3 inputs)))))
     :hints (("Goal" :in-theory (enable interl-gcd$interl-inputs
                                        interl-gcd$data0-in
                                        interl$data0-in)))))

  (local
   (defthm interl-gcd-aux-2
     (b* ((interl-inputs (interl-gcd$interl-inputs inputs st data-width)))
       (implies (natp data-width)
                (equal (interl$data1-in interl-inputs (* 2 data-width))
                       (take (* 2 data-width)
                             (nthcdr (+ 3 (* 2 data-width)) inputs)))))
     :hints (("Goal" :in-theory (enable interl-gcd$interl-inputs
                                        interl-gcd$data1-in
                                        interl$data1-in)))))

  (defthm interl-gcd$extracted0+1-step-correct
    (b* ((next-st (interl-gcd$step inputs st data-width)))
      (implies (and (interl-gcd$input-format inputs data-width)
                    (interl-gcd$valid-st st data-width))
               (and (equal (interl-gcd$extract0 next-st)
                           (interl-gcd$extracted0-step inputs st data-width))
                    (equal (interl-gcd$extract1 next-st)
                           (interl-gcd$extracted1-step inputs st data-width)))))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              gcd$valid-st=>data-width-constraint
                              interl$extracted0-step
                              interl$extracted1-step
                              interl-gcd$extracted0-step
                              interl-gcd$extracted1-step
                              interl-gcd$valid-st
                              interl-gcd$step
                              interl-gcd$data0-in
                              interl-gcd$data1-in
                              interl-gcd$interl-out-act0
                              interl-gcd$interl-out-act1
                              interl-gcd$interl-out-act
                              interl-gcd$in0-act
                              interl-gcd$in1-act
                              interl-gcd$extract0
                              interl-gcd$extract1)
                             (link$valid-st
                              link$step)))))

  (local
   (defthm interl-gcd$interl-out-act-inactive
     (implies (equal (nth *link$s*
                          (nth *interl-gcd$l* st))
                     '(t))
              (and (not (interl$out-act0
                         (interl-gcd$interl-inputs inputs st data-width)
                         (nth *interl-gcd$interl* st)
                         (* 2 data-width)))
                   (not (interl$out-act1
                         (interl-gcd$interl-inputs inputs st data-width)
                         (nth *interl-gcd$interl* st)
                         (* 2 data-width)))))
     :hints (("Goal"
              :in-theory (e/d (get-field
                               interl-gcd$interl-inputs)
                              (nfix))))))

  (local
   (defthm interl-gcd$gcd-in-act-inactive
     (implies (equal (nth *link$s*
                          (nth *interl-gcd$l* st))
                     '(nil))
              (not (gcd$in-act (interl-gcd$gcd-inputs inputs st data-width)
                               (nth *interl-gcd$gcd* st)
                               data-width)))
     :hints (("Goal"
              :in-theory (e/d (get-field
                               interl-gcd$gcd-inputs)
                              (nfix))))))

  (local
   (defthm interl-gcd-aux-3
     (b* ((gcd-inputs (interl-gcd$gcd-inputs inputs st data-width))
          (l (nth *interl-gcd$l* st))
          (l.d (nth *link$d* l)))
       (implies (and (natp data-width)
                     (equal (len l.d) (* 2 data-width))
                     (bvp (strip-cars l.d)))
                (equal (gcd$data-in gcd-inputs data-width)
                       (strip-cars l.d))))
     :hints (("Goal" :in-theory (enable get-field
                                        interl-gcd$gcd-inputs
                                        gcd$data-in)))))

  (defthm interl-gcd$extracted2-step-correct
    (b* ((next-st (interl-gcd$step inputs st data-width)))
      (implies (and (interl-gcd$input-format inputs data-width)
                    (interl-gcd$valid-st st data-width)
                    (interl-gcd$inv st))
               (equal (interl-gcd$extract2 next-st)
                      (interl-gcd$extracted2-step inputs st data-width))))
    :hints (("Goal"
             :use interl-gcd$input-format=>gcd$input-format
             :in-theory (e/d (get-field
                              f-sr
                              interl$out-act
                              gcd$valid-st=>data-width-constraint
                              gcd$extracted-step
                              interl-gcd$extracted2-step
                              interl-gcd$valid-st
                              interl-gcd$inv
                              interl-gcd$step
                              interl-gcd$interl-out-act0
                              interl-gcd$interl-out-act1
                              interl-gcd$interl-out-act
                              interl-gcd$interl-data-out
                              interl-gcd$out-act
                              interl-gcd$extract2)
                             (interl-gcd$input-format=>gcd$input-format
                              interl$extract0-lemma
                              interl$extract1-lemma)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that interl-gcd$valid-st is an invariant.

(encapsulate
  ()

  (local
   (defthm interl-gcd$valid-st-preserved-aux-1
     (implies (and (equal (nth 2 inputs2) (nth 0 inputs1))
                   (booleanp (nth 2 inputs2)))
              (not (and (interl$out-act inputs2 st2 data-width2)
                        (gcd$in-act inputs1 st1 data-width1))))
     :hints (("Goal" :cases ((nth 2 inputs2))))))

  (local
   (defthm interl-gcd$valid-st-preserved-aux-2
     (implies (link$valid-st st data-width)
              (booleanp (car (nth *link$s* st))))
     :hints (("Goal" :in-theory (enable get-field)))
     :rule-classes (:rewrite :type-prescription)))

  (defthm interl-gcd$valid-st-preserved
    (implies (and (interl-gcd$input-format inputs data-width)
                  (interl-gcd$valid-st st data-width))
             (interl-gcd$valid-st (interl-gcd$step inputs st data-width)
                                  data-width))
    :hints (("Goal"
             :use (interl-gcd$input-format=>interl$input-format
                   interl-gcd$input-format=>gcd$input-format)
             :in-theory (e/d (get-field
                              interl-gcd$valid-st
                              interl-gcd$step
                              interl-gcd$interl-inputs
                              interl-gcd$gcd-inputs)
                             (interl-gcd$input-format=>interl$input-format
                              interl-gcd$input-format=>gcd$input-format
                              link$valid-st
                              link$step
                              nfix)))))
  )

(encapsulate
  ()

  (local
   (defthm nthcdr-gcd$op-map
     (equal (nthcdr n (gcd$op-map l))
            (gcd$op-map (nthcdr n l)))))

  (local
   (defthm interl$extract0-lemma-alt
     (implies (and (interl$input-format inputs data-width)
                   (interl$valid-st st data-width)
                   (equal n (1- (len (interl$extract0 st))))
                   (interl$out-act0 inputs st data-width))
              (equal (nthcdr n (interl$extract0 st))
                     (list (interl$data-out inputs st data-width))))))

  (defthm interl-gcd$extract0-lemma
    (implies
     (and (interl-gcd$input-format inputs data-width)
          (interl-gcd$valid-st st data-width)
          (interl-gcd$interl-out-act0 inputs st data-width))
     (equal (list (gcd$op (interl-gcd$interl-data-out inputs st data-width)))
            (nthcdr (1- (len (interl-gcd$extract0 st)))
                    (interl-gcd$extract0 st))))
    :hints (("Goal"
             :use interl-gcd$input-format=>interl$input-format
             :in-theory (e/d (interl-gcd$valid-st
                              interl-gcd$interl-inputs
                              interl-gcd$extract0
                              interl-gcd$interl-out-act0
                              interl-gcd$interl-data-out)
                             (interl-gcd$input-format=>interl$input-format
                              interl$extract0-lemma)))))

  (local
   (defthm interl$extract1-lemma-alt
     (implies (and (interl$input-format inputs data-width)
                   (interl$valid-st st data-width)
                   (equal n (1- (len (interl$extract1 st))))
                   (interl$out-act1 inputs st data-width))
              (equal (nthcdr n (interl$extract1 st))
                     (list (interl$data-out inputs st data-width))))))

  (defthm interl-gcd$extract1-lemma
    (implies
     (and (interl-gcd$input-format inputs data-width)
          (interl-gcd$valid-st st data-width)
          (interl-gcd$interl-out-act1 inputs st data-width))
     (equal (list (gcd$op (interl-gcd$interl-data-out inputs st data-width)))
            (nthcdr (1- (len (interl-gcd$extract1 st)))
                    (interl-gcd$extract1 st))))
    :hints (("Goal"
             :use interl-gcd$input-format=>interl$input-format
             :in-theory (e/d (interl-gcd$valid-st
                              interl-gcd$interl-inputs
                              interl-gcd$extract1
                              interl-gcd$interl-out-act1
                              interl-gcd$interl-data-out)
                             (interl-gcd$input-format=>interl$input-format
                              interl$extract1-lemma)))))
  )

(defthm interl-gcd$extract2-lemma
  (implies (and (interl-gcd$input-format inputs data-width)
                (interl-gcd$valid-st st data-width)
                (interl-gcd$out-act inputs st data-width))
           (equal (list (interl-gcd$data-out inputs st data-width))
                  (nthcdr (1- (len (interl-gcd$extract2 st)))
                          (interl-gcd$extract2 st))))
  :hints (("Goal"
           :in-theory (enable interl-gcd$valid-st
                              interl-gcd$extract2
                              interl-gcd$out-act
                              interl-gcd$data-out))))

;; Extract the accepted input sequences

(seq-gen interl-gcd in0 in0-act 0
         (interl-gcd$data0-in inputs data-width))

(seq-gen interl-gcd in1 in1-act 1
         (interl-gcd$data1-in inputs data-width))

;; Extract the valid output sequence

(seq-gen interl-gcd out out-act 2
         (interl-gcd$data-out inputs st data-width)
         :netlist-data (nthcdr 3 outputs))

;; The multi-step input-output relationship

(encapsulate
  ()

  (local
   (defthm member-append-prepend-rec-instance-1
     (implies (and (member (append a b c) (prepend-rec x y))
                   (equal y++x1 (append y x1)))
              (member (append a b c x1)
                      (prepend-rec x y++x1)))
     :hints (("Goal" :use (:instance member-append-prepend-rec
                                     (e (append a b c))
                                     (x (prepend-rec x y))
                                     (e1 x1))))))

  (local
   (defthm member-append-prepend-rec-instance-2
     (implies (and (member (append a b c)
                           (prepend-rec (interleave x y) (cons e z)))
                   (equal z++x1 (append z x1))
                   (equal xe (append x (list e)))
                   (true-listp y))
              (member (append a b c x1)
                      (prepend-rec (interleave xe y) z++x1)))
     :hints (("Goal"
              :in-theory (disable member-append-prepend-rec-instance-1)
              :use (:instance member-append-prepend-rec-instance-1
                              (x (interleave xe y))
                              (y z)
                              (y++x1 z++x1))))))

  (local
   (defthm member-append-prepend-rec-instance-3
     (implies (and (member (append a b c)
                           (prepend-rec (interleave x y) (cons e z)))
                   (equal z++x1 (append z x1))
                   (equal ye (append y (list e)))
                   (true-listp x))
              (member (append a b c x1)
                      (prepend-rec (interleave x ye) z++x1)))
     :hints (("Goal"
              :in-theory (disable member-append-prepend-rec-instance-1)
              :use (:instance member-append-prepend-rec-instance-1
                              (x (interleave x ye))
                              (y z)
                              (y++x1 z++x1))))))

  (defthmd interl-gcd$dataflow-correct
    (b* ((extracted0-st (interl-gcd$extract0 st))
         (extracted1-st (interl-gcd$extract1 st))
         (extracted2-st (interl-gcd$extract2 st))
         (final-st (interl-gcd$run inputs-seq st data-width n))
         (final-extracted0-st (interl-gcd$extract0 final-st))
         (final-extracted1-st (interl-gcd$extract1 final-st))
         (final-extracted2-st (interl-gcd$extract2 final-st)))
      (implies
       (and (interl-gcd$input-format-n inputs-seq data-width n)
            (interl-gcd$valid-st st data-width)
            (interl-gcd$inv st)
            (member x (interleave final-extracted0-st final-extracted1-st)))
       (member
        (append x
                final-extracted2-st
                (interl-gcd$out-seq inputs-seq st data-width n))
        (prepend-rec
         (interleave (append (interl-gcd$op-map
                              (interl-gcd$in0-seq inputs-seq st data-width n))
                             extracted0-st)
                     (append (interl-gcd$op-map
                              (interl-gcd$in1-seq inputs-seq st data-width n))
                             extracted1-st))
         extracted2-st))))
    :hints (("Goal" :in-theory (enable f-or
                                       member-of-true-list-list-is-true-list
                                       interl-gcd$interl-out-act
                                       interl-gcd$extracted0-step
                                       interl-gcd$extracted1-step
                                       interl-gcd$extracted2-step))))

  (defthmd interl-gcd$functionally-correct
    (b* ((extracted0-st (interl-gcd$extract0 st))
         (extracted1-st (interl-gcd$extract1 st))
         (extracted2-st (interl-gcd$extract2 st))
         (final-st (de-n (si 'interl-gcd data-width) inputs-seq st netlist n))
         (final-extracted0-st (interl-gcd$extract0 final-st))
         (final-extracted1-st (interl-gcd$extract1 final-st))
         (final-extracted2-st (interl-gcd$extract2 final-st)))
      (implies
       (and (interl-gcd& netlist data-width)
            (interl-gcd$input-format-n inputs-seq data-width n)
            (interl-gcd$valid-st st data-width)
            (interl-gcd$inv st)
            (member x (interleave final-extracted0-st final-extracted1-st)))
       (member
        (append x
                final-extracted2-st
                (interl-gcd$netlist-out-seq
                 inputs-seq st netlist data-width n))
        (prepend-rec
         (interleave (append (interl-gcd$op-map
                              (interl-gcd$netlist-in0-seq
                               inputs-seq st netlist data-width n))
                             extracted0-st)
                     (append (interl-gcd$op-map
                              (interl-gcd$netlist-in1-seq
                               inputs-seq st netlist data-width n))
                             extracted1-st))
         extracted2-st))))
    :hints (("Goal"
             :use interl-gcd$dataflow-correct
             :in-theory (enable interl-gcd$valid-st=>st-format
                                interl-gcd$de-n))))
  )



