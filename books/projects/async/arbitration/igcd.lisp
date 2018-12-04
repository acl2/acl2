;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; November 2018

(in-package "ADE")

(include-book "interl")
(include-book "../gcd/gcd")

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "std/lists/sets" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of IGCD
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of IGCD
;;
;; Construct a DE module generator for circuits calculating the Greatest Common
;; Divisor (GCD) of two natural numbers.  There are two mutually exclusive
;; input streams to the GCD submodule that are served on a
;; first-come-first-served basis via an arbitrated merge joint.

(defconst *igcd$select-num* *interl$select-num*)
(defconst *igcd$go-num* (+ *interl$go-num*
                           *gcd$go-num*))
(defconst *igcd$st-len* 3)

(defun igcd$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 3 (* 4 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun igcd$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (igcd$data-ins-len data-width)
     *igcd$select-num*
     *igcd$go-num*))

;; DE module generator of IGCD

(module-generator
 igcd* (data-width)
 (si 'igcd data-width)
 (list* 'full-in0 'full-in1 'empty-out-
        (append (sis 'data0-in 0 (* 2 data-width))
                (sis 'data1-in 0 (* 2 data-width))
                (cons 'select (sis 'go 0 *igcd$go-num*))))
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

 (declare (xargs :guard (natp data-width))))

(make-event
 `(progn
    ,@(state-accessors-gen 'igcd '(l interl gcd) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; IGCD.

(defund igcd$netlist (data-width)
  (declare (xargs :guard (and (natp data-width)
                              (<= 2 data-width))))
  (cons (igcd* data-width)
        (union$ (interl$netlist (* 2 data-width))
                (gcd$netlist data-width)
                :test 'equal)))

;; Recognizer for IGCD

(defund igcd& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width)
                              (<= 2 data-width))))
  (b* ((subnetlist (delete-to-eq (si 'igcd data-width) netlist)))
    (and (equal (assoc (si 'igcd data-width) netlist)
                (igcd* data-width))
         (link& subnetlist (* 2 data-width))
         (interl& subnetlist (* 2 data-width))
         (gcd& subnetlist data-width))))

;; Sanity check

(local
 (defthmd check-igcd$netlist-64
   (and (net-syntax-okp (igcd$netlist 64))
        (net-arity-okp (igcd$netlist 64))
        (igcd& (igcd$netlist 64) 64))))

;; Constraints on the state of IGCD

(defund igcd$st-format (st data-width)
  (b* ((l (get-field *igcd$l* st))
       (interl (get-field *igcd$interl* st))
       (gcd (get-field *igcd$gcd* st)))
    (and (link$st-format l (* 2 data-width))
         (interl$st-format interl (* 2 data-width))
         (gcd$st-format gcd data-width))))

(defthm igcd$st-format=>data-width-constraint
  (implies (igcd$st-format st data-width)
           (and (natp data-width)
                (<= 3 data-width)))
  :hints (("Goal" :in-theory (enable igcd$st-format)))
  :rule-classes :forward-chaining)

(defund igcd$valid-st (st data-width)
  (b* ((l (get-field *igcd$l* st))
       (interl (get-field *igcd$interl* st))
       (gcd (get-field *igcd$gcd* st)))
    (and (link$valid-st l (* 2 data-width))
         (interl$valid-st interl (* 2 data-width))
         (gcd$valid-st gcd data-width))))

(defthmd igcd$valid-st=>data-width-constraint
  (implies (igcd$valid-st st data-width)
           (and (natp data-width)
                (<= 3 data-width)))
  :hints (("Goal" :in-theory (enable gcd$valid-st=>data-width-constraint
                                     igcd$valid-st)))
  :rule-classes :forward-chaining)

(defthmd igcd$valid-st=>st-format
  (implies (igcd$valid-st st data-width)
           (igcd$st-format st data-width))
  :hints (("Goal" :in-theory (e/d (interl$valid-st=>st-format
                                   gcd$valid-st=>st-format
                                   igcd$st-format
                                   igcd$valid-st)
                                  (link$st-format)))))

;; Extract the input and output signals for IGCD

(progn
  ;; Extract the 1st input data item

  (defun igcd$data0-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (* 2 (mbe :logic (nfix data-width)
                    :exec  data-width))
          (nthcdr 3 inputs)))

  (defthm len-igcd$data0-in
    (equal (len (igcd$data0-in inputs data-width))
           (* 2 (nfix data-width))))

  (in-theory (disable igcd$data0-in))

  ;; Extract the 2nd input data item

  (defun igcd$data1-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (b* ((width (* 2 (mbe :logic (nfix data-width)
                          :exec  data-width))))
      (take width
            (nthcdr (+ 3 width) inputs))))

  (defthm len-igcd$data1-in
    (equal (len (igcd$data1-in inputs data-width))
           (* 2 (nfix data-width))))

  (in-theory (disable igcd$data1-in))

  ;; Extract the inputs for joint INTERL

  (defund igcd$interl-inputs (inputs st data-width)
    (b* ((full-in0 (nth 0 inputs))
         (full-in1 (nth 1 inputs))
         (data0-in (igcd$data0-in inputs data-width))
         (data1-in (igcd$data1-in inputs data-width))
         (select   (nth (igcd$data-ins-len data-width) inputs))
         (go-signals (nthcdr (+ (igcd$data-ins-len data-width)
                                *igcd$select-num*)
                             inputs))

         (interl-go-signals (take *interl$go-num* go-signals))

         (l (get-field *igcd$l* st))
         (l.s (get-field *link$s* l)))
      (list* full-in0 full-in1 (f-buf (car l.s))
             (append data0-in data1-in
                     (cons select interl-go-signals)))))

  ;; Extract the "out-act0" signal for joint INTERL

  (defund igcd$interl-out-act0 (inputs st data-width)
    (b* ((interl-inputs (igcd$interl-inputs inputs st data-width))
         (interl (get-field *igcd$interl* st)))
      (interl$out-act0 interl-inputs interl (* 2 data-width))))

  ;; Extract the "out-act1" signal for joint INTERL

  (defund igcd$interl-out-act1 (inputs st data-width)
    (b* ((interl-inputs (igcd$interl-inputs inputs st data-width))
         (interl (get-field *igcd$interl* st)))
      (interl$out-act1 interl-inputs interl (* 2 data-width))))

  (defthm igcd$interl-out-act-mutually-exclusive
    (implies (and (igcd$valid-st st data-width)
                  (igcd$interl-out-act0 inputs st data-width))
             (not (igcd$interl-out-act1 inputs st data-width)))
    :hints (("Goal" :in-theory (enable igcd$valid-st
                                       igcd$interl-out-act0
                                       igcd$interl-out-act1))))

  ;; Extract the "out-act" signal for joint INTERL

  (defund igcd$interl-out-act (inputs st data-width)
    (f-or (igcd$interl-out-act0 inputs st data-width)
          (igcd$interl-out-act1 inputs st data-width)))

  ;; Extract the output data from joint INTERL

  (defund igcd$interl-data-out (inputs st data-width)
    (b* ((interl-inputs (igcd$interl-inputs inputs st data-width))
         (interl (get-field *igcd$interl* st)))
      (interl$data-out interl-inputs interl (* 2 data-width))))

  ;; Extract the inputs for joint GCD

  (defund igcd$gcd-inputs (inputs st data-width)
    (b* ((empty-out- (nth 2 inputs))
         (go-signals (nthcdr (+ (igcd$data-ins-len data-width)
                                *igcd$select-num*)
                             inputs))

         (gcd-go-signals (take *gcd$go-num*
                               (nthcdr *interl$go-num* go-signals)))

         (l (get-field *igcd$l* st))
         (l.s (get-field *link$s* l))
         (l.d (get-field *link$d* l)))

      (list* (f-buf (car l.s)) empty-out-
             (append (v-threefix (strip-cars l.d))
                     gcd-go-signals))))

  ;; Extract the "in0-act" signal

  (defund igcd$in0-act (inputs st data-width)
    (b* ((interl-inputs (igcd$interl-inputs inputs st data-width))
         (interl (get-field *igcd$interl* st)))
      (interl$in0-act interl-inputs interl (* 2 data-width))))

  ;; Extract the "in1-act" signal

  (defund igcd$in1-act (inputs st data-width)
    (b* ((interl-inputs (igcd$interl-inputs inputs st data-width))
         (interl (get-field *igcd$interl* st)))
      (interl$in1-act interl-inputs interl (* 2 data-width))))

  ;; Extract the "out-act" signal

  (defund igcd$out-act (inputs st data-width)
    (gcd$out-act (igcd$gcd-inputs inputs st data-width)
                 (get-field *igcd$gcd* st)
                 data-width))

  ;; Extract the output data

  (defund igcd$data-out (inputs st data-width)
    (gcd$data-out (igcd$gcd-inputs inputs st data-width)
                  (get-field *igcd$gcd* st)
                  data-width))

  (defthm len-igcd$data-out-1
    (implies (igcd$st-format st data-width)
             (equal (len (igcd$data-out inputs st data-width))
                    data-width))
    :hints (("Goal" :in-theory (enable igcd$st-format
                                       igcd$data-out))))

  (defthm len-igcd$data-out-2
    (implies (igcd$valid-st st data-width)
             (equal (len (igcd$data-out inputs st data-width))
                    data-width))
    :hints (("Goal" :in-theory (enable igcd$valid-st
                                       igcd$data-out))))

  (defthm bvp-igcd$data-out
    (implies (and (igcd$valid-st st data-width)
                  (igcd$out-act inputs st data-width))
             (bvp (igcd$data-out inputs st data-width)))
    :hints (("Goal" :in-theory (enable igcd$valid-st
                                       igcd$out-act
                                       igcd$data-out))))

  (defun igcd$outputs (inputs st data-width)
    (list* (igcd$in0-act inputs st data-width)
           (igcd$in1-act inputs st data-width)
           (igcd$out-act inputs st data-width)
           (igcd$data-out inputs st data-width)))
  )

;; The value lemma for IGCD

(encapsulate
  ()

  (local
   (defthm arith-lemma
     (implies (equal m (* 2 n))
              (equal (* 2 m) (* 4 n)))))

  (defthm igcd$value
    (b* ((inputs (list* full-in0 full-in1 empty-out-
                        (append data0-in data1-in
                                (cons select go-signals)))))
      (implies (and (igcd& netlist data-width)
                    (true-listp data0-in)
                    (equal (len data0-in) (* 2 data-width))
                    (true-listp data1-in)
                    (equal (len data1-in) (* 2 data-width))
                    (true-listp go-signals)
                    (equal (len go-signals) *igcd$go-num*)
                    (igcd$st-format st data-width))
               (equal (se (si 'igcd data-width) inputs st netlist)
                      (igcd$outputs inputs st data-width))))
    :hints (("Goal"
             :do-not-induct t
             :expand (:free (inputs data-width)
                            (se (si 'igcd data-width) inputs st netlist))
             :in-theory (e/d (de-rules
                              igcd&
                              igcd*$destructure
                              igcd$st-format
                              igcd$data0-in
                              igcd$data1-in
                              igcd$interl-inputs
                              igcd$gcd-inputs
                              igcd$in0-act
                              igcd$in1-act
                              igcd$out-act
                              igcd$data-out)
                             (de-module-disabled-rules)))))

  ;; This function specifies the next state of IGCD.

  (defun igcd$step (inputs st data-width)
    (b* ((l (get-field *igcd$l* st))
         (interl (get-field *igcd$interl* st))
         (gcd (get-field *igcd$gcd* st))

         (interl-inputs (igcd$interl-inputs inputs st data-width))
         (gcd-inputs (igcd$gcd-inputs inputs st data-width))

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

  (defthm len-of-igcd$step
    (equal (len (igcd$step inputs st data-width))
           *igcd$st-len*))

  ;; The state lemma for IGCD

  (defthm igcd$state
    (b* ((inputs (list* full-in0 full-in1 empty-out-
                        (append data0-in data1-in
                                (cons select go-signals)))))
      (implies (and (igcd& netlist data-width)
                    (true-listp data0-in)
                    (equal (len data0-in) (* 2 data-width))
                    (true-listp data1-in)
                    (equal (len data1-in) (* 2 data-width))
                    (true-listp go-signals)
                    (equal (len go-signals) *igcd$go-num*)
                    (igcd$st-format st data-width))
               (equal (de (si 'igcd data-width) inputs st netlist)
                      (igcd$step inputs st data-width))))
    :hints (("Goal"
             :do-not-induct t
             :expand (:free (inputs data-width)
                            (de (si 'igcd data-width) inputs st netlist))
             :in-theory (e/d (de-rules
                              igcd&
                              igcd*$destructure
                              igcd$st-format
                              igcd$data0-in
                              igcd$data1-in
                              igcd$interl-inputs
                              igcd$gcd-inputs
                              igcd$in0-act
                              igcd$in1-act
                              igcd$out-act)
                             (de-module-disabled-rules)))))

  (in-theory (disable igcd$step))
  )

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund igcd$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in0   (nth 0 inputs))
       (full-in1   (nth 1 inputs))
       (empty-out- (nth 2 inputs))
       (data0-in   (igcd$data0-in inputs data-width))
       (data1-in   (igcd$data1-in inputs data-width))
       (select     (nth (igcd$data-ins-len data-width) inputs))
       (go-signals (nthcdr (+ (igcd$data-ins-len data-width)
                              *igcd$select-num*)
                           inputs)))
    (and
     (booleanp full-in0)
     (booleanp full-in1)
     (booleanp empty-out-)
     (or (not full-in0) (bvp data0-in))
     (or (not full-in1) (bvp data1-in))
     (true-listp go-signals)
     (= (len go-signals) *igcd$go-num*)
     (equal inputs
            (list* full-in0 full-in1 empty-out-
                   (append data0-in data1-in (cons select go-signals)))))))

(local
 (defthm igcd$input-format=>interl$input-format
   (implies (and (igcd$input-format inputs data-width)
                 (igcd$valid-st st data-width))
            (interl$input-format
             (igcd$interl-inputs inputs st data-width)
             (* 2 data-width)))
   :hints (("Goal"
            :in-theory (e/d (open-nth
                             gcd$valid-st=>data-width-constraint
                             interl$input-format
                             interl$data0-in
                             interl$data1-in
                             igcd$input-format
                             igcd$valid-st
                             igcd$interl-inputs)
                            ())))))

(local
 (defthm igcd$input-format=>gcd$input-format
   (implies (and (igcd$input-format inputs data-width)
                 (igcd$valid-st st data-width))
            (gcd$input-format
             (igcd$gcd-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (gcd$valid-st=>data-width-constraint
                             gcd$input-format
                             gcd$data-in
                             igcd$input-format
                             igcd$valid-st
                             igcd$gcd-inputs)
                            ())))))

(defthm booleanp-igcd$in0-act
  (implies (and (igcd$input-format inputs data-width)
                (igcd$valid-st st data-width))
           (booleanp (igcd$in0-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (enable igcd$valid-st
                              igcd$in0-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-igcd$in1-act
  (implies (and (igcd$input-format inputs data-width)
                (igcd$valid-st st data-width))
           (booleanp (igcd$in1-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (enable igcd$valid-st
                              igcd$in1-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-igcd$out-act
  (implies (and (igcd$input-format inputs data-width)
                (igcd$valid-st st data-width))
           (booleanp (igcd$out-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (enable igcd$valid-st
                              igcd$out-act)))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma igcd)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The operation of IGCD over a data sequence

(defun igcd$op-map (x)
  (gcd$op-map x))

;; The extraction functions for IGCD

(defund igcd$extract0 (st)
  (b* ((interl (get-field *igcd$interl* st)))
    (igcd$op-map (interl$extract0 interl))))

(defund igcd$extract1 (st)
  (b* ((interl (get-field *igcd$interl* st)))
    (igcd$op-map (interl$extract1 interl))))

(defund igcd$extract2 (st)
  (b* ((l (get-field *igcd$l* st))
       (gcd (get-field *igcd$gcd* st)))
    (append (igcd$op-map (extract-valid-data (list l)))
            (gcd$extract gcd))))

(defthm igcd$extract0-not-empty
  (implies (and (igcd$interl-out-act0 inputs st data-width)
                (igcd$valid-st st data-width))
           (< 0 (len (igcd$extract0 st))))
  :hints (("Goal"
           :in-theory (e/d (igcd$interl-out-act0
                            igcd$valid-st
                            igcd$extract0)
                           ())))
  :rule-classes :linear)

(defthm igcd$extract1-not-empty
  (implies (and (igcd$interl-out-act1 inputs st data-width)
                (igcd$valid-st st data-width))
           (< 0 (len (igcd$extract1 st))))
  :hints (("Goal"
           :in-theory (e/d (igcd$interl-out-act1
                            igcd$valid-st
                            igcd$extract1)
                           ())))
  :rule-classes :linear)

(defthm igcd$extract2-not-empty
  (implies (and (igcd$out-act inputs st data-width)
                (igcd$valid-st st data-width))
           (< 0 (len (igcd$extract2 st))))
  :hints (("Goal"
           :in-theory (e/d (igcd$out-act
                            igcd$valid-st
                            igcd$extract2)
                           ())))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund igcd$inv (st)
    (b* ((gcd (get-field *igcd$gcd* st)))
      (gcd$inv gcd)))

  (defthm igcd$inv-preserved
    (implies (and (igcd$input-format inputs data-width)
                  (igcd$valid-st st data-width)
                  (igcd$inv st))
             (igcd$inv (igcd$step inputs st data-width)))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              igcd$valid-st
                              igcd$inv
                              igcd$step)
                             ()))))
  )

;; The extracted next-state functions for IGCD.  Note that these functions
;; avoid exploring the internal computation of IGCD.

(defund igcd$extracted0-step (inputs st data-width)
  (b* ((data (gcd$op (igcd$data0-in inputs data-width)))
       (extracted-st (igcd$extract0 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (igcd$interl-out-act0 inputs st data-width) t)
      (cond
       ((equal (igcd$in0-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (igcd$in0-act inputs st data-width) t)
          (cons data extracted-st))
         (t extracted-st))))))

(defund igcd$extracted1-step (inputs st data-width)
  (b* ((data (gcd$op (igcd$data1-in inputs data-width)))
       (extracted-st (igcd$extract1 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (igcd$interl-out-act1 inputs st data-width) t)
      (cond
       ((equal (igcd$in1-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (igcd$in1-act inputs st data-width) t)
          (cons data extracted-st))
         (t extracted-st))))))

(defund igcd$extracted2-step (inputs st data-width)
  (b* ((data (gcd$op (igcd$interl-data-out inputs st data-width)))
       (extracted-st (igcd$extract2 st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (igcd$out-act inputs st data-width) t)
      (cond
       ((equal (igcd$interl-out-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (igcd$interl-out-act inputs st data-width) t)
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
   (defthm igcd-aux-1
     (b* ((interl-inputs (igcd$interl-inputs inputs st data-width)))
       (implies (natp data-width)
                (equal (interl$data0-in interl-inputs (* 2 data-width))
                       (take (* 2 data-width)
                             (nthcdr 3 inputs)))))
     :hints (("Goal" :in-theory (enable igcd$interl-inputs
                                        igcd$data0-in
                                        interl$data0-in)))))

  (local
   (defthm igcd-aux-2
     (b* ((interl-inputs (igcd$interl-inputs inputs st data-width)))
       (implies (natp data-width)
                (equal (interl$data1-in interl-inputs (* 2 data-width))
                       (take (* 2 data-width)
                             (nthcdr (+ 3 (* 2 data-width)) inputs)))))
     :hints (("Goal" :in-theory (enable igcd$interl-inputs
                                        igcd$data1-in
                                        interl$data1-in)))))

  (defthm igcd$extracted0+1-step-correct
    (b* ((next-st (igcd$step inputs st data-width)))
      (implies (and (igcd$input-format inputs data-width)
                    (igcd$valid-st st data-width))
               (and (equal (igcd$extract0 next-st)
                           (igcd$extracted0-step inputs st data-width))
                    (equal (igcd$extract1 next-st)
                           (igcd$extracted1-step inputs st data-width)))))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              gcd$valid-st=>data-width-constraint
                              interl$extracted0-step
                              interl$extracted1-step
                              igcd$extracted0-step
                              igcd$extracted1-step
                              igcd$valid-st
                              igcd$step
                              igcd$data0-in
                              igcd$data1-in
                              igcd$interl-out-act0
                              igcd$interl-out-act1
                              igcd$interl-out-act
                              igcd$in0-act
                              igcd$in1-act
                              igcd$extract0
                              igcd$extract1)
                             (link$valid-st
                              link$step)))))

  (local
   (defthm igcd$interl-out-act-inactive
     (implies (equal (nth *link$s*
                          (nth *igcd$l* st))
                     '(t))
              (and (not (interl$out-act0
                         (igcd$interl-inputs inputs st data-width)
                         (nth *igcd$interl* st)
                         (* 2 data-width)))
                   (not (interl$out-act1
                         (igcd$interl-inputs inputs st data-width)
                         (nth *igcd$interl* st)
                         (* 2 data-width)))))
     :hints (("Goal"
              :in-theory (e/d (get-field
                               igcd$interl-inputs)
                              (nfix))))))

  (local
   (defthm igcd$gcd-in-act-inactive
     (implies (equal (nth *link$s*
                          (nth *igcd$l* st))
                     '(nil))
              (not (gcd$in-act (igcd$gcd-inputs inputs st data-width)
                               (nth *igcd$gcd* st)
                               data-width)))
     :hints (("Goal"
              :in-theory (e/d (get-field
                               igcd$gcd-inputs)
                              (nfix))))))

  (local
   (defthm igcd-aux-3
     (b* ((gcd-inputs (igcd$gcd-inputs inputs st data-width))
          (l (nth *igcd$l* st))
          (l.d (nth *link$d* l)))
       (implies (and (natp data-width)
                     (equal (len l.d) (* 2 data-width))
                     (bvp (strip-cars l.d)))
                (equal (gcd$data-in gcd-inputs data-width)
                       (strip-cars l.d))))
     :hints (("Goal" :in-theory (enable get-field
                                        igcd$gcd-inputs
                                        gcd$data-in)))))

  (defthm igcd$extracted2-step-correct
    (b* ((next-st (igcd$step inputs st data-width)))
      (implies (and (igcd$input-format inputs data-width)
                    (igcd$valid-st st data-width)
                    (igcd$inv st))
               (equal (igcd$extract2 next-st)
                      (igcd$extracted2-step inputs st data-width))))
    :hints (("Goal"
             :use igcd$input-format=>gcd$input-format
             :in-theory (e/d (get-field
                              f-sr
                              interl$out-act
                              gcd$valid-st=>data-width-constraint
                              gcd$extracted-step
                              igcd$extracted2-step
                              igcd$valid-st
                              igcd$inv
                              igcd$step
                              igcd$interl-out-act0
                              igcd$interl-out-act1
                              igcd$interl-out-act
                              igcd$interl-data-out
                              igcd$out-act
                              igcd$extract2)
                             (igcd$input-format=>gcd$input-format
                              interl$extract0-lemma
                              interl$extract1-lemma)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that igcd$valid-st is an invariant.

(encapsulate
  ()

  (local
   (defthm igcd$valid-st-preserved-aux-1
     (implies (and (equal (nth 2 inputs2) (nth 0 inputs1))
                   (booleanp (nth 2 inputs2)))
              (not (and (interl$out-act inputs2 st2 data-width2)
                        (gcd$in-act inputs1 st1 data-width1))))
     :hints (("Goal" :cases ((nth 2 inputs2))))))

  (local
   (defthm igcd$valid-st-preserved-aux-2
     (implies (link$valid-st st data-width)
              (booleanp (car (nth *link$s* st))))
     :hints (("Goal" :in-theory (enable get-field)))
     :rule-classes (:rewrite :type-prescription)))

  (defthm igcd$valid-st-preserved
    (implies (and (igcd$input-format inputs data-width)
                  (igcd$valid-st st data-width))
             (igcd$valid-st (igcd$step inputs st data-width)
                            data-width))
    :hints (("Goal"
             :use (igcd$input-format=>interl$input-format
                   igcd$input-format=>gcd$input-format)
             :in-theory (e/d (get-field
                              igcd$valid-st
                              igcd$step
                              igcd$interl-inputs
                              igcd$gcd-inputs)
                             (igcd$input-format=>interl$input-format
                              igcd$input-format=>gcd$input-format
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

  (defthm igcd$extract0-lemma
    (implies
     (and (igcd$input-format inputs data-width)
          (igcd$valid-st st data-width)
          (igcd$interl-out-act0 inputs st data-width))
     (equal (list (gcd$op (igcd$interl-data-out inputs st data-width)))
            (nthcdr (1- (len (igcd$extract0 st)))
                    (igcd$extract0 st))))
    :hints (("Goal"
             :use igcd$input-format=>interl$input-format
             :in-theory (e/d (igcd$valid-st
                              igcd$interl-inputs
                              igcd$extract0
                              igcd$interl-out-act0
                              igcd$interl-data-out)
                             (igcd$input-format=>interl$input-format
                              interl$extract0-lemma)))))

  (local
   (defthm interl$extract1-lemma-alt
     (implies (and (interl$input-format inputs data-width)
                   (interl$valid-st st data-width)
                   (equal n (1- (len (interl$extract1 st))))
                   (interl$out-act1 inputs st data-width))
              (equal (nthcdr n (interl$extract1 st))
                     (list (interl$data-out inputs st data-width))))))

  (defthm igcd$extract1-lemma
    (implies
     (and (igcd$input-format inputs data-width)
          (igcd$valid-st st data-width)
          (igcd$interl-out-act1 inputs st data-width))
     (equal (list (gcd$op (igcd$interl-data-out inputs st data-width)))
            (nthcdr (1- (len (igcd$extract1 st)))
                    (igcd$extract1 st))))
    :hints (("Goal"
             :use igcd$input-format=>interl$input-format
             :in-theory (e/d (igcd$valid-st
                              igcd$interl-inputs
                              igcd$extract1
                              igcd$interl-out-act1
                              igcd$interl-data-out)
                             (igcd$input-format=>interl$input-format
                              interl$extract1-lemma)))))
  )

(defthm igcd$extract2-lemma
  (implies (and (igcd$input-format inputs data-width)
                (igcd$valid-st st data-width)
                (igcd$out-act inputs st data-width))
           (equal (list (igcd$data-out inputs st data-width))
                  (nthcdr (1- (len (igcd$extract2 st)))
                          (igcd$extract2 st))))
  :hints (("Goal"
           :in-theory (enable igcd$valid-st
                              igcd$extract2
                              igcd$out-act
                              igcd$data-out))))

;; Extract the accepted input sequences

(seq-gen igcd in0 in0-act 0
         (igcd$data0-in inputs data-width))

(seq-gen igcd in1 in1-act 1
         (igcd$data1-in inputs data-width))

;; Extract the valid output sequence

(seq-gen igcd out out-act 2
         (igcd$data-out inputs st data-width)
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

  (defthmd igcd$dataflow-correct
    (b* ((extracted0-st (igcd$extract0 st))
         (extracted1-st (igcd$extract1 st))
         (extracted2-st (igcd$extract2 st))
         (final-st (igcd$run inputs-seq st data-width n))
         (final-extracted0-st (igcd$extract0 final-st))
         (final-extracted1-st (igcd$extract1 final-st))
         (final-extracted2-st (igcd$extract2 final-st)))
      (implies
       (and (igcd$input-format-n inputs-seq data-width n)
            (igcd$valid-st st data-width)
            (igcd$inv st)
            (member x (interleave final-extracted0-st final-extracted1-st)))
       (member
        (append x
                final-extracted2-st
                (igcd$out-seq inputs-seq st data-width n))
        (prepend-rec
         (interleave (append (igcd$op-map
                              (igcd$in0-seq inputs-seq st data-width n))
                             extracted0-st)
                     (append (igcd$op-map
                              (igcd$in1-seq inputs-seq st data-width n))
                             extracted1-st))
         extracted2-st))))
    :hints (("Goal" :in-theory (enable f-or
                                       member-of-true-list-list-is-true-list
                                       igcd$interl-out-act
                                       igcd$extracted0-step
                                       igcd$extracted1-step
                                       igcd$extracted2-step))))

  (defthmd igcd$functionally-correct
    (b* ((extracted0-st (igcd$extract0 st))
         (extracted1-st (igcd$extract1 st))
         (extracted2-st (igcd$extract2 st))
         (final-st (de-n (si 'igcd data-width) inputs-seq st netlist n))
         (final-extracted0-st (igcd$extract0 final-st))
         (final-extracted1-st (igcd$extract1 final-st))
         (final-extracted2-st (igcd$extract2 final-st)))
      (implies
       (and (igcd& netlist data-width)
            (igcd$input-format-n inputs-seq data-width n)
            (igcd$valid-st st data-width)
            (igcd$inv st)
            (member x (interleave final-extracted0-st final-extracted1-st)))
       (member
        (append x
                final-extracted2-st
                (igcd$netlist-out-seq
                 inputs-seq st netlist data-width n))
        (prepend-rec
         (interleave (append (igcd$op-map
                              (igcd$netlist-in0-seq
                               inputs-seq st netlist data-width n))
                             extracted0-st)
                     (append (igcd$op-map
                              (igcd$netlist-in1-seq
                               inputs-seq st netlist data-width n))
                             extracted1-st))
         extracted2-st))))
    :hints (("Goal"
             :use igcd$dataflow-correct
             :in-theory (enable igcd$valid-st=>st-format
                                igcd$de-n))))
  )



