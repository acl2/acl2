;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; November 2018

(in-package "ADE")

(include-book "comp-gcd")
(include-book "../fifo/queue10")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of Q10-COMP-GCD
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of Q10-COMP-GCD
;;
;; Construct a DE module generator that concatenates Q10 with COMP-GCD via a
;; link.  Prove the value and state lemmas for this module generator.

(defconst *q10-comp-gcd$go-num* (+ *queue10$go-num*
                                  *comp-gcd$go-num*))
(defconst *q10-comp-gcd$st-len* 3)

(defun q10-comp-gcd$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun q10-comp-gcd$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (q10-comp-gcd$data-ins-len data-width)
     *q10-comp-gcd$go-num*))

;; DE module generator of Q10-COMP-GCD

(module-generator
 q10-comp-gcd* (data-width)
 (si 'q10-comp-gcd data-width)
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 (* 2 data-width))
                                     (sis 'go 0 *q10-comp-gcd$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-width))
 '(l q10 comp-gcd)
 (list
  ;; LINK
  ;; L
  (list 'l
        (list* 'l-status (sis 'd-out 0 (* 2 data-width)))
        (si 'link (* 2 data-width))
        (list* 'q10-out-act 'comp-gcd-in-act
               (sis 'q10-data-out 0 (* 2 data-width))))

  ;; JOINTS
  ;; Q10
  (list 'q10
        (list* 'in-act 'q10-out-act
               (sis 'q10-data-out 0 (* 2 data-width)))
        (si 'queue10 (* 2 data-width))
        (list* 'full-in 'l-status
               (append (sis 'data-in 0 (* 2 data-width))
                       (sis 'go 0 *queue10$go-num*))))

  ;; COMP-GCD
  (list 'comp-gcd
        (list* 'comp-gcd-in-act 'out-act
               (sis 'data-out 0 data-width))
        (si 'comp-gcd data-width)
        (list* 'l-status 'empty-out-
               (append (sis 'd-out 0 (* 2 data-width))
                       (sis 'go
                            *queue10$go-num*
                            *comp-gcd$go-num*)))))

 (declare (xargs :guard (natp data-width))))

(make-event
 `(progn
    ,@(state-accessors-gen 'q10-comp-gcd '(l q10 comp-gcd) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; Q10-COMP-GCD.

(defund q10-comp-gcd$netlist (data-width)
  (declare (xargs :guard (and (natp data-width)
                              (<= 2 data-width))))
  (cons (q10-comp-gcd* data-width)
        (union$ (queue10$netlist (* 2 data-width))
                (comp-gcd$netlist data-width)
                :test 'equal)))

;; Recognizer for Q10-COMP-GCD

(defund q10-comp-gcd& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width)
                              (<= 2 data-width))))
  (b* ((subnetlist (delete-to-eq (si 'q10-comp-gcd data-width)
                                 netlist)))
    (and (equal (assoc (si 'q10-comp-gcd data-width) netlist)
                (q10-comp-gcd* data-width))
         (link& subnetlist (* 2 data-width))
         (queue10& subnetlist (* 2 data-width))
         (comp-gcd& subnetlist data-width))))

;; Sanity check

(local
 (defthmd check-q10-comp-gcd$netlist-64
   (and (net-syntax-okp (q10-comp-gcd$netlist 64))
        (net-arity-okp (q10-comp-gcd$netlist 64))
        (q10-comp-gcd& (q10-comp-gcd$netlist 64) 64))))

;; Constraints on the state of Q10-COMP-GCD

(defund q10-comp-gcd$st-format (st data-width)
  (b* ((l        (get-field *q10-comp-gcd$l* st))
       (q10       (get-field *q10-comp-gcd$q10* st))
       (comp-gcd (get-field *q10-comp-gcd$comp-gcd* st)))
    (and (link$st-format l (* 2 data-width))
         (queue10$st-format q10 (* 2 data-width))
         (comp-gcd$st-format comp-gcd data-width))))

(defthm q10-comp-gcd$st-format=>data-width-constraint
  (implies (q10-comp-gcd$st-format st data-width)
           (and (natp data-width)
                (<= 3 data-width)))
  :hints (("Goal"
           :in-theory (enable q10-comp-gcd$st-format)))
  :rule-classes :forward-chaining)

(defund q10-comp-gcd$valid-st (st data-width)
  (b* ((l        (get-field *q10-comp-gcd$l* st))
       (q10       (get-field *q10-comp-gcd$q10* st))
       (comp-gcd (get-field *q10-comp-gcd$comp-gcd* st)))
    (and (link$valid-st l (* 2 data-width))
         (queue10$valid-st q10 (* 2 data-width))
         (comp-gcd$valid-st comp-gcd data-width))))

(defthmd q10-comp-gcd$valid-st=>data-width-constraint
  (implies (q10-comp-gcd$valid-st st data-width)
           (and (natp data-width)
                (<= 3 data-width)))
  :hints (("Goal"
           :in-theory (enable comp-gcd$valid-st=>data-width-constraint
                              q10-comp-gcd$valid-st)))
  :rule-classes :forward-chaining)

(defthmd q10-comp-gcd$valid-st=>st-format
  (implies (q10-comp-gcd$valid-st st data-width)
           (q10-comp-gcd$st-format st data-width))
  :hints (("Goal" :in-theory (e/d (queue10$valid-st=>st-format
                                   comp-gcd$valid-st=>st-format
                                   q10-comp-gcd$st-format
                                   q10-comp-gcd$valid-st)
                                  (link$st-format)))))

;; Extract the input and output signals for Q10-COMP-GCD

(progn
  ;; Extract the input data

  (defun q10-comp-gcd$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (* 2 (mbe :logic (nfix data-width)
                    :exec  data-width))
          (nthcdr 2 inputs)))

  (defthm len-q10-comp-gcd$data-in
    (equal (len (q10-comp-gcd$data-in inputs data-width))
           (* 2 (nfix data-width))))

  (in-theory (disable q10-comp-gcd$data-in))

  ;; Extract the inputs for the Q10 joint

  (defund q10-comp-gcd$q10-inputs (inputs st data-width)
    (b* ((full-in (nth 0 inputs))
         (data-in (q10-comp-gcd$data-in inputs data-width))
         (go-signals (nthcdr (q10-comp-gcd$data-ins-len data-width)
                             inputs))

         (q10-go-signals (take *queue10$go-num* go-signals))

         (l (get-field *q10-comp-gcd$l* st))
         (l.s (get-field *link$s* l)))

      (list* full-in (f-buf (car l.s))
             (append data-in q10-go-signals))))

  ;; Extract the inputs for the COMP-GCD joint

  (defund q10-comp-gcd$comp-gcd-inputs (inputs st data-width)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (q10-comp-gcd$data-ins-len data-width)
                             inputs))

         (comp-gcd-go-signals (take *comp-gcd$go-num*
                                    (nthcdr *queue10$go-num* go-signals)))

         (l (get-field *q10-comp-gcd$l* st))
         (l.s (get-field *link$s* l))
         (l.d (get-field *link$d* l)))

      (list* (f-buf (car l.s)) empty-out-
             (append (v-threefix (strip-cars l.d))
                     comp-gcd-go-signals))))

  ;; Extract the "in-act" signal

  (defund q10-comp-gcd$in-act (inputs st data-width)
    (queue10$in-act (q10-comp-gcd$q10-inputs inputs st data-width)
                   (get-field *q10-comp-gcd$q10* st)
                   (* 2 data-width)))

  (defthm q10-comp-gcd$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (q10-comp-gcd$in-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable q10-comp-gcd$q10-inputs
                                       q10-comp-gcd$in-act))))

  ;; Extract the "out-act" signal

  (defund q10-comp-gcd$out-act (inputs st data-width)
    (comp-gcd$out-act (q10-comp-gcd$comp-gcd-inputs inputs st data-width)
                      (get-field *q10-comp-gcd$comp-gcd* st)
                      data-width))

  (defthm q10-comp-gcd$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (q10-comp-gcd$out-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable q10-comp-gcd$comp-gcd-inputs
                                       q10-comp-gcd$out-act))))

  ;; Extract the output data

  (defund q10-comp-gcd$data-out (inputs st data-width)
    (comp-gcd$data-out (q10-comp-gcd$comp-gcd-inputs inputs st data-width)
                       (get-field *q10-comp-gcd$comp-gcd* st)
                       data-width))

  (defthm len-q10-comp-gcd$data-out-1
    (implies (q10-comp-gcd$st-format st data-width)
             (equal (len (q10-comp-gcd$data-out inputs st data-width))
                    data-width))
    :hints (("Goal" :in-theory (enable q10-comp-gcd$st-format
                                       q10-comp-gcd$data-out))))

  (defthm len-q10-comp-gcd$data-out-2
    (implies (q10-comp-gcd$valid-st st data-width)
             (equal (len (q10-comp-gcd$data-out inputs st data-width))
                    data-width))
    :hints (("Goal" :in-theory (enable q10-comp-gcd$valid-st
                                       q10-comp-gcd$data-out))))

  (defthm bvp-q10-comp-gcd$data-out
    (implies (and (q10-comp-gcd$valid-st st data-width)
                  (q10-comp-gcd$out-act inputs st data-width))
             (bvp (q10-comp-gcd$data-out inputs st data-width)))
    :hints (("Goal" :in-theory (enable q10-comp-gcd$valid-st
                                       q10-comp-gcd$out-act
                                       q10-comp-gcd$data-out))))

  (defun q10-comp-gcd$outputs (inputs st data-width)
    (list* (q10-comp-gcd$in-act inputs st data-width)
           (q10-comp-gcd$out-act inputs st data-width)
           (q10-comp-gcd$data-out inputs st data-width)))
  )

;; The value lemma for Q10-COMP-GCD

(defthm q10-comp-gcd$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies
     (and (q10-comp-gcd& netlist data-width)
          (true-listp data-in)
          (equal (len data-in) (* 2 data-width))
          (true-listp go-signals)
          (equal (len go-signals) *q10-comp-gcd$go-num*)
          (q10-comp-gcd$st-format st data-width))
     (equal (se (si 'q10-comp-gcd data-width) inputs st netlist)
            (q10-comp-gcd$outputs inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'q10-comp-gcd data-width)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            q10-comp-gcd&
                            q10-comp-gcd*$destructure
                            q10-comp-gcd$data-in
                            q10-comp-gcd$st-format
                            q10-comp-gcd$in-act
                            q10-comp-gcd$out-act
                            q10-comp-gcd$data-out
                            q10-comp-gcd$q10-inputs
                            q10-comp-gcd$comp-gcd-inputs)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of Q10-COMP-GCD.

(defun q10-comp-gcd$step (inputs st data-width)
  (b* ((l   (get-field *q10-comp-gcd$l* st))
       (q10  (get-field *q10-comp-gcd$q10* st))
       (comp-gcd (get-field *q10-comp-gcd$comp-gcd* st))

       (q10-inputs (q10-comp-gcd$q10-inputs inputs st data-width))
       (comp-gcd-inputs (q10-comp-gcd$comp-gcd-inputs
                         inputs st data-width))

       (d-in (queue10$data-out q10))

       (q10-out-act (queue10$out-act q10-inputs q10 (* 2 data-width)))
       (comp-gcd-in-act (comp-gcd$in-act comp-gcd-inputs
                                         comp-gcd data-width))

       (l-inputs (list* q10-out-act comp-gcd-in-act d-in)))
    (list
     ;; L
     (link$step l-inputs l (* 2 data-width))
     ;; Joint Q10
     (queue10$step q10-inputs q10 (* 2 data-width))
     ;; Joint COMP-GCD
     (comp-gcd$step comp-gcd-inputs comp-gcd data-width))))

(defthm len-of-q10-comp-gcd$step
  (equal (len (q10-comp-gcd$step inputs st data-width))
         *q10-comp-gcd$st-len*))

;; The state lemma for Q10-COMP-GCD

(defthm q10-comp-gcd$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies
     (and (q10-comp-gcd& netlist data-width)
          (true-listp data-in)
          (equal (len data-in) (* 2 data-width))
          (true-listp go-signals)
          (equal (len go-signals) *q10-comp-gcd$go-num*)
          (q10-comp-gcd$st-format st data-width))
     (equal (de (si 'q10-comp-gcd data-width) inputs st netlist)
            (q10-comp-gcd$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'q10-comp-gcd data-width)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            q10-comp-gcd&
                            q10-comp-gcd*$destructure
                            q10-comp-gcd$st-format
                            q10-comp-gcd$data-in
                            q10-comp-gcd$data-out
                            q10-comp-gcd$q10-inputs
                            q10-comp-gcd$comp-gcd-inputs)
                           (de-module-disabled-rules)))))

(in-theory (disable q10-comp-gcd$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund q10-comp-gcd$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (q10-comp-gcd$data-in inputs data-width))
       (go-signals (nthcdr (q10-comp-gcd$data-ins-len data-width)
                           inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *q10-comp-gcd$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(local
 (defthm q10-comp-gcd$input-format=>q10$input-format
   (implies (and (q10-comp-gcd$input-format inputs data-width)
                 (q10-comp-gcd$valid-st st data-width))
            (queue10$input-format
             (q10-comp-gcd$q10-inputs inputs st data-width)
             (* 2 data-width)))
   :hints (("Goal"
            :in-theory (e/d (q10-comp-gcd$input-format
                             comp-gcd$valid-st=>data-width-constraint
                             queue10$input-format
                             queue10$data-in
                             q10-comp-gcd$valid-st
                             q10-comp-gcd$q10-inputs)
                            ())))))

(local
 (defthm q10-comp-gcd$input-format=>comp-gcd$input-format
   (implies (and (q10-comp-gcd$input-format inputs data-width)
                 (q10-comp-gcd$valid-st st data-width))
            (comp-gcd$input-format
             (q10-comp-gcd$comp-gcd-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (q10-comp-gcd$input-format
                             comp-gcd$valid-st=>data-width-constraint
                             comp-gcd$input-format
                             comp-gcd$data-in
                             q10-comp-gcd$valid-st
                             q10-comp-gcd$st-format
                             q10-comp-gcd$comp-gcd-inputs)
                            ())))))

(defthm booleanp-q10-comp-gcd$in-act
  (implies (and (q10-comp-gcd$input-format inputs data-width)
                (q10-comp-gcd$valid-st st data-width))
           (booleanp (q10-comp-gcd$in-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (enable q10-comp-gcd$valid-st
                              q10-comp-gcd$in-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-q10-comp-gcd$out-act
  (implies (and (q10-comp-gcd$input-format inputs data-width)
                (q10-comp-gcd$valid-st st data-width))
           (booleanp (q10-comp-gcd$out-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (enable q10-comp-gcd$valid-st
                              q10-comp-gcd$out-act)))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma q10-comp-gcd)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The operation of Q10-COMP-GCD over a data sequence

(defun q10-comp-gcd$op-map (x)
  (if (atom x)
      nil
    (cons (comp-gcd$op (car x))
          (q10-comp-gcd$op-map (cdr x)))))

(defthm len-of-q10-comp-gcd$op-map
  (equal (len (q10-comp-gcd$op-map x))
         (len x)))

(defthm q10-comp-gcd$op-map-of-append
  (equal (q10-comp-gcd$op-map (append x y))
         (append (q10-comp-gcd$op-map x) (q10-comp-gcd$op-map y))))

;; The extraction function for Q10-COMP-GCD that extracts the future output
;; sequence from the current state.

(defund q10-comp-gcd$extract (st)
  (b* ((l   (get-field *q10-comp-gcd$l* st))
       (q10  (get-field *q10-comp-gcd$q10* st))
       (comp-gcd (get-field *q10-comp-gcd$comp-gcd* st)))
    (append
     (q10-comp-gcd$op-map
      (append (queue10$extract q10)
              (extract-valid-data (list l))))
     (comp-gcd$extract comp-gcd))))

(defthm q10-comp-gcd$extract-not-empty
  (implies (and (q10-comp-gcd$out-act inputs st data-width)
                (q10-comp-gcd$valid-st st data-width))
           (< 0 (len (q10-comp-gcd$extract st))))
  :hints (("Goal"
           :in-theory (e/d (q10-comp-gcd$valid-st
                            q10-comp-gcd$extract
                            q10-comp-gcd$out-act)
                           ())))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund q10-comp-gcd$inv (st)
    (b* ((comp-gcd (get-field *q10-comp-gcd$comp-gcd* st)))
      (comp-gcd$inv comp-gcd)))

  (defthm q10-comp-gcd$inv-preserved
    (implies (and (q10-comp-gcd$input-format inputs data-width)
                  (q10-comp-gcd$valid-st st data-width)
                  (q10-comp-gcd$inv st))
             (q10-comp-gcd$inv
              (q10-comp-gcd$step inputs st data-width)))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              q10-comp-gcd$valid-st
                              q10-comp-gcd$inv
                              q10-comp-gcd$step)
                             ()))))
  )

;; The extracted next-state function for Q10-COMP-GCD.  Note that this
;; function avoids exploring the internal computation of Q10-COMP-GCD.

(defund q10-comp-gcd$extracted-step (inputs st data-width)
  (b* ((data (comp-gcd$op (q10-comp-gcd$data-in inputs data-width)))
       (extracted-st (q10-comp-gcd$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (q10-comp-gcd$out-act inputs st data-width) t)
      (cond
       ((equal (q10-comp-gcd$in-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (q10-comp-gcd$in-act inputs st data-width) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(progn
  (local
   (defthm q10-comp-gcd$q10-out-act-inactive
     (implies (equal (nth *link$s*
                          (nth *q10-comp-gcd$l* st))
                     '(t))
              (not (queue10$out-act
                    (q10-comp-gcd$q10-inputs inputs st data-width)
                    (nth *q10-comp-gcd$q10* st)
                    (* 2 data-width))))
     :hints (("Goal"
              :in-theory (e/d (get-field
                               q10-comp-gcd$q10-inputs)
                              ())))))

  (local
   (defthm q10-comp-gcd$comp-gcd-in-act-inactive
     (implies (equal (nth *link$s*
                          (nth *q10-comp-gcd$l* st))
                     '(nil))
              (not (comp-gcd$in-act
                    (q10-comp-gcd$comp-gcd-inputs inputs st data-width)
                    (nth *q10-comp-gcd$comp-gcd* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (e/d (get-field
                               q10-comp-gcd$comp-gcd-inputs)
                              ())))))

  (local
   (defthm q10-comp-gcd-aux-1
     (b* ((q10-inputs (q10-comp-gcd$q10-inputs inputs st data-width)))
       (implies (natp data-width)
                (equal (queue10$data-in q10-inputs (* 2 data-width))
                       (take (* 2 data-width)
                             (nthcdr 2 inputs)))))
     :hints (("Goal" :in-theory (enable q10-comp-gcd$q10-inputs
                                        q10-comp-gcd$data-in
                                        queue10$data-in)))))

  (local
   (defthm q10-comp-gcd-aux-2
     (b* ((comp-gcd-inputs (q10-comp-gcd$comp-gcd-inputs
                            inputs st data-width))
          (l (nth *q10-comp-gcd$l* st))
          (l.d (nth *link$d* l)))
       (implies (and (natp data-width)
                     (equal (len l.d) (* 2 data-width))
                     (bvp (strip-cars l.d)))
                (equal (comp-gcd$data-in comp-gcd-inputs data-width)
                       (strip-cars l.d))))
     :hints (("Goal" :in-theory (enable get-field
                                        q10-comp-gcd$comp-gcd-inputs
                                        comp-gcd$data-in)))))

  (local
   (defthm q10-comp-gcd$op-map-of-append-instance
     (equal (q10-comp-gcd$op-map (append x (list (strip-cars d))))
            (append (q10-comp-gcd$op-map x)
                    (q10-comp-gcd$op-map (list (strip-cars d)))))))

  (defthm q10-comp-gcd$extracted-step-correct
    (b* ((next-st (q10-comp-gcd$step inputs st data-width)))
      (implies (and (q10-comp-gcd$input-format inputs data-width)
                    (q10-comp-gcd$valid-st st data-width)
                    (q10-comp-gcd$inv st))
               (equal (q10-comp-gcd$extract next-st)
                      (q10-comp-gcd$extracted-step inputs st data-width))))
    :hints
    (("Goal"
      :use (q10-comp-gcd$input-format=>q10$input-format
            q10-comp-gcd$input-format=>comp-gcd$input-format)
      :in-theory (e/d (get-field
                       f-sr
                       comp-gcd$valid-st=>data-width-constraint
                       queue10$extracted-step
                       comp-gcd$extracted-step
                       q10-comp-gcd$extracted-step
                       q10-comp-gcd$valid-st
                       q10-comp-gcd$inv
                       q10-comp-gcd$step
                       q10-comp-gcd$data-in
                       q10-comp-gcd$in-act
                       q10-comp-gcd$out-act
                       q10-comp-gcd$data-out
                       q10-comp-gcd$extract)
                      (q10-comp-gcd$input-format=>q10$input-format
                       q10-comp-gcd$input-format=>comp-gcd$input-format
                       q10-comp-gcd$op-map-of-append
                       nfix)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that q10-comp-gcd$valid-st is an invariant.

(defthm q10-comp-gcd$valid-st-preserved
  (implies (and (q10-comp-gcd$input-format inputs data-width)
                (q10-comp-gcd$valid-st st data-width))
           (q10-comp-gcd$valid-st
            (q10-comp-gcd$step inputs st data-width)
            data-width))
  :hints
  (("Goal"
    :use (q10-comp-gcd$input-format=>q10$input-format
          q10-comp-gcd$input-format=>comp-gcd$input-format)
    :in-theory (e/d (get-field
                     f-sr
                     q10-comp-gcd$valid-st
                     q10-comp-gcd$step)
                    (q10-comp-gcd$input-format=>q10$input-format
                     q10-comp-gcd$input-format=>comp-gcd$input-format)))))

(defthm q10-comp-gcd$extract-lemma
  (implies (and (q10-comp-gcd$valid-st st data-width)
                (q10-comp-gcd$inv st)
                (q10-comp-gcd$out-act inputs st data-width))
           (equal (list (q10-comp-gcd$data-out inputs st data-width))
                  (nthcdr (1- (len (q10-comp-gcd$extract st)))
                          (q10-comp-gcd$extract st))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (q10-comp-gcd$valid-st
                            q10-comp-gcd$inv
                            q10-comp-gcd$extract
                            q10-comp-gcd$out-act
                            q10-comp-gcd$data-out)
                           ()))))

;; Extract the accepted input sequence

(seq-gen q10-comp-gcd in in-act 0
         (q10-comp-gcd$data-in inputs data-width))

;; Extract the valid output sequence

(seq-gen q10-comp-gcd out out-act 1
         (q10-comp-gcd$data-out inputs st data-width)
         :netlist-data (nthcdr 2 outputs))

;; The multi-step input-output relationship

(in-out-stream-lemma q10-comp-gcd :op t :inv t)

