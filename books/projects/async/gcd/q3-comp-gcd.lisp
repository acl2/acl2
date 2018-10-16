;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2018

(in-package "ADE")

(include-book "comp-gcd")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of Q3-COMP-GCD
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of Q3-COMP-GCD
;;
;; Construct a DE module generator that concatenates Q3 with COMP-GCD via a
;; link.  Prove the value and state lemmas for this module generator.

(defconst *q3-comp-gcd$go-num* (+ *queue3$go-num*
                                  *comp-gcd$go-num*))
(defconst *q3-comp-gcd$st-len* 3)

(defun q3-comp-gcd$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun q3-comp-gcd$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (q3-comp-gcd$data-ins-len data-width)
     *q3-comp-gcd$go-num*))

;; DE module generator of Q3-COMP-GCD

(module-generator
 q3-comp-gcd* (data-width)
 (si 'q3-comp-gcd data-width)
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 (* 2 data-width))
                                     (sis 'go 0 *q3-comp-gcd$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-width))
 '(l q3 comp-gcd)
 (list
  ;; LINK
  ;; L
  (list 'l
        (list* 'l-status (sis 'd-out 0 (* 2 data-width)))
        (si 'link (* 2 data-width))
        (list* 'q3-out-act 'comp-gcd-in-act
               (sis 'q3-data-out 0 (* 2 data-width))))

  ;; JOINTS
  ;; Q3
  (list 'q3
        (list* 'in-act 'q3-out-act
               (sis 'q3-data-out 0 (* 2 data-width)))
        (si 'queue3 (* 2 data-width))
        (list* 'full-in 'l-status
               (append (sis 'data-in 0 (* 2 data-width))
                       (sis 'go 0 *queue3$go-num*))))

  ;; COMP-GCD
  (list 'comp-gcd
        (list* 'comp-gcd-in-act 'out-act
               (sis 'data-out 0 data-width))
        (si 'comp-gcd data-width)
        (list* 'l-status 'empty-out-
               (append (sis 'd-out 0 (* 2 data-width))
                       (sis 'go
                            *queue3$go-num*
                            *comp-gcd$go-num*)))))

 :guard (natp data-width))

(make-event
 `(progn
    ,@(state-accessors-gen 'q3-comp-gcd '(l q3 comp-gcd) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; Q3-COMP-GCD.

(defun q3-comp-gcd$netlist (data-width)
  (declare (xargs :guard (and (natp data-width)
                              (<= 2 data-width))))
  (cons (q3-comp-gcd* data-width)
        (union$ (queue3$netlist (* 2 data-width))
                (comp-gcd$netlist data-width)
                :test 'equal)))

;; Recognizer for Q3-COMP-GCD

(defund q3-comp-gcd& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width)
                              (<= 2 data-width))))
  (and (equal (assoc (si 'q3-comp-gcd data-width) netlist)
              (q3-comp-gcd* data-width))
       (b* ((netlist (delete-to-eq (si 'q3-comp-gcd data-width)
                                   netlist)))
         (and (link& netlist (* 2 data-width))
              (queue3& netlist (* 2 data-width))
              (comp-gcd& netlist data-width)))))

;; Sanity check

(local
 (defthmd check-q3-comp-gcd$netlist-64
   (and (net-syntax-okp (q3-comp-gcd$netlist 64))
        (net-arity-okp (q3-comp-gcd$netlist 64))
        (q3-comp-gcd& (q3-comp-gcd$netlist 64) 64))))

;; Constraints on the state of Q3-COMP-GCD

(defund q3-comp-gcd$st-format (st data-width)
  (b* ((l        (get-field *q3-comp-gcd$l* st))
       (q3       (get-field *q3-comp-gcd$q3* st))
       (comp-gcd (get-field *q3-comp-gcd$comp-gcd* st)))
    (and (link$st-format l (* 2 data-width))
         (queue3$st-format q3 (* 2 data-width))
         (comp-gcd$st-format comp-gcd data-width))))

(defthm q3-comp-gcd$st-format=>data-width-constraint
  (implies (q3-comp-gcd$st-format st data-width)
           (and (natp data-width)
                (<= 3 data-width)))
  :hints (("Goal"
           :in-theory (enable q3-comp-gcd$st-format)))
  :rule-classes :forward-chaining)

(defund q3-comp-gcd$valid-st (st data-width)
  (b* ((l        (get-field *q3-comp-gcd$l* st))
       (q3       (get-field *q3-comp-gcd$q3* st))
       (comp-gcd (get-field *q3-comp-gcd$comp-gcd* st)))
    (and (link$valid-st l (* 2 data-width))
         (queue3$valid-st q3 (* 2 data-width))
         (comp-gcd$valid-st comp-gcd data-width))))

(defthmd q3-comp-gcd$valid-st=>data-width-constraint
  (implies (q3-comp-gcd$valid-st st data-width)
           (and (natp data-width)
                (<= 3 data-width)))
  :hints (("Goal"
           :in-theory (enable comp-gcd$valid-st=>data-width-constraint
                              q3-comp-gcd$valid-st)))
  :rule-classes :forward-chaining)

(defthmd q3-comp-gcd$valid-st=>st-format
  (implies (q3-comp-gcd$valid-st st data-width)
           (q3-comp-gcd$st-format st data-width))
  :hints (("Goal" :in-theory (e/d (queue3$valid-st=>st-format
                                   comp-gcd$valid-st=>st-format
                                   q3-comp-gcd$st-format
                                   q3-comp-gcd$valid-st)
                                  (link$st-format)))))

;; Extract the input and output signals for Q3-COMP-GCD

(progn
  ;; Extract the input data

  (defun q3-comp-gcd$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (* 2 (mbe :logic (nfix data-width)
                    :exec  data-width))
          (nthcdr 2 inputs)))

  (defthm len-q3-comp-gcd$data-in
    (equal (len (q3-comp-gcd$data-in inputs data-width))
           (* 2 (nfix data-width))))

  (in-theory (disable q3-comp-gcd$data-in))

  ;; Extract the inputs for the Q3 joint

  (defund q3-comp-gcd$q3-inputs (inputs st data-width)
    (b* ((full-in (nth 0 inputs))
         (data-in (q3-comp-gcd$data-in inputs data-width))
         (go-signals (nthcdr (q3-comp-gcd$data-ins-len data-width)
                             inputs))

         (q3-go-signals (take *queue3$go-num* go-signals))

         (l (get-field *q3-comp-gcd$l* st))
         (l.s (get-field *link$s* l)))

      (list* full-in (f-buf (car l.s))
             (append data-in q3-go-signals))))

  ;; Extract the inputs for the COMP-GCD joint

  (defund q3-comp-gcd$comp-gcd-inputs (inputs st data-width)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (q3-comp-gcd$data-ins-len data-width)
                             inputs))

         (comp-gcd-go-signals (take *comp-gcd$go-num*
                                    (nthcdr *queue3$go-num* go-signals)))

         (l (get-field *q3-comp-gcd$l* st))
         (l.s (get-field *link$s* l))
         (l.d (get-field *link$d* l)))

      (list* (f-buf (car l.s)) empty-out-
             (append (v-threefix (strip-cars l.d))
                     comp-gcd-go-signals))))

  ;; Extract the "in-act" signal

  (defund q3-comp-gcd$in-act (inputs st data-width)
    (queue3$in-act (q3-comp-gcd$q3-inputs inputs st data-width)
                   (get-field *q3-comp-gcd$q3* st)
                   (* 2 data-width)))

  (defthm q3-comp-gcd$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (q3-comp-gcd$in-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable q3-comp-gcd$q3-inputs
                                       q3-comp-gcd$in-act))))

  ;; Extract the "out-act" signal

  (defund q3-comp-gcd$out-act (inputs st data-width)
    (comp-gcd$out-act (q3-comp-gcd$comp-gcd-inputs inputs st data-width)
                      (get-field *q3-comp-gcd$comp-gcd* st)
                      data-width))

  (defthm q3-comp-gcd$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (q3-comp-gcd$out-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable q3-comp-gcd$comp-gcd-inputs
                                       q3-comp-gcd$out-act))))

  ;; Extract the output data

  (defund q3-comp-gcd$data-out (inputs st data-width)
    (comp-gcd$data-out (q3-comp-gcd$comp-gcd-inputs inputs st data-width)
                       (get-field *q3-comp-gcd$comp-gcd* st)
                       data-width))

  (defthm len-q3-comp-gcd$data-out-1
    (implies (q3-comp-gcd$st-format st data-width)
             (equal (len (q3-comp-gcd$data-out inputs st data-width))
                    data-width))
    :hints (("Goal" :in-theory (enable q3-comp-gcd$st-format
                                       q3-comp-gcd$data-out))))

  (defthm len-q3-comp-gcd$data-out-2
    (implies (q3-comp-gcd$valid-st st data-width)
             (equal (len (q3-comp-gcd$data-out inputs st data-width))
                    data-width))
    :hints (("Goal" :in-theory (enable q3-comp-gcd$valid-st
                                       q3-comp-gcd$data-out))))

  (defthm bvp-q3-comp-gcd$data-out
    (implies (and (q3-comp-gcd$valid-st st data-width)
                  (q3-comp-gcd$out-act inputs st data-width))
             (bvp (q3-comp-gcd$data-out inputs st data-width)))
    :hints (("Goal" :in-theory (enable q3-comp-gcd$valid-st
                                       q3-comp-gcd$out-act
                                       q3-comp-gcd$data-out))))

  (defun q3-comp-gcd$outputs (inputs st data-width)
    (list* (q3-comp-gcd$in-act inputs st data-width)
           (q3-comp-gcd$out-act inputs st data-width)
           (q3-comp-gcd$data-out inputs st data-width)))
  )

;; Prove that Q3-COMP-GCD is not a DE primitive.

(not-primp-lemma q3-comp-gcd)

;; The value lemma for Q3-COMP-GCD

(defthm q3-comp-gcd$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies
     (and (q3-comp-gcd& netlist data-width)
          (true-listp data-in)
          (equal (len data-in) (* 2 data-width))
          (true-listp go-signals)
          (equal (len go-signals) *q3-comp-gcd$go-num*)
          (q3-comp-gcd$st-format st data-width))
     (equal (se (si 'q3-comp-gcd data-width) inputs st netlist)
            (q3-comp-gcd$outputs inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'q3-comp-gcd data-width)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            q3-comp-gcd&
                            q3-comp-gcd*$destructure
                            q3-comp-gcd$data-in
                            q3-comp-gcd$st-format
                            q3-comp-gcd$in-act
                            q3-comp-gcd$out-act
                            q3-comp-gcd$data-out
                            q3-comp-gcd$q3-inputs
                            q3-comp-gcd$comp-gcd-inputs)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of Q3-COMP-GCD.

(defun q3-comp-gcd$step (inputs st data-width)
  (b* ((l   (get-field *q3-comp-gcd$l* st))
       (q3  (get-field *q3-comp-gcd$q3* st))
       (comp-gcd (get-field *q3-comp-gcd$comp-gcd* st))

       (q3-inputs (q3-comp-gcd$q3-inputs inputs st data-width))
       (comp-gcd-inputs (q3-comp-gcd$comp-gcd-inputs
                         inputs st data-width))

       (d-in (queue3$data-out q3))

       (q3-out-act (queue3$out-act q3-inputs q3 (* 2 data-width)))
       (comp-gcd-in-act (comp-gcd$in-act comp-gcd-inputs
                                         comp-gcd data-width))

       (l-inputs (list* q3-out-act comp-gcd-in-act d-in)))
    (list
     ;; L
     (link$step l-inputs l (* 2 data-width))
     ;; Joint Q3
     (queue3$step q3-inputs q3 (* 2 data-width))
     ;; Joint COMP-GCD
     (comp-gcd$step comp-gcd-inputs comp-gcd data-width))))

(defthm len-of-q3-comp-gcd$step
  (equal (len (q3-comp-gcd$step inputs st data-width))
         *q3-comp-gcd$st-len*))

;; The state lemma for Q3-COMP-GCD

(defthm q3-comp-gcd$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies
     (and (q3-comp-gcd& netlist data-width)
          (true-listp data-in)
          (equal (len data-in) (* 2 data-width))
          (true-listp go-signals)
          (equal (len go-signals) *q3-comp-gcd$go-num*)
          (q3-comp-gcd$st-format st data-width))
     (equal (de (si 'q3-comp-gcd data-width) inputs st netlist)
            (q3-comp-gcd$step inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'q3-comp-gcd data-width)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            q3-comp-gcd&
                            q3-comp-gcd*$destructure
                            q3-comp-gcd$st-format
                            q3-comp-gcd$data-in
                            q3-comp-gcd$data-out
                            q3-comp-gcd$q3-inputs
                            q3-comp-gcd$comp-gcd-inputs)
                           (de-module-disabled-rules)))))

(in-theory (disable q3-comp-gcd$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund q3-comp-gcd$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (q3-comp-gcd$data-in inputs data-width))
       (go-signals (nthcdr (q3-comp-gcd$data-ins-len data-width)
                           inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *q3-comp-gcd$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(local
 (defthm q3-comp-gcd$input-format=>q3$input-format
   (implies (and (q3-comp-gcd$input-format inputs data-width)
                 (q3-comp-gcd$valid-st st data-width))
            (queue3$input-format
             (q3-comp-gcd$q3-inputs inputs st data-width)
             (* 2 data-width)))
   :hints (("Goal"
            :in-theory (e/d (q3-comp-gcd$input-format
                             comp-gcd$valid-st=>data-width-constraint
                             queue3$input-format
                             queue3$data-in
                             q3-comp-gcd$valid-st
                             q3-comp-gcd$q3-inputs)
                            ())))))

(local
 (defthm q3-comp-gcd$input-format=>comp-gcd$input-format
   (implies (and (q3-comp-gcd$input-format inputs data-width)
                 (q3-comp-gcd$valid-st st data-width))
            (comp-gcd$input-format
             (q3-comp-gcd$comp-gcd-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (q3-comp-gcd$input-format
                             comp-gcd$valid-st=>data-width-constraint
                             comp-gcd$input-format
                             comp-gcd$data-in
                             q3-comp-gcd$valid-st
                             q3-comp-gcd$st-format
                             q3-comp-gcd$comp-gcd-inputs)
                            ())))))

(defthm booleanp-q3-comp-gcd$in-act
  (implies (and (q3-comp-gcd$input-format inputs data-width)
                (q3-comp-gcd$valid-st st data-width))
           (booleanp (q3-comp-gcd$in-act inputs st data-width)))
  :hints
  (("Goal"
    :use q3-comp-gcd$input-format=>q3$input-format
    :in-theory (e/d (q3-comp-gcd$valid-st
                     q3-comp-gcd$in-act)
                    (q3-comp-gcd$input-format=>q3$input-format))))
  :rule-classes :type-prescription)

(defthm booleanp-q3-comp-gcd$out-act
  (implies (and (q3-comp-gcd$input-format inputs data-width)
                (q3-comp-gcd$valid-st st data-width))
           (booleanp (q3-comp-gcd$out-act inputs st data-width)))
  :hints
  (("Goal"
    :use q3-comp-gcd$input-format=>comp-gcd$input-format
    :in-theory (e/d (q3-comp-gcd$valid-st
                     q3-comp-gcd$out-act)
                    (q3-comp-gcd$input-format=>comp-gcd$input-format))))
  :rule-classes :type-prescription)

(simulate-lemma q3-comp-gcd)

;; ======================================================================

;; 3. Single-Step-Update Property

;; The operation of Q3-COMP-GCD over a data sequence

(defun q3-comp-gcd$op-map (x)
  (if (atom x)
      nil
    (cons (comp-gcd$op (car x))
          (q3-comp-gcd$op-map (cdr x)))))

(defthm len-of-q3-comp-gcd$op-map
  (equal (len (q3-comp-gcd$op-map x))
         (len x)))

(defthm q3-comp-gcd$op-map-of-append
  (equal (q3-comp-gcd$op-map (append x y))
         (append (q3-comp-gcd$op-map x) (q3-comp-gcd$op-map y))))

;; The extraction function for Q3-COMP-GCD that extracts the future output
;; sequence from the current state.

(defund q3-comp-gcd$extract (st)
  (b* ((l   (get-field *q3-comp-gcd$l* st))
       (q3  (get-field *q3-comp-gcd$q3* st))
       (comp-gcd (get-field *q3-comp-gcd$comp-gcd* st)))
    (append
     (q3-comp-gcd$op-map
      (append (queue3$extract q3)
              (extract-valid-data (list l))))
     (comp-gcd$extract comp-gcd))))

(defthm q3-comp-gcd$extract-not-empty
  (implies (and (q3-comp-gcd$out-act inputs st data-width)
                (q3-comp-gcd$valid-st st data-width))
           (< 0 (len (q3-comp-gcd$extract st))))
  :hints (("Goal"
           :in-theory (e/d (q3-comp-gcd$valid-st
                            q3-comp-gcd$extract
                            q3-comp-gcd$out-act)
                           ())))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund q3-comp-gcd$inv (st)
    (b* ((comp-gcd (get-field *q3-comp-gcd$comp-gcd* st)))
      (comp-gcd$inv comp-gcd)))

  (defthm q3-comp-gcd$inv-preserved
    (implies (and (q3-comp-gcd$input-format inputs data-width)
                  (q3-comp-gcd$valid-st st data-width)
                  (q3-comp-gcd$inv st))
             (q3-comp-gcd$inv
              (q3-comp-gcd$step inputs st data-width)))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              q3-comp-gcd$valid-st
                              q3-comp-gcd$inv
                              q3-comp-gcd$step)
                             ()))))
  )

;; The extracted next-state function for Q3-COMP-GCD.  Note that this
;; function avoids exploring the internal computation of Q3-COMP-GCD.

(defund q3-comp-gcd$extracted-step (inputs st data-width)
  (b* ((data (comp-gcd$op (q3-comp-gcd$data-in inputs data-width)))
       (extracted-st (q3-comp-gcd$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (q3-comp-gcd$out-act inputs st data-width) t)
      (cond
       ((equal (q3-comp-gcd$in-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (q3-comp-gcd$in-act inputs st data-width) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(progn
  (local
   (defthm q3-comp-gcd$q3-out-act-inactive
     (implies (equal (nth *link$s*
                          (nth *q3-comp-gcd$l* st))
                     '(t))
              (not (queue3$out-act
                    (q3-comp-gcd$q3-inputs inputs st data-width)
                    (nth *q3-comp-gcd$q3* st)
                    (* 2 data-width))))
     :hints (("Goal"
              :in-theory (e/d (get-field
                               q3-comp-gcd$q3-inputs)
                              ())))))

  (local
   (defthm q3-comp-gcd$comp-gcd-in-act-inactive
     (implies (equal (nth *link$s*
                          (nth *q3-comp-gcd$l* st))
                     '(nil))
              (not (comp-gcd$in-act
                    (q3-comp-gcd$comp-gcd-inputs inputs st data-width)
                    (nth *q3-comp-gcd$comp-gcd* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (e/d (get-field
                               q3-comp-gcd$comp-gcd-inputs)
                              ())))))

  (local
   (defthm q3-comp-gcd-aux-1
     (b* ((q3-inputs (q3-comp-gcd$q3-inputs inputs st data-width)))
       (implies (natp data-width)
                (equal (queue3$data-in q3-inputs (* 2 data-width))
                       (take (* 2 data-width)
                             (nthcdr 2 inputs)))))
     :hints (("Goal" :in-theory (enable q3-comp-gcd$q3-inputs
                                        q3-comp-gcd$data-in
                                        queue3$data-in)))))

  (local
   (defthm q3-comp-gcd-aux-2
     (b* ((comp-gcd-inputs (q3-comp-gcd$comp-gcd-inputs
                            inputs st data-width))
          (l (nth *q3-comp-gcd$l* st))
          (l.d (nth *link$d* l)))
       (implies (and (natp data-width)
                     (equal (len l.d) (* 2 data-width))
                     (bvp (strip-cars l.d)))
                (equal (comp-gcd$data-in comp-gcd-inputs data-width)
                       (strip-cars l.d))))
     :hints (("Goal" :in-theory (enable get-field
                                        q3-comp-gcd$comp-gcd-inputs
                                        comp-gcd$data-in)))))

  (local
   (defthm q3-comp-gcd$op-map-of-append-instance
     (equal (q3-comp-gcd$op-map (append x (list (strip-cars d))))
            (append (q3-comp-gcd$op-map x)
                    (q3-comp-gcd$op-map (list (strip-cars d)))))))

  (defthm q3-comp-gcd$extracted-step-correct
    (b* ((next-st (q3-comp-gcd$step inputs st data-width)))
      (implies (and (q3-comp-gcd$input-format inputs data-width)
                    (q3-comp-gcd$valid-st st data-width)
                    (q3-comp-gcd$inv st))
               (equal (q3-comp-gcd$extract next-st)
                      (q3-comp-gcd$extracted-step inputs st data-width))))
    :hints
    (("Goal"
      :use (q3-comp-gcd$input-format=>q3$input-format
            q3-comp-gcd$input-format=>comp-gcd$input-format)
      :in-theory (e/d (get-field
                       f-sr
                       comp-gcd$valid-st=>data-width-constraint
                       queue3$extracted-step
                       comp-gcd$extracted-step
                       q3-comp-gcd$extracted-step
                       q3-comp-gcd$valid-st
                       q3-comp-gcd$inv
                       q3-comp-gcd$step
                       q3-comp-gcd$data-in
                       q3-comp-gcd$in-act
                       q3-comp-gcd$out-act
                       q3-comp-gcd$data-out
                       q3-comp-gcd$extract)
                      (q3-comp-gcd$input-format=>q3$input-format
                       q3-comp-gcd$input-format=>comp-gcd$input-format
                       q3-comp-gcd$op-map-of-append
                       nfix)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that q3-comp-gcd$valid-st is an invariant.

(defthm q3-comp-gcd$valid-st-preserved
  (implies (and (q3-comp-gcd$input-format inputs data-width)
                (q3-comp-gcd$valid-st st data-width))
           (q3-comp-gcd$valid-st
            (q3-comp-gcd$step inputs st data-width)
            data-width))
  :hints
  (("Goal"
    :use (q3-comp-gcd$input-format=>q3$input-format
          q3-comp-gcd$input-format=>comp-gcd$input-format)
    :in-theory (e/d (get-field
                     f-sr
                     q3-comp-gcd$valid-st
                     q3-comp-gcd$step)
                    (q3-comp-gcd$input-format=>q3$input-format
                     q3-comp-gcd$input-format=>comp-gcd$input-format)))))

(defthm q3-comp-gcd$extract-lemma
  (implies (and (q3-comp-gcd$valid-st st data-width)
                (q3-comp-gcd$inv st)
                (q3-comp-gcd$out-act inputs st data-width))
           (equal (list (q3-comp-gcd$data-out inputs st data-width))
                  (nthcdr (1- (len (q3-comp-gcd$extract st)))
                          (q3-comp-gcd$extract st))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (q3-comp-gcd$valid-st
                            q3-comp-gcd$inv
                            q3-comp-gcd$extract
                            q3-comp-gcd$out-act
                            q3-comp-gcd$data-out)
                           ()))))

;; Extract the accepted input sequence

(seq-gen q3-comp-gcd in in-act 0
         (q3-comp-gcd$data-in inputs data-width))

;; Extract the valid output sequence

(seq-gen q3-comp-gcd out out-act 1
         (q3-comp-gcd$data-out inputs st data-width)
         :netlist-data (nthcdr 2 outputs))

;; The multi-step input-output relationship

(in-out-stream-lemma q3-comp-gcd :op t :inv t)

