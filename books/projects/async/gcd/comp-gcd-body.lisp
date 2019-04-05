;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; February 2019

(in-package "ADE")

(include-book "../link-joint")
(include-book "../tv-if")
(include-book "../vector-module")
(include-book "../adders/subtractor")
(include-book "../comparators/v-less")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of COMP-GCD-BODY
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of COMP-GCD-BODY
;;
;; COMP-GCD-BODY performs the GCD operation in one iteration.  It is
;; constructed using the ripple-carry subtractor RIPPLE-SUB.

(defconst *comp-gcd-body$go-num* 3)
(defconst *comp-gcd-body$st-len* 3)

(defun comp-gcd-body$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (* 2 (mbe :logic (nfix data-size)
                 :exec  data-size))))

(defun comp-gcd-body$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (comp-gcd-body$data-ins-len data-size)
     *comp-gcd-body$go-num*))

(module-generator
 comp-gcd-body* (data-size)
 (si 'comp-gcd-body data-size)
 (list* 'full-in 'empty-out-
        (append (sis 'data-in 0 (* 2 data-size))
                (sis 'go 0 *comp-gcd-body$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 (* 2 data-size)))
 '(l0 l1 l2)
 (list
  ;; LINKS
  ;; L0
  (list 'l0
        (list* 'l0-status (sis 'd0-out 0 (* 2 data-size)))
        (si 'link (* 2 data-size))
        (list* 'in-act 'sub-act (sis 'd0-in 0 (* 2 data-size))))

  ;; L1
  (list 'l1
        (list* 'l1-status (sis 'd1-out 0 data-size))
        (si 'link data-size)
        (list* 'in-act 'out-act (sis 'd1-in 0 data-size)))

  ;; L2
  (list 'l2
        (list* 'l2-status (sis 'd2-out 0 data-size))
        (si 'link data-size)
        (list* 'sub-act 'out-act (sis 'd2-in 0 data-size)))

  ;; JOINTS
  ;; In
  '(g0 (ready-in-) b-or (l0-status l1-status))
  (list 'in-cntl
        '(in-act)
        'joint-cntl
        (list 'full-in 'ready-in- (si 'go 0)))
  (list 'in-op0
        '(a<b)
        (si 'v-< data-size)
        (append (rev (sis 'data-in 0 data-size))
                (rev (sis 'data-in data-size data-size))))
  (list 'in-op1
        (sis 'd0-in 0 (* 2 data-size))
        (si 'tv-if (tree-number (make-tree (* 2 data-size))))
        (cons 'a<b
              (append (append (sis 'data-in data-size data-size)
                              (sis 'data-in 0 data-size))
                      (sis 'data-in 0 (* 2 data-size)))))
  (list 'in-op2
        (sis 'd1-in 0 data-size)
        (si 'tv-if (tree-number (make-tree data-size)))
        (cons 'a<b
              (append (sis 'data-in 0 data-size)
                      (sis 'data-in data-size data-size))))

  ;; Sub
  (list 'sub-cntl
        '(sub-act)
        'joint-cntl
        (list 'l0-status 'l2-status (si 'go 2)))
  (list 'sub-op
        (sis 'd2-in 0 (1+ data-size))
        (si 'ripple-sub data-size)
        (append (sis 'd0-out 0 data-size)
                (sis 'd0-out data-size data-size)))

  ;; Out
  '(g1 (ready-out) b-and (l1-status l2-status))
  (list 'out-cntl
        '(out-act)
        'joint-cntl
        (list 'ready-out 'empty-out- (si 'go 1)))
  (list 'out-op
        (sis 'data-out 0 (* 2 data-size))
        (si 'v-wire (* 2 data-size))
        (append (sis 'd2-out 0 data-size)
                (sis 'd1-out 0 data-size))))
 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'comp-gcd-body '(l0 l1 l2) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; COMP-GCD-BODY.

(defund comp-gcd-body$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (comp-gcd-body* data-size)
        (union$ (link$netlist data-size)
                (link$netlist (* 2 data-size))
                *joint-cntl*
                (tv-if$netlist (make-tree data-size))
                (tv-if$netlist (make-tree (* 2 data-size)))
                (v-wire$netlist (* 2 data-size))
                (v-<$netlist data-size)
                (ripple-sub$netlist data-size)
                :test 'equal)))

;; Recognizer for COMP-GCD-BODY

(defund comp-gcd-body& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'comp-gcd-body data-size) netlist)))
    (and (equal (assoc (si 'comp-gcd-body data-size) netlist)
                (comp-gcd-body* data-size))
         (link& subnetlist data-size)
         (link& subnetlist (* 2 data-size))
         (joint-cntl& subnetlist)
         (tv-if& subnetlist (make-tree data-size))
         (tv-if& subnetlist (make-tree (* 2 data-size)))
         (v-wire& subnetlist (* 2 data-size))
         (v-<& subnetlist data-size)
         (ripple-sub& subnetlist data-size))))

;; Sanity check

(local
 (defthmd check-comp-gcd-body$netlist-64
   (and (net-syntax-okp (comp-gcd-body$netlist 64))
        (net-arity-okp (comp-gcd-body$netlist 64))
        (comp-gcd-body& (comp-gcd-body$netlist 64) 64))))

;; Constraints on the state of COMP-GCD-BODY

(defund comp-gcd-body$st-format (st data-size)
  (b* ((l0 (get-field *comp-gcd-body$l0* st))
       (l1 (get-field *comp-gcd-body$l1* st))
       (l2 (get-field *comp-gcd-body$l2* st)))
    (and (< 0 data-size)
         (link$st-format l0 (* 2 data-size))
         (link$st-format l1 data-size)
         (link$st-format l2 data-size))))

(defthm comp-gcd-body$st-format=>constraint
  (implies (comp-gcd-body$st-format st data-size)
           (posp data-size))
  :hints (("Goal" :in-theory (enable comp-gcd-body$st-format)))
  :rule-classes :forward-chaining)

(defund comp-gcd-body$valid-st (st data-size)
  (b* ((l0 (get-field *comp-gcd-body$l0* st))
       (l1 (get-field *comp-gcd-body$l1* st))
       (l2 (get-field *comp-gcd-body$l2* st)))
    (and (< 0 data-size)
         (link$valid-st l0 (* 2 data-size))
         (link$valid-st l1 data-size)
         (link$valid-st l2 data-size))))

(defthmd comp-gcd-body$valid-st=>constraint
  (implies (comp-gcd-body$valid-st st data-size)
           (posp data-size))
  :hints (("Goal" :in-theory (enable comp-gcd-body$valid-st)))
  :rule-classes :forward-chaining)

(defthmd comp-gcd-body$valid-st=>st-format
  (implies (comp-gcd-body$valid-st st data-size)
           (comp-gcd-body$st-format st data-size))
  :hints (("Goal" :in-theory (e/d (comp-gcd-body$st-format
                                   comp-gcd-body$valid-st)
                                  ()))))

;; Extract the input and output signals for COMP-GCD-BODY

(progn
  ;; Extract the input data

  (defun comp-gcd-body$data-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (* 2 (mbe :logic (nfix data-size)
                    :exec  data-size))
          (nthcdr 2 inputs)))

  (defthm len-comp-gcd-body$data-in
    (equal (len (comp-gcd-body$data-in inputs data-size))
           (* 2 (nfix data-size))))

  (in-theory (disable comp-gcd-body$data-in))

  ;; Extract the "a<b" signal

  (defund comp-gcd-body$a<b (inputs data-size)
    (b* ((data-in (comp-gcd-body$data-in inputs data-size)))
      (fv-< nil t
            (rev (take data-size data-in))
            (rev (nthcdr data-size data-in)))))

  ;; Extract the "in-act" signal

  (defund comp-gcd-body$in-act (inputs st data-size)
    (b* ((full-in (nth 0 inputs))
         (go-signals (nthcdr (comp-gcd-body$data-ins-len data-size) inputs))
         (go-in (nth 0 go-signals))

         (l0 (get-field *comp-gcd-body$l0* st))
         (l0.s (get-field *link$s* l0))
         (l1 (get-field *comp-gcd-body$l1* st))
         (l1.s (get-field *link$s* l1))

         (ready-in- (f-or (car l0.s) (car l1.s))))
      (joint-act full-in ready-in- go-in)))

  (defthm comp-gcd-body$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (comp-gcd-body$in-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-gcd-body$in-act))))

  ;; Extract the "out-act" signal

  (defund comp-gcd-body$out-act (inputs st data-size)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (comp-gcd-body$data-ins-len data-size) inputs))
         (go-out (nth 1 go-signals))

         (l1 (get-field *comp-gcd-body$l1* st))
         (l1.s (get-field *link$s* l1))
         (l2 (get-field *comp-gcd-body$l2* st))
         (l2.s (get-field *link$s* l2))

         (ready-out (f-and (car l1.s) (car l2.s))))
      (joint-act ready-out empty-out- go-out)))

  (defthm comp-gcd-body$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (comp-gcd-body$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-gcd-body$out-act))))

  (defthm comp-gcd-body$in-out-acts-mutually-exclusive
    (implies (and (comp-gcd-body$valid-st st data-size)
                  (comp-gcd-body$in-act inputs st data-size))
             (not (comp-gcd-body$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-gcd-body$valid-st
                                       comp-gcd-body$in-act
                                       comp-gcd-body$out-act))))

  ;; Extract the output data

  (defund comp-gcd-body$data-out (st)
    (b* ((l1 (get-field *comp-gcd-body$l1* st))
         (l1.d (get-field *link$d* l1))
         (l2 (get-field *comp-gcd-body$l2* st))
         (l2.d (get-field *link$d* l2)))
      (append (v-threefix (strip-cars l2.d))
              (v-threefix (strip-cars l1.d)))))

  (defthm len-comp-gcd-body$data-out-1
    (implies (comp-gcd-body$st-format st data-size)
             (equal (len (comp-gcd-body$data-out st))
                    (* 2 data-size)))
    :hints (("Goal" :in-theory (enable comp-gcd-body$st-format
                                       comp-gcd-body$data-out))))

  (defthm len-comp-gcd-body$data-out-2
    (implies (comp-gcd-body$valid-st st data-size)
             (equal (len (comp-gcd-body$data-out st))
                    (* 2 data-size)))
    :hints (("Goal" :in-theory (enable comp-gcd-body$valid-st
                                       comp-gcd-body$data-out))))

  (defthm bvp-comp-gcd-body$data-out
    (implies (and (comp-gcd-body$valid-st st data-size)
                  (comp-gcd-body$out-act inputs st data-size))
             (bvp (comp-gcd-body$data-out st)))
    :hints (("Goal" :in-theory (enable comp-gcd-body$valid-st
                                       comp-gcd-body$out-act
                                       comp-gcd-body$data-out))))

  (defun comp-gcd-body$outputs (inputs st data-size)
    (list* (comp-gcd-body$in-act inputs st data-size)
           (comp-gcd-body$out-act inputs st data-size)
           (comp-gcd-body$data-out st)))
  )

;; The value lemma for COMP-GCD-BODY

(defthm comp-gcd-body$value
  (b* ((inputs (list* full-in empty-out-
                      (append data-in go-signals))))
    (implies (and (comp-gcd-body& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-size))
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-gcd-body$go-num*)
                  (comp-gcd-body$st-format st data-size))
             (equal (se (si 'comp-gcd-body data-size) inputs st netlist)
                    (comp-gcd-body$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'comp-gcd-body data-size)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            comp-gcd-body&
                            comp-gcd-body*$destructure
                            comp-gcd-body$st-format
                            comp-gcd-body$in-act
                            comp-gcd-body$out-act
                            comp-gcd-body$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of COMP-GCD-BODY.

(defun comp-gcd-body$step (inputs st data-size)
  (b* ((data-in (comp-gcd-body$data-in inputs data-size))
       (go-signals (nthcdr (comp-gcd-body$data-ins-len data-size) inputs))

       (go-sub (nth 2 go-signals))

       (l0 (get-field *comp-gcd-body$l0* st))
       (l0.s (get-field *link$s* l0))
       (l0.d (get-field *link$d* l0))
       (l1 (get-field *comp-gcd-body$l1* st))
       (l2 (get-field *comp-gcd-body$l2* st))
       (l2.s (get-field *link$s* l2))

       (in-act (comp-gcd-body$in-act inputs st data-size))
       (out-act (comp-gcd-body$out-act inputs st data-size))
       (sub-act (joint-act (car l0.s) (car l2.s) go-sub))

       (a<b (comp-gcd-body$a<b inputs data-size))
       (d0-in (fv-if a<b
                     (append (nthcdr data-size data-in)
                             (take data-size data-in))
                     data-in))
       (d1-in (fv-if a<b
                     (take data-size data-in)
                     (nthcdr data-size data-in)))
       (d2-in (fv-adder-output t
                               (take data-size (strip-cars l0.d))
                               (fv-not
                                (nthcdr data-size (strip-cars l0.d)))))

       (l0-inputs (list* in-act sub-act d0-in))
       (l1-inputs (list* in-act out-act d1-in))
       (l2-inputs (list* sub-act out-act d2-in)))
    (list
     ;; L0
     (link$step l0-inputs l0 (* 2 data-size))
     ;; L1
     (link$step l1-inputs l1 data-size)
     ;; L2
     (link$step l2-inputs l2 data-size))))

(defthm len-of-comp-gcd-body$step
  (equal (len (comp-gcd-body$step inputs st data-size))
         *comp-gcd-body$st-len*))

;; The state lemma for COMP-GCD-BODY

(defthm comp-gcd-body$state
  (b* ((inputs (list* full-in empty-out-
                      (append data-in go-signals))))
    (implies (and (comp-gcd-body& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-size))
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-gcd-body$go-num*)
                  (comp-gcd-body$st-format st data-size))
             (equal (de (si 'comp-gcd-body data-size) inputs st netlist)
                    (comp-gcd-body$step inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'comp-gcd-body data-size)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            fv-adder-output
                            comp-gcd-body&
                            comp-gcd-body*$destructure
                            comp-gcd-body$st-format
                            comp-gcd-body$data-in
                            comp-gcd-body$a<b
                            comp-gcd-body$in-act
                            comp-gcd-body$out-act)
                           (associativity-of-append
                            append-take-nthcdr
                            append-v-threefix
                            de-module-disabled-rules)))))

(in-theory (disable comp-gcd-body$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund comp-gcd-body$input-format (inputs data-size)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-size))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (comp-gcd-body$data-in inputs data-size))
       (go-signals (nthcdr (comp-gcd-body$data-ins-len data-size) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in)
         (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *comp-gcd-body$go-num*)
     (equal inputs
            (list* full-in empty-out-
                   (append data-in go-signals))))))

(defthm booleanp-comp-gcd-body$in-act
  (implies (and (comp-gcd-body$input-format inputs data-size)
                (comp-gcd-body$valid-st st data-size))
           (booleanp (comp-gcd-body$in-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (e/d (comp-gcd-body$input-format
                            comp-gcd-body$valid-st
                            comp-gcd-body$in-act)
                           ())))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-gcd-body$out-act
  (implies (and (comp-gcd-body$input-format inputs data-size)
                (comp-gcd-body$valid-st st data-size))
           (booleanp (comp-gcd-body$out-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (e/d (comp-gcd-body$input-format
                            comp-gcd-body$valid-st
                            comp-gcd-body$out-act)
                           ())))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma comp-gcd-body)

;; ======================================================================

;; 3. Single-Step-Update Property

;; Specify the functionality of COMP-GCD-BODY

(defund comp-gcd-body$op (x)
  (b* ((data-size (/ (len x) 2))
       (a (take data-size x))
       (b (nthcdr data-size x))
       (a<b (v-< nil t (rev a) (rev b))))
    (cond
     ((or (atom x)
          (zp data-size)
          (not (bvp x)))
      x)
     (t (v-if a<b
              (append (v-adder-output t b (v-not a))
                      a)
              (append (v-adder-output t a (v-not b))
                      b))))))

;; The operation of COMP-GCD-BODY over a data sequence

(defun comp-gcd-body$op-map (x)
  (if (atom x)
      nil
    (cons (comp-gcd-body$op (car x))
          (comp-gcd-body$op-map (cdr x)))))

(defthm comp-gcd-body$op-map-of-append
  (equal (comp-gcd-body$op-map (append x y))
         (append (comp-gcd-body$op-map x)
                 (comp-gcd-body$op-map y))))

;; The extraction function for COMP-GCD-BODY that extracts the future output
;; sequence from the current state.

(defund comp-gcd-body$extract (st data-size)
  (b* ((l0 (get-field *comp-gcd-body$l0* st))
       (l0.s (get-field *link$s* l0))
       (l0.d (get-field *link$d* l0))
       (l1 (get-field *comp-gcd-body$l1* st))
       (l1.s (get-field *link$s* l1))
       (l1.d (get-field *link$d* l1))
       (l2 (get-field *comp-gcd-body$l2* st))
       (l2.d (get-field *link$d* l2)))
    (if (emptyp l1.s)
        nil
      (list
       (append
        (if (fullp l0.s)
            (v-adder-output t
                            (take data-size (strip-cars l0.d))
                            (v-not (nthcdr data-size (strip-cars l0.d))))
          (strip-cars l2.d))
        (strip-cars l1.d))))))

(defthm comp-gcd-body$extract-not-empty
  (implies (and (comp-gcd-body$out-act inputs st data-size)
                (comp-gcd-body$valid-st st data-size))
           (< 0 (len (comp-gcd-body$extract st data-size))))
  :hints (("Goal"
           :in-theory (e/d (comp-gcd-body$valid-st
                            comp-gcd-body$extract
                            comp-gcd-body$out-act)
                           ())))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund comp-gcd-body$inv (st)
    (b* ((l0 (get-field *comp-gcd-body$l0* st))
         (l1 (get-field *comp-gcd-body$l1* st))
         (l2 (get-field *comp-gcd-body$l2* st))

         (len1 (len (extract-valid-data (list l0 l2))))
         (len2 (len (extract-valid-data (list l1)))))
      (equal len1 len2)))

  (defthm comp-gcd-body$inv-preserved
    (implies (and (comp-gcd-body$input-format inputs data-size)
                  (comp-gcd-body$valid-st st data-size)
                  (comp-gcd-body$inv st))
             (comp-gcd-body$inv
              (comp-gcd-body$step inputs st data-size)))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              comp-gcd-body$valid-st
                              comp-gcd-body$inv
                              comp-gcd-body$step
                              comp-gcd-body$in-act
                              comp-gcd-body$out-act)
                             ()))))
  )

;; The extracted next-state function for COMP-GCD-BODY.  Note that this
;; function avoids exploring the internal computation of COMP-GCD-BODY.

(defund comp-gcd-body$extracted-step (inputs st data-size)
  (b* ((data (comp-gcd-body$op (comp-gcd-body$data-in inputs data-size)))
       (extracted-st (comp-gcd-body$extract st data-size))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-gcd-body$out-act inputs st data-size) t)
      (take n extracted-st))
     ((equal (comp-gcd-body$in-act inputs st data-size) t)
      (cons data extracted-st))
     (t extracted-st))))

(local
 (defthm comp-gcd-body$input-format-lemma-1
   (implies (comp-gcd-body$input-format inputs data-size)
            (booleanp (nth 0 inputs)))
   :hints (("Goal" :in-theory (enable comp-gcd-body$input-format)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm comp-gcd-body$input-format-lemma-2
   (implies (comp-gcd-body$input-format inputs data-size)
            (booleanp (nth 1 inputs)))
   :hints (("Goal" :in-theory (enable comp-gcd-body$input-format)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm comp-gcd-body$input-format-lemma-3
   (implies (and (comp-gcd-body$input-format inputs data-size)
                 (nth 0 inputs))
            (bvp (comp-gcd-body$data-in inputs data-size)))
   :hints (("Goal" :in-theory (enable comp-gcd-body$input-format)))))

;; The single-step-update property

(defthm comp-gcd-body$extracted-step-correct
  (b* ((next-st (comp-gcd-body$step inputs st data-size)))
    (implies (and (comp-gcd-body$input-format inputs data-size)
                  (comp-gcd-body$valid-st st data-size)
                  (comp-gcd-body$inv st))
             (equal (comp-gcd-body$extract next-st data-size)
                    (comp-gcd-body$extracted-step inputs st data-size))))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            joint-act
                            pos-len=>cons
                            fv-if-rewrite
                            comp-gcd-body$extracted-step
                            comp-gcd-body$valid-st
                            comp-gcd-body$inv
                            comp-gcd-body$step
                            comp-gcd-body$a<b
                            comp-gcd-body$in-act
                            comp-gcd-body$out-act
                            comp-gcd-body$extract
                            comp-gcd-body$op)
                           ()))))

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that comp-gcd-body$valid-st is an invariant.

(defthm comp-gcd-body$valid-st-preserved
  (implies (and (comp-gcd-body$input-format inputs data-size)
                (comp-gcd-body$valid-st st data-size))
           (comp-gcd-body$valid-st
            (comp-gcd-body$step inputs st data-size)
            data-size))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            f-sr
                            joint-act
                            comp-gcd-body$valid-st
                            comp-gcd-body$step
                            comp-gcd-body$a<b
                            comp-gcd-body$in-act
                            comp-gcd-body$out-act)
                           (if*)))))

(defthm comp-gcd-body$extract-lemma
  (implies (and (comp-gcd-body$valid-st st data-size)
                (comp-gcd-body$inv st)
                (comp-gcd-body$out-act inputs st data-size))
           (equal (list (comp-gcd-body$data-out st))
                  (nthcdr (1- (len (comp-gcd-body$extract st data-size)))
                          (comp-gcd-body$extract st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (comp-gcd-body$valid-st
                            comp-gcd-body$inv
                            comp-gcd-body$extract
                            comp-gcd-body$out-act
                            comp-gcd-body$data-out)
                           ()))))

;; Extract the accepted input sequence

(seq-gen comp-gcd-body in in-act 0
         (comp-gcd-body$data-in inputs data-size))

;; Extract the valid output sequence

(seq-gen comp-gcd-body out out-act 1
         (comp-gcd-body$data-out st)
         :netlist-data (nthcdr 2 outputs))

;; The multi-step input-output relationship

(encapsulate
  ()

  (local
   (defthm comp-gcd-body$dataflow-correct-aux
     (implies (equal (append x y1)
                     (append (comp-gcd-body$op-map seq) y2))
              (equal (append x y1 z)
                     (append (comp-gcd-body$op-map seq)
                             y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (associativity-of-append))))))

  (defthmd comp-gcd-body$dataflow-correct
    (b* ((extracted-st (comp-gcd-body$extract st data-size))
         (final-st (comp-gcd-body$run
                    inputs-seq st data-size n))
         (final-extracted-st (comp-gcd-body$extract final-st data-size)))
      (implies
       (and (comp-gcd-body$input-format-n inputs-seq data-size n)
            (comp-gcd-body$valid-st st data-size)
            (comp-gcd-body$inv st))
       (equal (append final-extracted-st
                      (comp-gcd-body$out-seq
                       inputs-seq st data-size n))
              (append (comp-gcd-body$op-map
                       (comp-gcd-body$in-seq
                        inputs-seq st data-size n))
                      extracted-st))))
    :hints (("Goal"
             :in-theory (enable comp-gcd-body$extracted-step))))

  (defthmd comp-gcd-body$functionally-correct
    (b* ((extracted-st (comp-gcd-body$extract st data-size))
         (final-st (de-n (si 'comp-gcd-body data-size)
                         inputs-seq st netlist n))
         (final-extracted-st (comp-gcd-body$extract final-st data-size)))
      (implies
       (and (comp-gcd-body& netlist data-size)
            (comp-gcd-body$input-format-n inputs-seq data-size n)
            (comp-gcd-body$valid-st st data-size)
            (comp-gcd-body$inv st))
       (equal (append final-extracted-st
                      (comp-gcd-body$out-seq-netlist
                       inputs-seq st netlist data-size n))
              (append (comp-gcd-body$op-map
                       (comp-gcd-body$in-seq-netlist
                        inputs-seq st netlist data-size n))
                      extracted-st))))
    :hints (("Goal"
             :use comp-gcd-body$dataflow-correct
             :in-theory (enable comp-gcd-body$valid-st=>st-format
                                comp-gcd-body$de-n))))
  )



