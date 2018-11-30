;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; November 2018

(in-package "ADE")

(include-book "../vector-module")
(include-book "../comparators/v-less")
(include-book "../serial-adder/serial-sub")

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
;; constructed using the self-timed serial subtractor SERIAL-SUB.

(defconst *comp-gcd-body$prim-go-num* 2)
(defconst *comp-gcd-body$go-num* (+ *comp-gcd-body$prim-go-num*
                                    *serial-sub$go-num*))
(defconst *comp-gcd-body$st-len* 4)

(defun comp-gcd-body$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun comp-gcd-body$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (comp-gcd-body$data-ins-len data-width)
     *comp-gcd-body$go-num*))

(module-generator
 comp-gcd-body* (data-width)
 (si 'comp-gcd-body data-width)
 (list* 'full-in 'empty-out-
        (append (sis 'data-in 0 (* 2 data-width))
                (sis 'go 0 *comp-gcd-body$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 (* 2 data-width)))
 '(l0 l1 l2 sub)
 (list
  ;; LINKS
  ;; L0
  (list 'l0
        (list* 'l0-status (sis 'd0-out 0 (* 2 data-width)))
        (si 'link (* 2 data-width))
        (list* 'in-act 'sub-in-act (sis 'd0-in 0 (* 2 data-width))))

  ;; L1
  (list 'l1
        (list* 'l1-status (sis 'd1-out 0 data-width))
        (si 'link data-width)
        (list* 'in-act 'out-act (sis 'd1-in 0 data-width)))

  ;; L2
  (list 'l2
        (list* 'l2-status (sis 'd2-out 0 data-width))
        (si 'link data-width)
        (list* 'sub-out-act 'out-act (sis 'd2-in 0 data-width)))

  ;; JOINTS
  ;; In
  '(g0 (ready-in-) b-or (l0-status l1-status))
  (list 'in-cntl
        '(in-act)
        'joint-cntl
        (list 'full-in 'ready-in- (si 'go 0)))
  (list 'in-op0
        '(a<b)
        (si 'v-< data-width)
        (append (rev (sis 'data-in 0 data-width))
                (rev (sis 'data-in data-width data-width))))
  (list 'in-op1
        (sis 'd0-in 0 (* 2 data-width))
        (si 'tv-if (tree-number (make-tree (* 2 data-width))))
        (cons 'a<b
              (append (append (sis 'data-in data-width data-width)
                              (sis 'data-in 0 data-width))
                      (sis 'data-in 0 (* 2 data-width)))))
  (list 'in-op2
        (sis 'd1-in 0 data-width)
        (si 'tv-if (tree-number (make-tree data-width)))
        (cons 'a<b
              (append (sis 'data-in 0 data-width)
                      (sis 'data-in data-width data-width))))

  ;; Subtractor
  (list 'sub
        (list* 'sub-in-act 'sub-out-act
               (sis 'd2-in 0 data-width))
        (si 'serial-sub data-width)
        (list* 'l0-status 'l2-status
               (append (sis 'd0-out 0 data-width)
                       (sis 'd0-out data-width data-width)
                       (sis 'go 2 *serial-sub$go-num*))))

  ;; Out
  '(g1 (ready-out) b-and (l1-status l2-status))
  (list 'out-cntl
        '(out-act)
        'joint-cntl
        (list 'ready-out 'empty-out- (si 'go 1)))
  (list 'out-op
        (sis 'data-out 0 (* 2 data-width))
        (si 'v-wire (* 2 data-width))
        (append (sis 'd1-out 0 data-width)
                (sis 'd2-out 0 data-width))))
 (declare (xargs :guard (natp data-width))))

(make-event
 `(progn
    ,@(state-accessors-gen 'comp-gcd-body '(l0 l1 l2 sub) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; COMP-GCD-BODY.

(defund comp-gcd-body$netlist (data-width cnt-width)
  (declare (xargs :guard (and (posp data-width)
                              (natp cnt-width)
                              (<= 3 cnt-width))))
  (cons (comp-gcd-body* data-width)
        (union$ (link$netlist (* 2 data-width))
                (tv-if$netlist (make-tree (* 2 data-width)))
                (v-wire$netlist (* 2 data-width))
                (v-<$netlist data-width)
                (serial-sub$netlist data-width cnt-width)
                :test 'equal)))

;; Recognizer for COMP-GCD-BODY

(defund comp-gcd-body& (netlist data-width cnt-width)
  (declare (xargs :guard (and (alistp netlist)
                              (posp data-width)
                              (natp cnt-width)
                              (<= 3 cnt-width))))
  (b* ((subnetlist (delete-to-eq (si 'comp-gcd-body data-width) netlist)))
    (and (equal (assoc (si 'comp-gcd-body data-width) netlist)
                (comp-gcd-body* data-width))
         (link& subnetlist data-width)
         (link& subnetlist (* 2 data-width))
         (joint-cntl& subnetlist)
         (tv-if& subnetlist (make-tree data-width))
         (tv-if& subnetlist (make-tree (* 2 data-width)))
         (v-wire& subnetlist (* 2 data-width))
         (v-<& subnetlist data-width)
         (serial-sub& subnetlist data-width cnt-width))))

;; Sanity check

(local
 (defthmd check-comp-gcd-body$netlist-64-7
   (and (net-syntax-okp (comp-gcd-body$netlist 64 7))
        (net-arity-okp (comp-gcd-body$netlist 64 7))
        (comp-gcd-body& (comp-gcd-body$netlist 64 7) 64 7))))

;; Constraints on the state of COMP-GCD-BODY

(defund comp-gcd-body$st-format (st data-width cnt-width)
  (b* ((l0 (get-field *comp-gcd-body$l0* st))
       (l1 (get-field *comp-gcd-body$l1* st))
       (l2 (get-field *comp-gcd-body$l2* st))
       (sub (get-field *comp-gcd-body$sub* st)))
    (and (link$st-format l0 (* 2 data-width))
         (link$st-format l1 data-width)
         (link$st-format l2 data-width)
         (serial-sub$st-format sub data-width cnt-width))))

(defthm comp-gcd-body$st-format=>constraints
  (implies (comp-gcd-body$st-format st data-width cnt-width)
           (and (posp data-width)
                (natp cnt-width)
                (<= 4 cnt-width)))
  :hints (("Goal" :in-theory (enable comp-gcd-body$st-format)))
  :rule-classes :forward-chaining)

(defund comp-gcd-body$valid-st (st data-width cnt-width)
  (b* ((l0 (get-field *comp-gcd-body$l0* st))
       (l1 (get-field *comp-gcd-body$l1* st))
       (l2 (get-field *comp-gcd-body$l2* st))
       (sub (get-field *comp-gcd-body$sub* st)))
    (and (link$valid-st l0 (* 2 data-width))
         (link$valid-st l1 data-width)
         (link$valid-st l2 data-width)
         (serial-sub$valid-st sub data-width cnt-width))))

(defthmd comp-gcd-body$valid-st=>constraints
  (implies (comp-gcd-body$valid-st st data-width cnt-width)
           (and (posp data-width)
                (natp cnt-width)
                (<= 4 cnt-width)))
  :hints (("Goal" :in-theory (enable serial-sub$valid-st=>constraints
                                     comp-gcd-body$valid-st)))
  :rule-classes :forward-chaining)

(defthmd comp-gcd-body$valid-st=>st-format
  (implies (comp-gcd-body$valid-st st data-width cnt-width)
           (comp-gcd-body$st-format st data-width cnt-width))
  :hints (("Goal" :in-theory (e/d (serial-sub$valid-st=>st-format
                                   comp-gcd-body$st-format
                                   comp-gcd-body$valid-st)
                                  ()))))

;; Extract the input and output signals for COMP-GCD-BODY

(progn
  ;; Extract the input data

  (defun comp-gcd-body$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (* 2 (mbe :logic (nfix data-width)
                    :exec  data-width))
          (nthcdr 2 inputs)))

  (defthm len-comp-gcd-body$data-in
    (equal (len (comp-gcd-body$data-in inputs data-width))
           (* 2 (nfix data-width))))

  (in-theory (disable comp-gcd-body$data-in))

  ;; Extract the "a<b" signal

  (defund comp-gcd-body$a<b (inputs data-width)
    (b* ((data-in (comp-gcd-body$data-in inputs data-width)))
      (fv-< nil t
            (rev (take data-width data-in))
            (rev (nthcdr data-width data-in)))))

  ;; Extract the inputs for the SUB joint

  (defund comp-gcd-body$sub-inputs (inputs st data-width)
    (b* ((go-signals (nthcdr (comp-gcd-body$data-ins-len data-width) inputs))
         (sub-go-signals (take *serial-sub$go-num*
                               (nthcdr *comp-gcd-body$prim-go-num*
                                       go-signals)))

         (l0 (get-field *comp-gcd-body$l0* st))
         (l0.s (get-field *link$s* l0))
         (l0.d (get-field *link$d* l0))
         (l2 (get-field *comp-gcd-body$l2* st))
         (l2.s (get-field *link$s* l2)))
      (list* (f-buf (car l0.s)) (f-buf (car l2.s))
             (append (v-threefix (take data-width (strip-cars l0.d)))
                     (v-threefix (nthcdr data-width (strip-cars l0.d)))
                     sub-go-signals))))

  ;; Extract the "in-act" signal

  (defund comp-gcd-body$in-act (inputs st data-width)
    (b* ((full-in (nth 0 inputs))
         (go-signals (nthcdr (comp-gcd-body$data-ins-len data-width) inputs))
         (go-in (nth 0 go-signals))

         (l0 (get-field *comp-gcd-body$l0* st))
         (l0.s (get-field *link$s* l0))
         (l1 (get-field *comp-gcd-body$l1* st))
         (l1.s (get-field *link$s* l1))

         (ready-in- (f-or (car l0.s) (car l1.s))))
      (joint-act full-in ready-in- go-in)))

  (defthm comp-gcd-body$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (comp-gcd-body$in-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable comp-gcd-body$in-act))))

  ;; Extract the "out-act" signal

  (defund comp-gcd-body$out-act (inputs st data-width)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (comp-gcd-body$data-ins-len data-width) inputs))
         (go-out (nth 1 go-signals))

         (l1 (get-field *comp-gcd-body$l1* st))
         (l1.s (get-field *link$s* l1))
         (l2 (get-field *comp-gcd-body$l2* st))
         (l2.s (get-field *link$s* l2))

         (ready-out (f-and (car l1.s) (car l2.s))))
      (joint-act ready-out empty-out- go-out)))

  (defthm comp-gcd-body$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (comp-gcd-body$out-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable comp-gcd-body$out-act))))

  (defthm comp-gcd-body$in-out-acts-mutually-exclusive
    (implies (and (comp-gcd-body$valid-st st data-width cnt-width)
                  (comp-gcd-body$in-act inputs st data-width))
             (not (comp-gcd-body$out-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable comp-gcd-body$valid-st
                                       comp-gcd-body$in-act
                                       comp-gcd-body$out-act))))

  ;; Extract the output data

  (defund comp-gcd-body$data-out (st)
    (b* ((l1 (get-field *comp-gcd-body$l1* st))
         (l1.d (get-field *link$d* l1))
         (l2 (get-field *comp-gcd-body$l2* st))
         (l2.d (get-field *link$d* l2)))
      (append (v-threefix (strip-cars l1.d))
              (v-threefix (strip-cars l2.d)))))

  (defthm len-comp-gcd-body$data-out-1
    (implies (comp-gcd-body$st-format st data-width cnt-width)
             (equal (len (comp-gcd-body$data-out st))
                    (* 2 data-width)))
    :hints (("Goal" :in-theory (enable comp-gcd-body$st-format
                                       comp-gcd-body$data-out))))

  (defthm len-comp-gcd-body$data-out-2
    (implies (comp-gcd-body$valid-st st data-width cnt-width)
             (equal (len (comp-gcd-body$data-out st))
                    (* 2 data-width)))
    :hints (("Goal" :in-theory (enable comp-gcd-body$valid-st
                                       comp-gcd-body$data-out))))

  (defthm bvp-comp-gcd-body$data-out
    (implies (and (comp-gcd-body$valid-st st data-width cnt-width)
                  (comp-gcd-body$out-act inputs st data-width))
             (bvp (comp-gcd-body$data-out st)))
    :hints (("Goal" :in-theory (enable comp-gcd-body$valid-st
                                       comp-gcd-body$out-act
                                       comp-gcd-body$data-out))))

  (defun comp-gcd-body$outputs (inputs st data-width)
    (list* (comp-gcd-body$in-act inputs st data-width)
           (comp-gcd-body$out-act inputs st data-width)
           (comp-gcd-body$data-out st)))
  )

;; The value lemma for COMP-GCD-BODY

(defthm comp-gcd-body$value
  (b* ((inputs (list* full-in empty-out-
                      (append data-in go-signals))))
    (implies (and (comp-gcd-body& netlist data-width cnt-width)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-width))
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-gcd-body$go-num*)
                  (comp-gcd-body$st-format st data-width cnt-width))
             (equal (se (si 'comp-gcd-body data-width) inputs st netlist)
                    (comp-gcd-body$outputs inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'comp-gcd-body data-width)
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

(defun comp-gcd-body$step (inputs st data-width cnt-width)
  (b* ((data-in (comp-gcd-body$data-in inputs data-width))

       (l0 (get-field *comp-gcd-body$l0* st))
       (l1 (get-field *comp-gcd-body$l1* st))
       (l2 (get-field *comp-gcd-body$l2* st))
       (sub (get-field *comp-gcd-body$sub* st))

       (sub-inputs (comp-gcd-body$sub-inputs inputs st data-width))
       (sub-in-act (serial-sub$in-act sub-inputs sub data-width))
       (sub-out-act (serial-sub$out-act sub-inputs sub data-width))
       (in-act (comp-gcd-body$in-act inputs st data-width))
       (out-act (comp-gcd-body$out-act inputs st data-width))

       (a<b (comp-gcd-body$a<b inputs data-width))
       (d0-in (fv-if a<b
                     (append (nthcdr data-width data-in)
                             (take data-width data-in))
                     data-in))
       (d1-in (fv-if a<b
                     (take data-width data-in)
                     (nthcdr data-width data-in)))
       (d2-in (serial-sub$data-out sub))

       (l0-inputs (list* in-act sub-in-act d0-in))
       (l1-inputs (list* in-act out-act d1-in))
       (l2-inputs (list* sub-out-act out-act d2-in)))
    (list
     ;; L0
     (link$step l0-inputs l0 (* 2 data-width))
     ;; L1
     (link$step l1-inputs l1 data-width)
     ;; L2
     (link$step l2-inputs l2 data-width)
     ;; Joint SUB
     (serial-sub$step sub-inputs sub data-width cnt-width))))

(defthm len-of-comp-gcd-body$step
  (equal (len (comp-gcd-body$step inputs st data-width cnt-width))
         *comp-gcd-body$st-len*))

;; The state lemma for COMP-GCD-BODY

(defthm comp-gcd-body$state
  (b* ((inputs (list* full-in empty-out-
                      (append data-in go-signals))))
    (implies (and (comp-gcd-body& netlist data-width cnt-width)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-width))
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-gcd-body$go-num*)
                  (comp-gcd-body$st-format st data-width cnt-width))
             (equal (de (si 'comp-gcd-body data-width) inputs st netlist)
                    (comp-gcd-body$step inputs st data-width cnt-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'comp-gcd-body data-width)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            comp-gcd-body&
                            comp-gcd-body*$destructure
                            comp-gcd-body$st-format
                            comp-gcd-body$data-in
                            comp-gcd-body$a<b
                            comp-gcd-body$sub-inputs
                            comp-gcd-body$in-act
                            comp-gcd-body$out-act)
                           (associativity-of-append
                            append-take-nthcdr
                            de-module-disabled-rules)))))

(in-theory (disable comp-gcd-body$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund comp-gcd-body$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (comp-gcd-body$data-in inputs data-width))
       (go-signals (nthcdr (comp-gcd-body$data-ins-len data-width) inputs)))
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

(local
 (defthm comp-gcd-body$input-format=>sub$input-format
   (implies (and (comp-gcd-body$input-format inputs data-width)
                 (comp-gcd-body$valid-st st data-width cnt-width))
            (serial-sub$input-format
             (comp-gcd-body$sub-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (serial-sub$input-format
                             serial-sub$data0-in
                             serial-sub$data1-in
                             comp-gcd-body$input-format
                             comp-gcd-body$valid-st
                             comp-gcd-body$sub-inputs)
                            ())))))

(defthm booleanp-comp-gcd-body$in-act
  (implies (and (comp-gcd-body$input-format inputs data-width)
                (comp-gcd-body$valid-st st data-width cnt-width))
           (booleanp (comp-gcd-body$in-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (e/d (comp-gcd-body$input-format
                            comp-gcd-body$valid-st
                            comp-gcd-body$in-act)
                           ())))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-gcd-body$out-act
  (implies (and (comp-gcd-body$input-format inputs data-width)
                (comp-gcd-body$valid-st st data-width cnt-width))
           (booleanp (comp-gcd-body$out-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (e/d (comp-gcd-body$input-format
                            comp-gcd-body$valid-st
                            comp-gcd-body$out-act)
                           ())))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma comp-gcd-body :sizes (data-width cnt-width))

;; ======================================================================

;; 3. Single-Step-Update Property

;; Specify the functionality of COMP-GCD-BODY

(defund comp-gcd-body$op (x)
  (b* ((data-width (/ (len x) 2))
       (a (take data-width x))
       (b (nthcdr data-width x))
       (a<b (v-< nil t (rev a) (rev b))))
    (cond
     ((or (atom x)
          (zp data-width)
          (not (bvp x)))
      x)
     (t (v-if a<b
              (append a (serial-sub$op t b a))
              (append b (serial-sub$op t a b)))))))

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

;; The extraction function for COMP-GCD-BODY that extracts the future
;; output sequence from the current state.

(defund comp-gcd-body$extract (st data-width)
  (b* ((l0 (get-field *comp-gcd-body$l0* st))
       (l0.s (get-field *link$s* l0))
       (l0.d (get-field *link$d* l0))
       (l1 (get-field *comp-gcd-body$l1* st))
       (l2 (get-field *comp-gcd-body$l2* st))
       (sub (get-field *comp-gcd-body$sub* st)))
    (if (zp (len (extract-valid-data (list l1))))
        nil
      (list (append
             (car (extract-valid-data (list l1)))
             (car (append
                   (if (fullp l0.s)
                       (list
                        (serial-sub$op
                         t
                         (take data-width (strip-cars l0.d))
                         (nthcdr data-width (strip-cars l0.d))))
                     nil)
                   (serial-sub$extract sub data-width)
                   (extract-valid-data (list l2)))))))))

(defthm comp-gcd-body$extract-not-empty
  (implies (and (comp-gcd-body$out-act inputs st data-width)
                (comp-gcd-body$valid-st st data-width cnt-width))
           (< 0 (len (comp-gcd-body$extract st data-width))))
  :hints (("Goal"
           :in-theory (e/d (comp-gcd-body$valid-st
                            comp-gcd-body$extract
                            comp-gcd-body$out-act)
                           ())))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund comp-gcd-body$inv (st data-width)
    (b* ((l0 (get-field *comp-gcd-body$l0* st))
         (l1 (get-field *comp-gcd-body$l1* st))
         (l2 (get-field *comp-gcd-body$l2* st))
         (sub (get-field *comp-gcd-body$sub* st))

         (len1 (len (extract-valid-data (list l1))))
         (len2 (len (append
                     (serial-sub$op-map (extract-valid-data (list l0)))
                     (serial-sub$extract sub data-width)
                     (extract-valid-data (list l2))))))
      (and (equal len1 len2)
           (serial-sub$inv sub data-width))))

  (local
   (defthm comp-gcd-body$sub-in-act-inactive
     (b* ((l0 (nth *comp-gcd-body$l0* st))
          (l0.s (nth *link$s* l0))
          (sub (nth *comp-gcd-body$sub* st))
          (sub-inputs (comp-gcd-body$sub-inputs inputs st data-width)))
       (implies (emptyp l0.s)
                (not (serial-sub$in-act sub-inputs
                                        sub
                                        data-width))))
     :hints (("Goal" :in-theory (enable get-field
                                        comp-gcd-body$sub-inputs)))))

  (defthm comp-gcd-body$inv-preserved
    (implies (and (comp-gcd-body$input-format inputs data-width)
                  (comp-gcd-body$valid-st st data-width cnt-width)
                  (comp-gcd-body$inv st data-width))
             (comp-gcd-body$inv
              (comp-gcd-body$step inputs st data-width cnt-width)
              data-width))
    :hints (("Goal"
             :use comp-gcd-body$input-format=>sub$input-format
             :in-theory (e/d (get-field
                              f-sr
                              serial-sub$extracted-step
                              comp-gcd-body$valid-st
                              comp-gcd-body$inv
                              comp-gcd-body$step
                              comp-gcd-body$in-act
                              comp-gcd-body$out-act)
                             (comp-gcd-body$input-format=>sub$input-format)))))
  )

;; The extracted next-state function for COMP-GCD-BODY.  Note that this
;; function avoids exploring the internal computation of COMP-GCD-BODY.

(defund comp-gcd-body$extracted-step (inputs st data-width)
  (b* ((data (comp-gcd-body$op (comp-gcd-body$data-in inputs data-width)))
       (extracted-st (comp-gcd-body$extract st data-width))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-gcd-body$out-act inputs st data-width) t)
      (take n extracted-st))
     ((equal (comp-gcd-body$in-act inputs st data-width) t)
      (cons data extracted-st))
     (t extracted-st))))

(local
 (defthm comp-gcd-body$input-format-lemma-1
   (implies (comp-gcd-body$input-format inputs data-width)
            (booleanp (nth 0 inputs)))
   :hints (("Goal" :in-theory (enable comp-gcd-body$input-format)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm comp-gcd-body$input-format-lemma-2
   (implies (comp-gcd-body$input-format inputs data-width)
            (booleanp (nth 1 inputs)))
   :hints (("Goal" :in-theory (enable comp-gcd-body$input-format)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm comp-gcd-body$input-format-lemma-3
   (implies (and (comp-gcd-body$input-format inputs data-width)
                 (nth 0 inputs))
            (bvp (comp-gcd-body$data-in inputs data-width)))
   :hints (("Goal" :in-theory (enable comp-gcd-body$input-format)))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm comp-gcd-body$extracted-step-correct-aux-1
     (b* ((sub-inputs (comp-gcd-body$sub-inputs inputs st data-width))
          (l0 (nth *comp-gcd-body$l0* st))
          (l0.d (nth *link$d* l0)))
       (equal (serial-sub$data0-in sub-inputs data-width)
              (v-threefix (take data-width (strip-cars l0.d)))))
     :hints (("Goal" :in-theory (enable get-field
                                        serial-sub$data0-in
                                        comp-gcd-body$sub-inputs)))))

  (local
   (defthm comp-gcd-body$extracted-step-correct-aux-2
     (b* ((sub-inputs (comp-gcd-body$sub-inputs inputs st data-width))
          (l0 (nth *comp-gcd-body$l0* st))
          (l0.d (nth *link$d* l0)))
       (implies (and (equal (len l0.d) (* 2 data-width))
                     (integerp data-width))
                (equal (serial-sub$data1-in sub-inputs data-width)
                       (v-threefix (nthcdr data-width (strip-cars l0.d))))))
     :hints (("Goal" :in-theory (enable get-field
                                        serial-sub$data1-in
                                        comp-gcd-body$sub-inputs)))))

  (defthm comp-gcd-body$extracted-step-correct
    (b* ((next-st (comp-gcd-body$step inputs st data-width cnt-width)))
      (implies (and (comp-gcd-body$input-format inputs data-width)
                    (comp-gcd-body$valid-st st data-width cnt-width)
                    (comp-gcd-body$inv st data-width))
               (equal (comp-gcd-body$extract next-st data-width)
                      (comp-gcd-body$extracted-step inputs st data-width))))
    :hints (("Goal"
             :use comp-gcd-body$input-format=>sub$input-format
             :in-theory (e/d (get-field
                              joint-act
                              pos-len=>cons
                              fv-if-rewrite
                              serial-sub$valid-st=>constraints
                              serial-sub$extracted-step
                              comp-gcd-body$extracted-step
                              comp-gcd-body$valid-st
                              comp-gcd-body$inv
                              comp-gcd-body$step
                              comp-gcd-body$a<b
                              comp-gcd-body$in-act
                              comp-gcd-body$out-act
                              comp-gcd-body$extract
                              comp-gcd-body$op)
                             (comp-gcd-body$input-format=>sub$input-format)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that comp-gcd-body$valid-st is an invariant.

(encapsulate
  ()

  (local
   (defthm comp-gcd-body$sub-out-act-inactive
     (b* ((l2 (nth *comp-gcd-body$l2* st))
          (l2.s (nth *link$s* l2))
          (sub (nth *comp-gcd-body$sub* st))
          (sub-inputs (comp-gcd-body$sub-inputs inputs st data-width)))
       (implies (fullp l2.s)
                (not (serial-sub$out-act sub-inputs
                                                sub
                                                data-width))))
     :hints (("Goal" :in-theory (enable get-field
                                        comp-gcd-body$sub-inputs)))))

  (defthm comp-gcd-body$valid-st-preserved
    (implies (and (comp-gcd-body$input-format inputs data-width)
                  (comp-gcd-body$valid-st st data-width cnt-width))
             (comp-gcd-body$valid-st
              (comp-gcd-body$step inputs st data-width cnt-width)
              data-width
              cnt-width))
    :hints (("Goal"
             :use comp-gcd-body$input-format=>sub$input-format
             :in-theory (e/d (get-field
                              f-sr
                              joint-act
                              serial-sub$valid-st=>constraints
                              comp-gcd-body$valid-st
                              comp-gcd-body$step
                              comp-gcd-body$a<b
                              comp-gcd-body$in-act
                              comp-gcd-body$out-act)
                             (comp-gcd-body$input-format=>sub$input-format
                              if*)))))
  )

(defthm comp-gcd-body$extract-lemma
  (implies (and (comp-gcd-body$valid-st st data-width cnt-width)
                (comp-gcd-body$inv st data-width)
                (comp-gcd-body$out-act inputs st data-width))
           (equal (list (comp-gcd-body$data-out st))
                  (nthcdr (1- (len (comp-gcd-body$extract st data-width)))
                          (comp-gcd-body$extract st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (len-0-is-atom
                            comp-gcd-body$valid-st
                            comp-gcd-body$inv
                            comp-gcd-body$extract
                            comp-gcd-body$out-act
                            comp-gcd-body$data-out)
                           ()))))

;; Extract the accepted input sequence

(seq-gen comp-gcd-body in in-act 0
         (comp-gcd-body$data-in inputs data-width)
         :sizes (data-width cnt-width))

;; Extract the valid output sequence

(seq-gen comp-gcd-body out out-act 1
         (comp-gcd-body$data-out st)
         :netlist-data (nthcdr 2 outputs)
         :sizes (data-width cnt-width))

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
    (b* ((extracted-st (comp-gcd-body$extract st data-width))
         (final-st (comp-gcd-body$run
                    inputs-seq st data-width cnt-width n))
         (final-extracted-st (comp-gcd-body$extract final-st data-width)))
      (implies
       (and (comp-gcd-body$input-format-n inputs-seq data-width n)
            (comp-gcd-body$valid-st st data-width cnt-width)
            (comp-gcd-body$inv st data-width))
       (equal (append final-extracted-st
                      (comp-gcd-body$out-seq
                       inputs-seq st data-width cnt-width n))
              (append (comp-gcd-body$op-map
                       (comp-gcd-body$in-seq
                        inputs-seq st data-width cnt-width n))
                      extracted-st))))
    :hints (("Goal"
             :in-theory (enable comp-gcd-body$extracted-step))))

  (defthmd comp-gcd-body$functionally-correct
    (b* ((extracted-st (comp-gcd-body$extract st data-width))
         (final-st (de-n (si 'comp-gcd-body data-width)
                         inputs-seq st netlist n))
         (final-extracted-st (comp-gcd-body$extract final-st data-width)))
      (implies
       (and (comp-gcd-body& netlist data-width cnt-width)
            (comp-gcd-body$input-format-n inputs-seq data-width n)
            (comp-gcd-body$valid-st st data-width cnt-width)
            (comp-gcd-body$inv st data-width))
       (equal (append final-extracted-st
                      (comp-gcd-body$netlist-out-seq
                       inputs-seq st netlist data-width n))
              (append (comp-gcd-body$op-map
                       (comp-gcd-body$netlist-in-seq
                        inputs-seq st netlist data-width n))
                      extracted-st))))
    :hints (("Goal"
             :use comp-gcd-body$dataflow-correct
             :in-theory (enable comp-gcd-body$valid-st=>st-format
                                comp-gcd-body$de-n))))
  )



