;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; February 2019

(in-package "ADE")

(include-book "../vector-module")
(include-book "../comparators/v-less")
(include-book "../serial-adder/serial-sub")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of COMP-GCD-BODY2
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of COMP-GCD-BODY2
;;
;; COMP-GCD-BODY2 performs the GCD operation in one iteration.  It is
;; constructed using the self-timed serial subtractor SERIAL-SUB.

(defconst *comp-gcd-body2$prim-go-num* 2)
(defconst *comp-gcd-body2$go-num* (+ *comp-gcd-body2$prim-go-num*
                                     *serial-sub$go-num*))
(defconst *comp-gcd-body2$st-len* 4)

(defun comp-gcd-body2$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (* 2 (mbe :logic (nfix data-size)
                 :exec  data-size))))

(defun comp-gcd-body2$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (comp-gcd-body2$data-ins-len data-size)
     *comp-gcd-body2$go-num*))

(module-generator
 comp-gcd-body2* (data-size)
 (si 'comp-gcd-body2 data-size)
 (list* 'full-in 'empty-out-
        (append (sis 'data-in 0 (* 2 data-size))
                (sis 'go 0 *comp-gcd-body2$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 (* 2 data-size)))
 '(l0 l1 l2 sub)
 (list
  ;; LINKS
  ;; L0
  (list 'l0
        (list* 'l0-status (sis 'd0-out 0 (* 2 data-size)))
        (si 'link (* 2 data-size))
        (list* 'in-act 'sub-in-act (sis 'd0-in 0 (* 2 data-size))))

  ;; L1
  (list 'l1
        (list* 'l1-status (sis 'd1-out 0 data-size))
        (si 'link data-size)
        (list* 'in-act 'out-act (sis 'd1-in 0 data-size)))

  ;; L2
  (list 'l2
        (list* 'l2-status (sis 'd2-out 0 data-size))
        (si 'link data-size)
        (list* 'sub-out-act 'out-act (sis 'd2-in 0 data-size)))

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

  ;; Subtractor
  (list 'sub
        (list* 'sub-in-act 'sub-out-act
               (sis 'd2-in 0 data-size))
        (si 'serial-sub data-size)
        (list* 'l0-status 'l2-status
               (append (sis 'd0-out 0 data-size)
                       (sis 'd0-out data-size data-size)
                       (sis 'go 2 *serial-sub$go-num*))))

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
    ,@(state-accessors-gen 'comp-gcd-body2 '(l0 l1 l2 sub) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; COMP-GCD-BODY2.

(defund comp-gcd-body2$netlist (data-size cnt-size)
  (declare (xargs :guard (and (posp data-size)
                              (natp cnt-size)
                              (<= 3 cnt-size))))
  (cons (comp-gcd-body2* data-size)
        (union$ (link$netlist (* 2 data-size))
                (tv-if$netlist (make-tree (* 2 data-size)))
                (v-wire$netlist (* 2 data-size))
                (v-<$netlist data-size)
                (serial-sub$netlist data-size cnt-size)
                :test 'equal)))

;; Recognizer for COMP-GCD-BODY2

(defund comp-gcd-body2& (netlist data-size cnt-size)
  (declare (xargs :guard (and (alistp netlist)
                              (posp data-size)
                              (natp cnt-size)
                              (<= 3 cnt-size))))
  (b* ((subnetlist (delete-to-eq (si 'comp-gcd-body2 data-size) netlist)))
    (and (equal (assoc (si 'comp-gcd-body2 data-size) netlist)
                (comp-gcd-body2* data-size))
         (link& subnetlist data-size)
         (link& subnetlist (* 2 data-size))
         (joint-cntl& subnetlist)
         (tv-if& subnetlist (make-tree data-size))
         (tv-if& subnetlist (make-tree (* 2 data-size)))
         (v-wire& subnetlist (* 2 data-size))
         (v-<& subnetlist data-size)
         (serial-sub& subnetlist data-size cnt-size))))

;; Sanity check

(local
 (defthmd check-comp-gcd-body2$netlist-64-7
   (and (net-syntax-okp (comp-gcd-body2$netlist 64 7))
        (net-arity-okp (comp-gcd-body2$netlist 64 7))
        (comp-gcd-body2& (comp-gcd-body2$netlist 64 7) 64 7))))

;; Constraints on the state of COMP-GCD-BODY2

(defund comp-gcd-body2$st-format (st data-size cnt-size)
  (b* ((l0 (get-field *comp-gcd-body2$l0* st))
       (l1 (get-field *comp-gcd-body2$l1* st))
       (l2 (get-field *comp-gcd-body2$l2* st))
       (sub (get-field *comp-gcd-body2$sub* st)))
    (and (link$st-format l0 (* 2 data-size))
         (link$st-format l1 data-size)
         (link$st-format l2 data-size)
         (serial-sub$st-format sub data-size cnt-size))))

(defthm comp-gcd-body2$st-format=>constraint
  (implies (comp-gcd-body2$st-format st data-size cnt-size)
           (and (posp data-size)
                (natp cnt-size)
                (<= 4 cnt-size)))
  :hints (("Goal" :in-theory (enable comp-gcd-body2$st-format)))
  :rule-classes :forward-chaining)

(defund comp-gcd-body2$valid-st (st data-size cnt-size)
  (b* ((l0 (get-field *comp-gcd-body2$l0* st))
       (l1 (get-field *comp-gcd-body2$l1* st))
       (l2 (get-field *comp-gcd-body2$l2* st))
       (sub (get-field *comp-gcd-body2$sub* st)))
    (and (link$valid-st l0 (* 2 data-size))
         (link$valid-st l1 data-size)
         (link$valid-st l2 data-size)
         (serial-sub$valid-st sub data-size cnt-size))))

(defthmd comp-gcd-body2$valid-st=>constraint
  (implies (comp-gcd-body2$valid-st st data-size cnt-size)
           (and (posp data-size)
                (natp cnt-size)
                (<= 4 cnt-size)))
  :hints (("Goal" :in-theory (enable serial-sub$valid-st=>constraint
                                     comp-gcd-body2$valid-st)))
  :rule-classes :forward-chaining)

(defthmd comp-gcd-body2$valid-st=>st-format
  (implies (comp-gcd-body2$valid-st st data-size cnt-size)
           (comp-gcd-body2$st-format st data-size cnt-size))
  :hints (("Goal" :in-theory (e/d (serial-sub$valid-st=>st-format
                                   comp-gcd-body2$st-format
                                   comp-gcd-body2$valid-st)
                                  ()))))

;; Extract the input and output signals for COMP-GCD-BODY2

(progn
  ;; Extract the input data

  (defun comp-gcd-body2$data-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (* 2 (mbe :logic (nfix data-size)
                    :exec  data-size))
          (nthcdr 2 inputs)))

  (defthm len-comp-gcd-body2$data-in
    (equal (len (comp-gcd-body2$data-in inputs data-size))
           (* 2 (nfix data-size))))

  (in-theory (disable comp-gcd-body2$data-in))

  ;; Extract the "a<b" signal

  (defund comp-gcd-body2$a<b (inputs data-size)
    (b* ((data-in (comp-gcd-body2$data-in inputs data-size)))
      (fv-< nil t
            (rev (take data-size data-in))
            (rev (nthcdr data-size data-in)))))

  ;; Extract the inputs for the SUB joint

  (defund comp-gcd-body2$sub-inputs (inputs st data-size)
    (b* ((go-signals (nthcdr (comp-gcd-body2$data-ins-len data-size) inputs))
         (sub-go-signals (take *serial-sub$go-num*
                               (nthcdr *comp-gcd-body2$prim-go-num*
                                       go-signals)))

         (l0 (get-field *comp-gcd-body2$l0* st))
         (l0.s (get-field *link$s* l0))
         (l0.d (get-field *link$d* l0))
         (l2 (get-field *comp-gcd-body2$l2* st))
         (l2.s (get-field *link$s* l2)))
      (list* (f-buf (car l0.s)) (f-buf (car l2.s))
             (append (v-threefix (take data-size (strip-cars l0.d)))
                     (v-threefix (nthcdr data-size (strip-cars l0.d)))
                     sub-go-signals))))

  ;; Extract the "in-act" signal

  (defund comp-gcd-body2$in-act (inputs st data-size)
    (b* ((full-in (nth 0 inputs))
         (go-signals (nthcdr (comp-gcd-body2$data-ins-len data-size) inputs))
         (go-in (nth 0 go-signals))

         (l0 (get-field *comp-gcd-body2$l0* st))
         (l0.s (get-field *link$s* l0))
         (l1 (get-field *comp-gcd-body2$l1* st))
         (l1.s (get-field *link$s* l1))

         (ready-in- (f-or (car l0.s) (car l1.s))))
      (joint-act full-in ready-in- go-in)))

  (defthm comp-gcd-body2$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (comp-gcd-body2$in-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-gcd-body2$in-act))))

  ;; Extract the "out-act" signal

  (defund comp-gcd-body2$out-act (inputs st data-size)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (comp-gcd-body2$data-ins-len data-size) inputs))
         (go-out (nth 1 go-signals))

         (l1 (get-field *comp-gcd-body2$l1* st))
         (l1.s (get-field *link$s* l1))
         (l2 (get-field *comp-gcd-body2$l2* st))
         (l2.s (get-field *link$s* l2))

         (ready-out (f-and (car l1.s) (car l2.s))))
      (joint-act ready-out empty-out- go-out)))

  (defthm comp-gcd-body2$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (comp-gcd-body2$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-gcd-body2$out-act))))

  (defthm comp-gcd-body2$in-out-acts-mutually-exclusive
    (implies (and (comp-gcd-body2$valid-st st data-size cnt-size)
                  (comp-gcd-body2$in-act inputs st data-size))
             (not (comp-gcd-body2$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable comp-gcd-body2$valid-st
                                       comp-gcd-body2$in-act
                                       comp-gcd-body2$out-act))))

  ;; Extract the output data

  (defund comp-gcd-body2$data-out (st)
    (b* ((l1 (get-field *comp-gcd-body2$l1* st))
         (l1.d (get-field *link$d* l1))
         (l2 (get-field *comp-gcd-body2$l2* st))
         (l2.d (get-field *link$d* l2)))
      (append (v-threefix (strip-cars l2.d))
              (v-threefix (strip-cars l1.d)))))

  (defthm len-comp-gcd-body2$data-out-1
    (implies (comp-gcd-body2$st-format st data-size cnt-size)
             (equal (len (comp-gcd-body2$data-out st))
                    (* 2 data-size)))
    :hints (("Goal" :in-theory (enable comp-gcd-body2$st-format
                                       comp-gcd-body2$data-out))))

  (defthm len-comp-gcd-body2$data-out-2
    (implies (comp-gcd-body2$valid-st st data-size cnt-size)
             (equal (len (comp-gcd-body2$data-out st))
                    (* 2 data-size)))
    :hints (("Goal" :in-theory (enable comp-gcd-body2$valid-st
                                       comp-gcd-body2$data-out))))

  (defthm bvp-comp-gcd-body2$data-out
    (implies (and (comp-gcd-body2$valid-st st data-size cnt-size)
                  (comp-gcd-body2$out-act inputs st data-size))
             (bvp (comp-gcd-body2$data-out st)))
    :hints (("Goal" :in-theory (enable comp-gcd-body2$valid-st
                                       comp-gcd-body2$out-act
                                       comp-gcd-body2$data-out))))

  (defun comp-gcd-body2$outputs (inputs st data-size)
    (list* (comp-gcd-body2$in-act inputs st data-size)
           (comp-gcd-body2$out-act inputs st data-size)
           (comp-gcd-body2$data-out st)))
  )

;; The value lemma for COMP-GCD-BODY2

(defthm comp-gcd-body2$value
  (b* ((inputs (list* full-in empty-out-
                      (append data-in go-signals))))
    (implies (and (comp-gcd-body2& netlist data-size cnt-size)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-size))
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-gcd-body2$go-num*)
                  (comp-gcd-body2$st-format st data-size cnt-size))
             (equal (se (si 'comp-gcd-body2 data-size) inputs st netlist)
                    (comp-gcd-body2$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'comp-gcd-body2 data-size)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            comp-gcd-body2&
                            comp-gcd-body2*$destructure
                            comp-gcd-body2$st-format
                            comp-gcd-body2$in-act
                            comp-gcd-body2$out-act
                            comp-gcd-body2$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of COMP-GCD-BODY2.

(defun comp-gcd-body2$step (inputs st data-size cnt-size)
  (b* ((data-in (comp-gcd-body2$data-in inputs data-size))

       (l0 (get-field *comp-gcd-body2$l0* st))
       (l1 (get-field *comp-gcd-body2$l1* st))
       (l2 (get-field *comp-gcd-body2$l2* st))
       (sub (get-field *comp-gcd-body2$sub* st))

       (in-act (comp-gcd-body2$in-act inputs st data-size))
       (out-act (comp-gcd-body2$out-act inputs st data-size))
       (sub-inputs (comp-gcd-body2$sub-inputs inputs st data-size))
       (sub-in-act (serial-sub$in-act sub-inputs sub data-size))
       (sub-out-act (serial-sub$out-act sub-inputs sub data-size))

       (a<b (comp-gcd-body2$a<b inputs data-size))
       (d0-in (fv-if a<b
                     (append (nthcdr data-size data-in)
                             (take data-size data-in))
                     data-in))
       (d1-in (fv-if a<b
                     (take data-size data-in)
                     (nthcdr data-size data-in)))
       (d2-in (serial-sub$data-out sub))

       (l0-inputs (list* in-act sub-in-act d0-in))
       (l1-inputs (list* in-act out-act d1-in))
       (l2-inputs (list* sub-out-act out-act d2-in)))
    (list
     ;; L0
     (link$step l0-inputs l0 (* 2 data-size))
     ;; L1
     (link$step l1-inputs l1 data-size)
     ;; L2
     (link$step l2-inputs l2 data-size)
     ;; Joint SUB
     (serial-sub$step sub-inputs sub data-size cnt-size))))

(defthm len-of-comp-gcd-body2$step
  (equal (len (comp-gcd-body2$step inputs st data-size cnt-size))
         *comp-gcd-body2$st-len*))

;; The state lemma for COMP-GCD-BODY2

(defthm comp-gcd-body2$state
  (b* ((inputs (list* full-in empty-out-
                      (append data-in go-signals))))
    (implies (and (comp-gcd-body2& netlist data-size cnt-size)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-size))
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-gcd-body2$go-num*)
                  (comp-gcd-body2$st-format st data-size cnt-size))
             (equal (de (si 'comp-gcd-body2 data-size) inputs st netlist)
                    (comp-gcd-body2$step inputs st data-size cnt-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'comp-gcd-body2 data-size)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            comp-gcd-body2&
                            comp-gcd-body2*$destructure
                            comp-gcd-body2$st-format
                            comp-gcd-body2$data-in
                            comp-gcd-body2$a<b
                            comp-gcd-body2$sub-inputs
                            comp-gcd-body2$in-act
                            comp-gcd-body2$out-act)
                           (associativity-of-append
                            append-take-nthcdr
                            de-module-disabled-rules)))))

(in-theory (disable comp-gcd-body2$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund comp-gcd-body2$input-format (inputs data-size)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-size))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (comp-gcd-body2$data-in inputs data-size))
       (go-signals (nthcdr (comp-gcd-body2$data-ins-len data-size) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in)
         (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *comp-gcd-body2$go-num*)
     (equal inputs
            (list* full-in empty-out-
                   (append data-in go-signals))))))

(local
 (defthm comp-gcd-body2$input-format=>sub$input-format
   (implies (and (comp-gcd-body2$input-format inputs data-size)
                 (comp-gcd-body2$valid-st st data-size cnt-size))
            (serial-sub$input-format
             (comp-gcd-body2$sub-inputs inputs st data-size)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (serial-sub$input-format
                             serial-sub$data0-in
                             serial-sub$data1-in
                             comp-gcd-body2$input-format
                             comp-gcd-body2$valid-st
                             comp-gcd-body2$sub-inputs)
                            ())))))

(defthm booleanp-comp-gcd-body2$in-act
  (implies (and (comp-gcd-body2$input-format inputs data-size)
                (comp-gcd-body2$valid-st st data-size cnt-size))
           (booleanp (comp-gcd-body2$in-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (e/d (comp-gcd-body2$input-format
                            comp-gcd-body2$valid-st
                            comp-gcd-body2$in-act)
                           ())))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-gcd-body2$out-act
  (implies (and (comp-gcd-body2$input-format inputs data-size)
                (comp-gcd-body2$valid-st st data-size cnt-size))
           (booleanp (comp-gcd-body2$out-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (e/d (comp-gcd-body2$input-format
                            comp-gcd-body2$valid-st
                            comp-gcd-body2$out-act)
                           ())))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma comp-gcd-body2 :sizes (data-size cnt-size))

;; ======================================================================

;; 3. Single-Step-Update Property

;; Specify the functionality of COMP-GCD-BODY2

(defund comp-gcd-body2$op (x)
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
              (append (serial-sub$op t b a) a)
              (append (serial-sub$op t a b) b))))))

;; The operation of COMP-GCD-BODY2 over a data sequence

(defun comp-gcd-body2$op-map (x)
  (if (atom x)
      nil
    (cons (comp-gcd-body2$op (car x))
          (comp-gcd-body2$op-map (cdr x)))))

(defthm comp-gcd-body2$op-map-of-append
  (equal (comp-gcd-body2$op-map (append x y))
         (append (comp-gcd-body2$op-map x)
                 (comp-gcd-body2$op-map y))))

;; The extraction function for COMP-GCD-BODY2 that extracts the future output
;; sequence from the current state.

(defund comp-gcd-body2$extract (st data-size)
  (b* ((l0 (get-field *comp-gcd-body2$l0* st))
       (l0.s (get-field *link$s* l0))
       (l0.d (get-field *link$d* l0))
       (l1 (get-field *comp-gcd-body2$l1* st))
       (l1.s (get-field *link$s* l1))
       (l1.d (get-field *link$d* l1))
       (l2 (get-field *comp-gcd-body2$l2* st))
       (l2.s (get-field *link$s* l2))
       (l2.d (get-field *link$d* l2))
       (sub (get-field *comp-gcd-body2$sub* st)))
    (if (emptyp l1.s)
        nil
      (list
       (append
        (cond ((fullp l0.s)
               (serial-sub$op t
                              (take data-size (strip-cars l0.d))
                              (nthcdr data-size (strip-cars l0.d))))
              ((fullp l2.s)
               (strip-cars l2.d))
              (t (car (serial-sub$extract sub data-size))))
        (strip-cars l1.d))))))

(defthm comp-gcd-body2$extract-not-empty
  (implies (and (comp-gcd-body2$out-act inputs st data-size)
                (comp-gcd-body2$valid-st st data-size cnt-size))
           (< 0 (len (comp-gcd-body2$extract st data-size))))
  :hints (("Goal"
           :in-theory (e/d (comp-gcd-body2$valid-st
                            comp-gcd-body2$extract
                            comp-gcd-body2$out-act)
                           ())))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund comp-gcd-body2$inv (st data-size)
    (b* ((l0 (get-field *comp-gcd-body2$l0* st))
         (l1 (get-field *comp-gcd-body2$l1* st))
         (l2 (get-field *comp-gcd-body2$l2* st))
         (sub (get-field *comp-gcd-body2$sub* st))

         (len1 (len (append
                     (extract-valid-data (list l0 l2))
                     (serial-sub$extract sub data-size))))
         (len2 (len (extract-valid-data (list l1)))))
      (and (equal len1 len2)
           (serial-sub$inv sub data-size))))

  (local
   (defthm comp-gcd-body2$sub-in-act-inactive
     (b* ((l0 (nth *comp-gcd-body2$l0* st))
          (l0.s (nth *link$s* l0))
          (sub (nth *comp-gcd-body2$sub* st))
          (sub-inputs (comp-gcd-body2$sub-inputs inputs st data-size)))
       (implies (emptyp l0.s)
                (not (serial-sub$in-act sub-inputs
                                        sub
                                        data-size))))
     :hints (("Goal" :in-theory (enable get-field
                                        comp-gcd-body2$sub-inputs)))))

  (defthm comp-gcd-body2$inv-preserved
    (implies (and (comp-gcd-body2$input-format inputs data-size)
                  (comp-gcd-body2$valid-st st data-size cnt-size)
                  (comp-gcd-body2$inv st data-size))
             (comp-gcd-body2$inv
              (comp-gcd-body2$step inputs st data-size cnt-size)
              data-size))
    :hints (("Goal"
             :use comp-gcd-body2$input-format=>sub$input-format
             :in-theory (e/d (get-field
                              f-sr
                              serial-sub$extracted-step
                              comp-gcd-body2$valid-st
                              comp-gcd-body2$inv
                              comp-gcd-body2$step
                              comp-gcd-body2$in-act
                              comp-gcd-body2$out-act)
                             (comp-gcd-body2$input-format=>sub$input-format)))))
  )

;; The extracted next-state function for COMP-GCD-BODY2.  Note that this
;; function avoids exploring the internal computation of COMP-GCD-BODY2.

(defund comp-gcd-body2$extracted-step (inputs st data-size)
  (b* ((data (comp-gcd-body2$op (comp-gcd-body2$data-in inputs data-size)))
       (extracted-st (comp-gcd-body2$extract st data-size))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-gcd-body2$out-act inputs st data-size) t)
      (take n extracted-st))
     ((equal (comp-gcd-body2$in-act inputs st data-size) t)
      (cons data extracted-st))
     (t extracted-st))))

(local
 (defthm comp-gcd-body2$input-format-lemma-1
   (implies (comp-gcd-body2$input-format inputs data-size)
            (booleanp (nth 0 inputs)))
   :hints (("Goal" :in-theory (enable comp-gcd-body2$input-format)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm comp-gcd-body2$input-format-lemma-2
   (implies (comp-gcd-body2$input-format inputs data-size)
            (booleanp (nth 1 inputs)))
   :hints (("Goal" :in-theory (enable comp-gcd-body2$input-format)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm comp-gcd-body2$input-format-lemma-3
   (implies (and (comp-gcd-body2$input-format inputs data-size)
                 (nth 0 inputs))
            (bvp (comp-gcd-body2$data-in inputs data-size)))
   :hints (("Goal" :in-theory (enable comp-gcd-body2$input-format)))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm comp-gcd-body2$extracted-step-correct-aux-1
     (b* ((sub-inputs (comp-gcd-body2$sub-inputs inputs st data-size))
          (l0 (nth *comp-gcd-body2$l0* st))
          (l0.d (nth *link$d* l0)))
       (equal (serial-sub$data0-in sub-inputs data-size)
              (v-threefix (take data-size (strip-cars l0.d)))))
     :hints (("Goal" :in-theory (enable get-field
                                        serial-sub$data0-in
                                        comp-gcd-body2$sub-inputs)))))

  (local
   (defthm comp-gcd-body2$extracted-step-correct-aux-2
     (b* ((sub-inputs (comp-gcd-body2$sub-inputs inputs st data-size))
          (l0 (nth *comp-gcd-body2$l0* st))
          (l0.d (nth *link$d* l0)))
       (implies (and (equal (len l0.d) (* 2 data-size))
                     (integerp data-size))
                (equal (serial-sub$data1-in sub-inputs data-size)
                       (v-threefix (nthcdr data-size (strip-cars l0.d))))))
     :hints (("Goal" :in-theory (enable get-field
                                        serial-sub$data1-in
                                        comp-gcd-body2$sub-inputs)))))

  (local
   (defthm car-of-serial-sub$extract-lemma
     (implies (and (equal (len (serial-sub$extract st data-size))
                          1)
                   (serial-sub$valid-st st data-size cnt-size)
                   (serial-sub$inv st data-size)
                   (serial-sub$out-act inputs st data-size))
              (equal (car (serial-sub$extract st data-size))
                     (serial-sub$data-out st)))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d (get-field
                               serial-sub$valid-st
                               serial-sub$inv
                               serial-sub$extract
                               serial-sub$out-act
                               serial-sub$data-out)
                              (acl2::normalize-terms-such-as-a/a+b-+-b/a+b
                               acl2::prefer-positive-addends-<
                               acl2::simplify-products-gather-exponents-<
                               acl2::len-when-prefixp
                               acl2::take-when-prefixp
                               take-redefinition
                               not
                               default-car
                               default-cdr
                               true-listp
                               bv-is-true-list))))))

  (defthm comp-gcd-body2$extracted-step-correct
    (b* ((next-st (comp-gcd-body2$step inputs st data-size cnt-size)))
      (implies (and (comp-gcd-body2$input-format inputs data-size)
                    (comp-gcd-body2$valid-st st data-size cnt-size)
                    (comp-gcd-body2$inv st data-size))
               (equal (comp-gcd-body2$extract next-st data-size)
                      (comp-gcd-body2$extracted-step inputs st data-size))))
    :hints (("Goal"
             :use comp-gcd-body2$input-format=>sub$input-format
             :in-theory (e/d (get-field
                              joint-act
                              pos-len=>cons
                              fv-if-rewrite
                              serial-sub$valid-st=>constraint
                              serial-sub$extracted-step
                              comp-gcd-body2$extracted-step
                              comp-gcd-body2$valid-st
                              comp-gcd-body2$inv
                              comp-gcd-body2$step
                              comp-gcd-body2$a<b
                              comp-gcd-body2$in-act
                              comp-gcd-body2$out-act
                              comp-gcd-body2$extract
                              comp-gcd-body2$op)
                             (comp-gcd-body2$input-format=>sub$input-format)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that comp-gcd-body2$valid-st is an invariant.

(encapsulate
  ()

  (local
   (defthm comp-gcd-body2$sub-out-act-inactive
     (b* ((l2 (nth *comp-gcd-body2$l2* st))
          (l2.s (nth *link$s* l2))
          (sub (nth *comp-gcd-body2$sub* st))
          (sub-inputs (comp-gcd-body2$sub-inputs inputs st data-size)))
       (implies (fullp l2.s)
                (not (serial-sub$out-act sub-inputs
                                         sub
                                         data-size))))
     :hints (("Goal" :in-theory (enable get-field
                                        comp-gcd-body2$sub-inputs)))))

  (defthm comp-gcd-body2$valid-st-preserved
    (implies (and (comp-gcd-body2$input-format inputs data-size)
                  (comp-gcd-body2$valid-st st data-size cnt-size))
             (comp-gcd-body2$valid-st
              (comp-gcd-body2$step inputs st data-size cnt-size)
              data-size
              cnt-size))
    :hints (("Goal"
             :use comp-gcd-body2$input-format=>sub$input-format
             :in-theory (e/d (get-field
                              f-sr
                              joint-act
                              serial-sub$valid-st=>constraint
                              comp-gcd-body2$valid-st
                              comp-gcd-body2$step
                              comp-gcd-body2$a<b
                              comp-gcd-body2$in-act
                              comp-gcd-body2$out-act)
                             (comp-gcd-body2$input-format=>sub$input-format
                              if*)))))
  )

(defthm comp-gcd-body2$extract-lemma
  (implies (and (comp-gcd-body2$valid-st st data-size cnt-size)
                (comp-gcd-body2$inv st data-size)
                (comp-gcd-body2$out-act inputs st data-size))
           (equal (list (comp-gcd-body2$data-out st))
                  (nthcdr (1- (len (comp-gcd-body2$extract st data-size)))
                          (comp-gcd-body2$extract st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (len-0-is-atom
                            comp-gcd-body2$valid-st
                            comp-gcd-body2$inv
                            comp-gcd-body2$extract
                            comp-gcd-body2$out-act
                            comp-gcd-body2$data-out)
                           ()))))

;; Extract the accepted input sequence

(seq-gen comp-gcd-body2 in in-act 0
         (comp-gcd-body2$data-in inputs data-size)
         :sizes (data-size cnt-size))

;; Extract the valid output sequence

(seq-gen comp-gcd-body2 out out-act 1
         (comp-gcd-body2$data-out st)
         :netlist-data (nthcdr 2 outputs)
         :sizes (data-size cnt-size))

;; The multi-step input-output relationship

(encapsulate
  ()

  (local
   (defthm comp-gcd-body2$dataflow-correct-aux
     (implies (equal (append x y1)
                     (append (comp-gcd-body2$op-map seq) y2))
              (equal (append x y1 z)
                     (append (comp-gcd-body2$op-map seq)
                             y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (associativity-of-append))))))

  (defthmd comp-gcd-body2$dataflow-correct
    (b* ((extracted-st (comp-gcd-body2$extract st data-size))
         (final-st (comp-gcd-body2$run
                    inputs-seq st data-size cnt-size n))
         (final-extracted-st (comp-gcd-body2$extract final-st data-size)))
      (implies
       (and (comp-gcd-body2$input-format-n inputs-seq data-size n)
            (comp-gcd-body2$valid-st st data-size cnt-size)
            (comp-gcd-body2$inv st data-size))
       (equal (append final-extracted-st
                      (comp-gcd-body2$out-seq
                       inputs-seq st data-size cnt-size n))
              (append (comp-gcd-body2$op-map
                       (comp-gcd-body2$in-seq
                        inputs-seq st data-size cnt-size n))
                      extracted-st))))
    :hints (("Goal"
             :in-theory (enable comp-gcd-body2$extracted-step))))

  (defthmd comp-gcd-body2$functionally-correct
    (b* ((extracted-st (comp-gcd-body2$extract st data-size))
         (final-st (de-n (si 'comp-gcd-body2 data-size)
                         inputs-seq st netlist n))
         (final-extracted-st (comp-gcd-body2$extract final-st data-size)))
      (implies
       (and (comp-gcd-body2& netlist data-size cnt-size)
            (comp-gcd-body2$input-format-n inputs-seq data-size n)
            (comp-gcd-body2$valid-st st data-size cnt-size)
            (comp-gcd-body2$inv st data-size))
       (equal (append final-extracted-st
                      (comp-gcd-body2$out-seq-netlist
                       inputs-seq st netlist data-size n))
              (append (comp-gcd-body2$op-map
                       (comp-gcd-body2$in-seq-netlist
                        inputs-seq st netlist data-size n))
                      extracted-st))))
    :hints (("Goal"
             :use comp-gcd-body2$dataflow-correct
             :in-theory (enable comp-gcd-body2$valid-st=>st-format
                                comp-gcd-body2$de-n))))
  )



