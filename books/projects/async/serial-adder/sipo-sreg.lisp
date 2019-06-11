;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "../link-joint")
(include-book "../tv-if")
(include-book "../vector-module")
(include-book "../adders/counter")
(include-book "../comparators/fast-zero")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of SIPO-SREG
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of SIPO-SREG
;;
;; Construct a DE module generator that generates self-timed serial-in,
;; parallel-out (SIPO) shift register modules.  Prove the value and state
;; lemmas for this module generator.

(defconst *sipo-sreg$go-num* 2)

(defconst *sipo-sreg$data-ins-len* 3)

(defconst *sipo-sreg$ins-len*
  (+ *sipo-sreg$data-ins-len*
     *sipo-sreg$go-num*))

;; DE module generator of SIPO-SREG

(module-generator
 sipo-sreg* (data-size cnt-size)
 (si 'sipo-sreg data-size)
 (list* 'full-in 'empty-out- 'bit-in
        (sis 'go 0 *sipo-sreg$go-num*))
 (list* 'in-act 'out-act 'cnt-out=1 (sis 'data-out 0 data-size))
 '(r-data r-cnt w-data w-cnt)
 (list
  ;; LINKS
  ;; R-DATA
  (list 'r-data
        (list* 'r-data-status (sis 'r-data-out 0 data-size))
        (si 'link data-size)
        (list* 'buf-act 'shift-act (sis 'r-data-in 0 data-size)))

  ;; R-CNT
  (list 'r-cnt
        (list* 'r-cnt-status (sis 'r-cnt-out 0 cnt-size))
        (si 'link cnt-size)
        (list* 'buf-act 'shift-act (sis 'r-cnt-in 0 cnt-size)))

  ;; W-DATA
  (list 'w-data
        (list* 'w-data-status (sis 'w-data-out 0 data-size))
        (si 'link data-size)
        (list* 'shift-act 'buf-act (sis 'w-data-in 0 data-size)))

  ;; W-CNT
  (list 'w-cnt
        (list* 'w-cnt-status (sis 'w-cnt-out 0 cnt-size))
        (si 'link cnt-size)
        (list* 'shift-act 'buf-act (sis 'w-cnt-in 0 cnt-size)))

  '(g0 (low) vss ())
  '(g1 (high) vdd ())

  ;; JOINTS
  ;; Shift
  (list 'r-cnt=0?
        '(r-cnt=0)
        (si 'fast-zero cnt-size)
        (sis 'r-cnt-out 0 cnt-size))
  '(s0 (r-cnt=0~) b-not (r-cnt=0))
  '(s1 (shift-full-in) b-and4 (r-data-status r-cnt-status r-cnt=0~ full-in))
  '(s2 (r-full) b-and3 (r-data-status r-cnt-status r-cnt=0))
  '(s3 (w-empty-) b-or (w-data-status w-cnt-status))
  '(s4 (shift-empty-out-) b-or3 (w-data-status w-cnt-status empty-out-))

  (list 'in-cntl
        '(in-act)
        'joint-cntl
        (list 'shift-full-in 'w-empty- (si 'go 0)))
  (list 'shift-reg-op0
        (sis 'w-data-in0 0 data-size)
        (si 'v-buf data-size)
        (append (sis 'r-data-out 1 (1- data-size))
                '(bit-in)))
  (list 'shift-cnt-op0
        (sis 'w-cnt-in0 0 cnt-size)
        (si 'counter cnt-size)
        (sis 'r-cnt-out 0 cnt-size))

  (list 'out-cntl
        '(out-act)
        'joint-cntl
        (list 'r-full 'shift-empty-out- (si 'go 0)))
  (list 'shift-reg-op1
        (sis 'w-data-in1 0 data-size)
        (si 'v-buf data-size)
        (sis 'r-data-out 0 data-size))
  (list 'shift-cnt-op1
        (sis 'w-cnt-in1 0 cnt-size)
        (si 'v-buf cnt-size)
        (append (make-list (1- cnt-size) :initial-element 'low)
                '(high)))

  '(shift-cntl (shift-act) b-or (in-act out-act))
  (list 'shift-reg-op
        (sis 'w-data-in 0 data-size)
        (si 'tv-if (tree-number (make-tree data-size)))
        (cons 'r-cnt=0
              (append (sis 'w-data-in1 0 data-size)
                      (sis 'w-data-in0 0 data-size))))
  (list 'shift-cnt-op
        (sis 'w-cnt-in 0 cnt-size)
        (si 'tv-if (tree-number (make-tree cnt-size)))
        (cons 'r-cnt=0
              (append (sis 'w-cnt-in1 0 cnt-size)
                      (sis 'w-cnt-in0 0 cnt-size))))

  ;; Buffer
  '(b0 (buf-full-in) b-and (w-data-status w-cnt-status))
  '(b1 (buf-empty-out-) b-or (r-data-status r-cnt-status))
  (list 'buf-cntl
        '(buf-act)
        'joint-cntl
        (list 'buf-full-in 'buf-empty-out- (si 'go 1)))
  (list 'buf-reg-op
        (sis 'r-data-in 0 data-size)
        (si 'v-buf data-size)
        (sis 'w-data-out 0 data-size))
  (list 'buf-cnt-op
        (sis 'r-cnt-in 0 cnt-size)
        (si 'v-buf cnt-size)
        (sis 'w-cnt-out 0 cnt-size))

  ;; OUTPUTS
  (list 'reg-out
        (sis 'data-out 0 data-size)
        (si 'v-wire data-size)
        (sis 'r-data-out 0 data-size))
  (list 'cnt-out<2?
        '(cnt-out<2)
        (si 'fast-zero (1- cnt-size))
        (sis 'r-cnt-out 1 (1- cnt-size)))
  (list 'cnt-out=1?
        '(cnt-out=1)
        'b-and
        (list (si 'r-cnt-out 0) 'cnt-out<2)))

 (declare (xargs :guard (and (posp data-size) (posp cnt-size)))))

(make-event
 `(progn
    ,@(state-accessors-gen 'sipo-sreg
                           '(r-data r-cnt w-data w-cnt)
                           0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; SIPO-SREG.

(defund sipo-sreg$netlist (data-size cnt-size)
  (declare (xargs :guard (and (posp data-size)
                              (natp cnt-size)
                              (<= 3 cnt-size))))
  (cons (sipo-sreg* data-size cnt-size)
        (union$ (link$netlist data-size)
                (link$netlist cnt-size)
                *joint-cntl*
                (fast-zero$netlist (1- cnt-size))
                (fast-zero$netlist cnt-size)
                (counter$netlist cnt-size)
                (v-buf$netlist data-size)
                (v-buf$netlist cnt-size)
                (v-wire$netlist data-size)
                (v-wire$netlist cnt-size)
                (tv-if$netlist (make-tree data-size))
                (tv-if$netlist (make-tree cnt-size))
                :test 'equal)))

;; Recognizer for SIPO-SREG

(defund sipo-sreg& (netlist data-size cnt-size)
  (declare (xargs :guard (and (alistp netlist)
                              (posp data-size)
                              (natp cnt-size)
                              (<= 3 cnt-size))))
  (b* ((subnetlist (delete-to-eq (si 'sipo-sreg data-size)
                                 netlist)))
    (and (equal (assoc (si 'sipo-sreg data-size) netlist)
                (sipo-sreg* data-size cnt-size))
         (link& subnetlist data-size)
         (link& subnetlist cnt-size)
         (joint-cntl& subnetlist)
         (fast-zero& subnetlist (1- cnt-size))
         (fast-zero& subnetlist cnt-size)
         (counter& subnetlist cnt-size)
         (v-buf& subnetlist data-size)
         (v-buf& subnetlist cnt-size)
         (v-wire& subnetlist data-size)
         (v-wire& subnetlist cnt-size)
         (tv-if& subnetlist (make-tree data-size))
         (tv-if& subnetlist (make-tree cnt-size)))))

;; Sanity check

(local
 (defthmd check-sipo-sreg$netlist-64-7
   (and (net-syntax-okp (sipo-sreg$netlist 64 7))
        (net-arity-okp (sipo-sreg$netlist 64 7))
        (sipo-sreg& (sipo-sreg$netlist 64 7) 64 7))))

;; Constraints on the state of SIPO-SREG

(defund sipo-sreg$st-format (st data-size cnt-size)
  (b* ((r-data (nth *sipo-sreg$r-data* st))
       (r-cnt (nth *sipo-sreg$r-cnt* st))
       (w-data (nth *sipo-sreg$w-data* st))
       (w-cnt (nth *sipo-sreg$w-cnt* st)))
    (and (posp data-size)
         (natp cnt-size)
         (<= 4 cnt-size)
         (link$st-format r-data data-size)
         (link$st-format r-cnt cnt-size)
         (link$st-format w-data data-size)
         (link$st-format w-cnt cnt-size))))

(defthm sipo-sreg$st-format=>constraint
  (implies (sipo-sreg$st-format st data-size cnt-size)
           (and (posp data-size)
                (natp cnt-size)
                (<= 4 cnt-size)))
  :hints (("Goal" :in-theory (enable sipo-sreg$st-format)))
  :rule-classes :forward-chaining)

(defund sipo-sreg$valid-st (st data-size cnt-size)
  (b* ((r-data (nth *sipo-sreg$r-data* st))
       (r-cnt (nth *sipo-sreg$r-cnt* st))
       (w-data (nth *sipo-sreg$w-data* st))
       (w-cnt (nth *sipo-sreg$w-cnt* st)))
    (and (sipo-sreg$st-format st data-size cnt-size)
         (equal data-size (expt 2 (1- cnt-size)))
         (link$valid-st r-data data-size)
         (link$valid-st r-cnt cnt-size)
         (link$valid-st w-data data-size)
         (link$valid-st w-cnt cnt-size))))

(local
 (defthm expt-linear-lower-<=-instance
   (implies (and (<= 3 n)
                 (integerp n))
            (<= 8 (expt 2 n)))
   :rule-classes :linear))

(defthmd sipo-sreg$valid-st=>constraint
  (implies (sipo-sreg$valid-st st data-size cnt-size)
           (and (natp data-size)
                (<= 8 data-size)
                (natp cnt-size)
                (<= 4 cnt-size)))
  :hints (("Goal" :in-theory (enable sipo-sreg$valid-st)))
  :rule-classes :forward-chaining)

(defthmd sipo-sreg$valid-st=>st-format
  (implies (sipo-sreg$valid-st st data-size cnt-size)
           (sipo-sreg$st-format st data-size cnt-size))
  :hints (("Goal" :in-theory (enable sipo-sreg$valid-st))))

;; Extract the input and output signals for SIPO-SREG

(progn
  ;; Extract the input data

  (defun sipo-sreg$bit-in (inputs)
    (declare (xargs :guard (true-listp inputs)))
    (nth 2 inputs))

  (in-theory (disable sipo-sreg$bit-in))

  ;; Extract the "in-act" signal

  (defund sipo-sreg$in-act (inputs st)
    (b* ((full-in (nth 0 inputs))
         (go-signals (nthcdr *sipo-sreg$data-ins-len* inputs))
         (go-shift (nth 0 go-signals))

         (r-data (nth *sipo-sreg$r-data* st))
         (r-data.s (nth *link$s* r-data))
         (r-cnt (nth *sipo-sreg$r-cnt* st))
         (r-cnt.s (nth *link$s* r-cnt))
         (r-cnt.d (nth *link$d* r-cnt))
         (w-data (nth *sipo-sreg$w-data* st))
         (w-data.s (nth *link$s* w-data))
         (w-cnt (nth *sipo-sreg$w-cnt* st))
         (w-cnt.s (nth *link$s* w-cnt))

         (r-cnt=0~ (f-not (f$fast-zero (strip-cars r-cnt.d))))
         (shift-full-in (f-and4 (car r-data.s) (car r-cnt.s)
                                r-cnt=0~ full-in))
         (w-empty- (f-or (car w-data.s) (car w-cnt.s))))
      (joint-act shift-full-in w-empty- go-shift)))

  (defthm sipo-sreg$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (sipo-sreg$in-act inputs st)))
    :hints (("Goal" :in-theory (enable f-and4
                                       sipo-sreg$in-act))))

  ;; Extract the "out-act" signal

  (defund sipo-sreg$out-act (inputs st)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr *sipo-sreg$data-ins-len* inputs))
         (go-shift (nth 0 go-signals))

         (r-data (nth *sipo-sreg$r-data* st))
         (r-data.s (nth *link$s* r-data))
         (r-cnt (nth *sipo-sreg$r-cnt* st))
         (r-cnt.s (nth *link$s* r-cnt))
         (r-cnt.d (nth *link$d* r-cnt))
         (w-data (nth *sipo-sreg$w-data* st))
         (w-data.s (nth *link$s* w-data))
         (w-cnt (nth *sipo-sreg$w-cnt* st))
         (w-cnt.s (nth *link$s* w-cnt))

         (r-cnt=0 (f$fast-zero (strip-cars r-cnt.d)))
         (r-full (f-and3 (car r-data.s) (car r-cnt.s) r-cnt=0))
         (shift-empty-out- (f-or3 (car w-data.s) (car w-cnt.s) empty-out-)))
      (joint-act r-full shift-empty-out- go-shift)))

  (defthm sipo-sreg$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (sipo-sreg$out-act inputs st)))
    :hints (("Goal" :in-theory (enable f-or3
                                       sipo-sreg$out-act))))

  (defthm sipo-sreg$in-out-acts-mutually-exclusive
    (implies (and (sipo-sreg$valid-st st data-size cnt-size)
                  (sipo-sreg$in-act inputs st))
             (not (sipo-sreg$out-act inputs st)))
    :hints (("Goal" :in-theory (enable f-and4
                                       sipo-sreg$valid-st
                                       sipo-sreg$in-act
                                       sipo-sreg$out-act))))

  ;; Extract the output data

  (defund sipo-sreg$cnt-out=1 (st)
    (b* ((r-cnt (nth *sipo-sreg$r-cnt* st))
         (r-cnt.d (nth *link$d* r-cnt)))
      (f-and (car (strip-cars r-cnt.d))
             (f$fast-zero (nthcdr 1 (strip-cars r-cnt.d))))))

  (local
   (defthm len-cdr
     (implies (< 0 (len x))
              (equal (len (cdr x))
                     (1- (len x))))))

  (defthm booleanp-sipo-sreg$cnt-out=1-1
    (implies (and (sipo-sreg$valid-st st data-size cnt-size)
                  (sipo-sreg$in-act inputs st))
             (booleanp (sipo-sreg$cnt-out=1 st)))
    :hints (("Goal" :in-theory (enable f-and4
                                       bvp
                                       sipo-sreg$valid-st
                                       sipo-sreg$in-act
                                       sipo-sreg$cnt-out=1)))
    :rule-classes (:rewrite :type-prescription))

  (defthm booleanp-sipo-sreg$cnt-out=1-2
    (implies (and (sipo-sreg$valid-st st data-size cnt-size)
                  (sipo-sreg$out-act inputs st))
             (booleanp (sipo-sreg$cnt-out=1 st)))
    :hints (("Goal" :in-theory (enable f-and3
                                       bvp
                                       sipo-sreg$valid-st
                                       sipo-sreg$out-act
                                       sipo-sreg$cnt-out=1)))
    :rule-classes (:rewrite :type-prescription))

  (defund sipo-sreg$data-out (st)
    (b* ((r-data (nth *sipo-sreg$r-data* st))
         (r-data.d (nth *link$d* r-data)))
      (v-threefix (strip-cars r-data.d))))

  (defthm len-sipo-sreg$data-out-1
    (implies (sipo-sreg$st-format st data-size cnt-size)
             (equal (len (sipo-sreg$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable sipo-sreg$st-format
                                       sipo-sreg$data-out))))

  (defthm len-sipo-sreg$data-out-2
    (implies (sipo-sreg$valid-st st data-size cnt-size)
             (equal (len (sipo-sreg$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable sipo-sreg$valid-st
                                       sipo-sreg$data-out))))

  (defthm bvp-sipo-sreg$data-out-1
    (implies (and (sipo-sreg$valid-st st data-size cnt-size)
                  (sipo-sreg$in-act inputs st))
             (bvp (sipo-sreg$data-out st)))
    :hints (("Goal" :in-theory (enable f-and4
                                       sipo-sreg$valid-st
                                       sipo-sreg$in-act
                                       sipo-sreg$data-out))))

  (defthm bvp-sipo-sreg$data-out-2
    (implies (and (sipo-sreg$valid-st st data-size cnt-size)
                  (sipo-sreg$out-act inputs st))
             (bvp (sipo-sreg$data-out st)))
    :hints (("Goal" :in-theory (enable f-and3
                                       sipo-sreg$valid-st
                                       sipo-sreg$out-act
                                       sipo-sreg$data-out))))

  (defun sipo-sreg$outputs (inputs st)
    (list* (sipo-sreg$in-act inputs st)
           (sipo-sreg$out-act inputs st)
           (sipo-sreg$cnt-out=1 st)
           (sipo-sreg$data-out st)))
  )

;; The value lemma for SIPO-SREG

(defthm sipo-sreg$value
  (b* ((inputs (list* full-in empty-out- bit-in go-signals)))
    (implies (and (sipo-sreg& netlist data-size cnt-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *sipo-sreg$go-num*)
                  (sipo-sreg$st-format st data-size cnt-size))
             (equal (se (si 'sipo-sreg data-size) inputs st netlist)
                    (sipo-sreg$outputs inputs st))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'sipo-sreg data-size)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            sipo-sreg&
                            sipo-sreg*$destructure
                            sipo-sreg$st-format
                            sipo-sreg$in-act
                            sipo-sreg$out-act
                            sipo-sreg$cnt-out=1
                            sipo-sreg$data-out)
                           (car-cdr-elim
                            de-module-disabled-rules)))))

;; This function specifies the next state of SIPO-SREG.

(defun sipo-sreg$step (inputs st data-size cnt-size)
  (b* ((bit-in     (sipo-sreg$bit-in inputs))
       (go-signals (nthcdr *sipo-sreg$data-ins-len* inputs))
       (go-buf (nth 1 go-signals))

       (r-data (nth *sipo-sreg$r-data* st))
       (r-data.s (nth *link$s* r-data))
       (r-data.d (nth *link$d* r-data))
       (r-cnt (nth *sipo-sreg$r-cnt* st))
       (r-cnt.s (nth *link$s* r-cnt))
       (r-cnt.d (nth *link$d* r-cnt))
       (w-data (nth *sipo-sreg$w-data* st))
       (w-data.s (nth *link$s* w-data))
       (w-data.d (nth *link$d* w-data))
       (w-cnt (nth *sipo-sreg$w-cnt* st))
       (w-cnt.s (nth *link$s* w-cnt))
       (w-cnt.d (nth *link$d* w-cnt))

       (r-cnt=0 (f$fast-zero (strip-cars r-cnt.d)))
       (in-act (sipo-sreg$in-act inputs st))
       (out-act (sipo-sreg$out-act inputs st))
       (shift-act (f-or in-act out-act))

       (buf-full-in (f-and (car w-data.s) (car w-cnt.s)))
       (buf-empty-out- (f-or (car r-data.s) (car r-cnt.s)))
       (buf-act (joint-act buf-full-in buf-empty-out- go-buf))

       (r-data-inputs (list* buf-act shift-act (strip-cars w-data.d)))
       (r-cnt-inputs (list* buf-act shift-act (strip-cars w-cnt.d)))
       (w-data-inputs (list* shift-act buf-act
                            (fv-if r-cnt=0
                                   (strip-cars r-data.d)
                                   (append (nthcdr 1 (v-threefix
                                                      (strip-cars r-data.d)))
                                           (list bit-in)))))
       (w-cnt-inputs
        (list* shift-act buf-act
               (fv-if r-cnt=0
                      (append (make-list (1- cnt-size))
                              '(t))
                      (fv-adder-output
                       t
                       (strip-cars r-cnt.d)
                       (fv-not
                        (cons t (make-list (1- cnt-size)))))))))
    (list
     ;; R-DATA
     (link$step r-data-inputs r-data data-size)
     ;; R-CNT
     (link$step r-cnt-inputs r-cnt cnt-size)
     ;; W-DATA
     (link$step w-data-inputs w-data data-size)
     ;; W-CNT
     (link$step w-cnt-inputs w-cnt cnt-size))))

;; The state lemma for SIPO-SREG

(defthm sipo-sreg$state
  (b* ((inputs (list* full-in empty-out- bit-in go-signals)))
    (implies
     (and (sipo-sreg& netlist data-size cnt-size)
          (true-listp go-signals)
          (equal (len go-signals) *sipo-sreg$go-num*)
          (sipo-sreg$st-format st data-size cnt-size))
     (equal (de (si 'sipo-sreg data-size) inputs st netlist)
            (sipo-sreg$step inputs st data-size cnt-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'sipo-sreg data-size)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            sipo-sreg&
                            sipo-sreg*$destructure
                            sipo-sreg$bit-in
                            sipo-sreg$in-act
                            sipo-sreg$out-act
                            sipo-sreg$st-format)
                           (append-v-threefix
                            associativity-of-append
                            de-module-disabled-rules)))))

(in-theory (disable sipo-sreg$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund sipo-sreg$input-format (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (bit-in     (sipo-sreg$bit-in inputs))
       (go-signals (nthcdr *sipo-sreg$data-ins-len* inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (booleanp bit-in))
     (true-listp go-signals)
     (= (len go-signals) *sipo-sreg$go-num*)
     (equal inputs
            (list* full-in empty-out- bit-in go-signals)))))

(defthm booleanp-sipo-sreg$in-act
  (implies (and (sipo-sreg$input-format inputs)
                (sipo-sreg$valid-st st data-size cnt-size))
           (booleanp (sipo-sreg$in-act inputs st)))
  :hints (("Goal"
           :in-theory (e/d (f-and4
                            sipo-sreg$input-format
                            sipo-sreg$valid-st
                            sipo-sreg$in-act)
                           ())))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-sipo-sreg$out-act
  (implies (and (sipo-sreg$input-format inputs)
                (sipo-sreg$valid-st st data-size cnt-size))
           (booleanp (sipo-sreg$out-act inputs st)))
  :hints (("Goal"
           :in-theory (e/d (f-and3
                            sipo-sreg$input-format
                            sipo-sreg$valid-st
                            sipo-sreg$out-act)
                           ())))
  :rule-classes (:rewrite :type-prescription))

;;(simulate-lemma sipo-sreg nil data-size cnt-size)

(progn
  (defthm sipo-sreg$st-format-preserved
    (implies
     (sipo-sreg$st-format st data-size cnt-size)
     (sipo-sreg$st-format (sipo-sreg$step
                                     inputs st data-size cnt-size)
                                    data-size
                                    cnt-size))
    :hints (("Goal" :in-theory (enable sipo-sreg$step
                                       sipo-sreg$st-format))))

  (defthmd sipo-sreg$value-alt
    (implies
     (and (sipo-sreg& netlist data-size cnt-size)
          (sipo-sreg$input-format inputs)
          (sipo-sreg$st-format st data-size cnt-size))
     (equal (se (si 'sipo-sreg data-size) inputs st netlist)
            (sipo-sreg$outputs inputs st)))
    :hints (("Goal" :in-theory (enable sipo-sreg$input-format))))

  (defthmd sipo-sreg$state-alt
    (implies
     (and (sipo-sreg& netlist data-size cnt-size)
          (sipo-sreg$input-format inputs)
          (sipo-sreg$st-format st data-size cnt-size))
     (equal (de (si 'sipo-sreg data-size) inputs st netlist)
            (sipo-sreg$step inputs st data-size cnt-size)))
    :hints (("Goal" :in-theory (enable sipo-sreg$input-format))))

  (run-gen sipo-sreg data-size cnt-size)
  (input-format-n-gen sipo-sreg)

  (defthmd sipo-sreg$de-n
    (implies (and (sipo-sreg& netlist data-size cnt-size)
                  (sipo-sreg$input-format-n inputs-seq n)
                  (sipo-sreg$st-format st data-size cnt-size))
             (equal (de-n (si 'sipo-sreg data-size)
                          inputs-seq st netlist n)
                    (sipo-sreg$run
                     inputs-seq st data-size cnt-size n)))
    :hints (("Goal" :in-theory (enable sipo-sreg$run
                                       sipo-sreg$state-alt)))))

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for SIPO-SREG

(defund sipo-sreg$extract (st)
  (b* ((r-data (nth *sipo-sreg$r-data* st))
       (r-data.s (nth *link$s* r-data))
       (r-data.d (nth *link$d* r-data))
       (r-cnt (nth *sipo-sreg$r-cnt* st))
       (r-cnt.d (nth *link$d* r-cnt))
       (w-data (nth *sipo-sreg$w-data* st))
       (w-data.d (nth *link$d* w-data))
       (w-cnt (nth *sipo-sreg$w-cnt* st))
       (w-cnt.d (nth *link$d* w-cnt)))
    (if (fullp r-data.s)
        (nthcdr (v-to-nat (strip-cars r-cnt.d))
                (strip-cars r-data.d))
      (nthcdr (v-to-nat (strip-cars w-cnt.d))
              (strip-cars w-data.d)))))

(local
 (defthm v-to-nat-of-v-zp
   (equal (v-zp x)
          (equal (v-to-nat x) 0))
   :hints (("Goal" :in-theory (enable v-zp v-nzp v-to-nat)))))

(defthm sipo-sreg$extract-not-empty
  (implies (and (sipo-sreg$out-act inputs st)
                (sipo-sreg$valid-st st data-size cnt-size))
           (< 0 (len (sipo-sreg$extract st))))
  :hints (("Goal"
           :in-theory (e/d (f-and
                            f-and3
                            sipo-sreg$valid-st
                            sipo-sreg$extract
                            sipo-sreg$out-act)
                           ())))
  :rule-classes :linear)

(defthmd len-of-sipo-sreg$extract-lemma
  (implies (and (sipo-sreg$out-act inputs st)
                (sipo-sreg$valid-st st data-size cnt-size))
           (equal (len (sipo-sreg$extract st))
                  data-size))
  :hints (("Goal" :in-theory (enable f-and3
                                     f-and
                                     f-or3
                                     joint-act
                                     sipo-sreg$valid-st
                                     sipo-sreg$out-act
                                     sipo-sreg$extract))))

(defthm len-of-sipo-sreg$extract-contrapositive-lemma-1
  (implies (and (sipo-sreg$out-act inputs st)
                (not (equal (len (sipo-sreg$extract st))
                            data-size)))
           (not (sipo-sreg$valid-st st data-size cnt-size)))
  :hints (("Goal" :in-theory (enable f-and3
                                     f-and
                                     f-or3
                                     joint-act
                                     sipo-sreg$valid-st
                                     sipo-sreg$out-act
                                     sipo-sreg$extract))))

(defthm len-of-sipo-sreg$extract-contrapositive-lemma-2
  (implies (and (sipo-sreg$valid-st st data-size cnt-size)
                (not (equal (len (sipo-sreg$extract st))
                            data-size)))
           (not (sipo-sreg$out-act inputs st)))
  :hints (("Goal" :in-theory (enable f-and3
                                     f-and
                                     f-or3
                                     joint-act
                                     sipo-sreg$valid-st
                                     sipo-sreg$out-act
                                     sipo-sreg$extract))))

;; Specify and prove a state invariant

(progn
  (defund sipo-sreg$inv (st)
    (b* ((r-data (nth *sipo-sreg$r-data* st))
         (r-data.s (nth *link$s* r-data))
         (r-data.d (nth *link$d* r-data))
         (r-cnt (nth *sipo-sreg$r-cnt* st))
         (r-cnt.s (nth *link$s* r-cnt))
         (r-cnt.d (nth *link$d* r-cnt))
         (w-data (nth *sipo-sreg$w-data* st))
         (w-data.s (nth *link$s* w-data))
         (w-data.d (nth *link$d* w-data))
         (w-cnt (nth *sipo-sreg$w-cnt* st))
         (w-cnt.s (nth *link$s* w-cnt))
         (w-cnt.d (nth *link$d* w-cnt)))
      (and (equal r-data.s r-cnt.s)
           (equal w-data.s w-cnt.s)
           (not (equal r-data.s w-data.s))

           (or (emptyp r-cnt.s)
               (<= (v-to-nat (strip-cars r-cnt.d))
                   (len r-data.d)))
           (or (emptyp w-cnt.s)
               (<= (v-to-nat (strip-cars w-cnt.d))
                   (len w-data.d))))))

  (defthm len-of-sipo-sreg$extract-upper-bound
    (implies (and (sipo-sreg$valid-st st data-size cnt-size)
                  (sipo-sreg$inv st))
             (<= (len (sipo-sreg$extract st))
                 data-size))
    :hints (("Goal" :in-theory (enable sipo-sreg$valid-st
                                       sipo-sreg$inv
                                       sipo-sreg$extract)))
    :rule-classes :linear)

  (defthm len-of-sipo-sreg$extract-upper-bound-when-in-act
    (implies (and (sipo-sreg$in-act inputs st)
                  (sipo-sreg$valid-st st data-size cnt-size)
                  (sipo-sreg$inv st))
             (< (len (sipo-sreg$extract st))
                data-size))
    :hints (("Goal" :in-theory (e/d (f-and4
                                     sipo-sreg$valid-st
                                     sipo-sreg$st-format
                                     sipo-sreg$inv
                                     sipo-sreg$in-act
                                     sipo-sreg$extract)
                                    (acl2::prefer-positive-addends-equal))))
    :rule-classes :linear)

  (local
   (defthm sipo-sreg$input-format-lemma-1
     (implies (sipo-sreg$input-format inputs)
              (booleanp (nth 0 inputs)))
     :hints (("Goal" :in-theory (enable sipo-sreg$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm sipo-sreg$input-format-lemma-2
     (implies (sipo-sreg$input-format inputs)
              (booleanp (nth 1 inputs)))
     :hints (("Goal" :in-theory (enable sipo-sreg$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm sipo-sreg$input-format-lemma-3
     (implies (and (sipo-sreg$input-format inputs)
                   (nth 0 inputs))
              (booleanp (sipo-sreg$bit-in inputs)))
     :hints (("Goal" :in-theory (enable sipo-sreg$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm v-to-nat-of-repeat-lemma
     (equal (v-to-nat (append (repeat n nil) '(t)))
            (expt 2 (nfix n)))
     :hints (("Goal" :in-theory (enable v-to-nat repeat)))))

  (defthm sipo-sreg$inv-preserved
    (implies (and (sipo-sreg$input-format inputs)
                  (sipo-sreg$valid-st st data-size cnt-size)
                  (sipo-sreg$inv st))
             (sipo-sreg$inv
              (sipo-sreg$step inputs st data-size cnt-size)))
    :hints (("Goal"
             :in-theory (e/d (f-sr
                              bvp
                              sipo-sreg$st-format
                              sipo-sreg$valid-st
                              sipo-sreg$inv
                              sipo-sreg$step
                              sipo-sreg$in-act
                              sipo-sreg$out-act)
                             ()))))
  )

;; The extracted next-state function for SIPO-SREG.  Note that this function
;; avoids exploring the internal computation of SIPO-SREG.

(defund sipo-sreg$extracted-step (inputs st)
  (b* ((data (sipo-sreg$bit-in inputs))
       (extracted-st (sipo-sreg$extract st)))
    (cond
     ((equal (sipo-sreg$out-act inputs st) t)
      nil)
     ((equal (sipo-sreg$in-act inputs st) t)
      (append extracted-st (list data)))
     (t extracted-st))))

;; The single-step-update property

(progn
  (local
   (defthm nthcdr-append-2
     (implies (<= n (len x))
              (equal (nthcdr n (append x y))
                     (append (nthcdr n x) y)))))

  (local
   (defthm nthcdr-of-len-of-list
     (implies (and (equal n (len l))
                   (true-listp l))
              (not (nthcdr n l)))))

  (defthm sipo-sreg$extracted-step-correct
    (b* ((next-st (sipo-sreg$step inputs st data-size cnt-size)))
      (implies (and (sipo-sreg$input-format inputs)
                    (sipo-sreg$valid-st st data-size cnt-size)
                    (sipo-sreg$inv st))
               (equal (sipo-sreg$extract next-st)
                      (sipo-sreg$extracted-step inputs st))))
    :hints (("Goal"
             :in-theory (e/d (f-sr
                              joint-act
                              bvp
                              pos-len=>cons
                              sipo-sreg$extracted-step
                              sipo-sreg$valid-st
                              sipo-sreg$inv
                              sipo-sreg$step
                              sipo-sreg$in-act
                              sipo-sreg$out-act
                              sipo-sreg$extract)
                             ()))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that sipo-sreg$valid-st is an invariant.

(defthm sipo-sreg$valid-st-preserved
  (implies (and (sipo-sreg$input-format inputs)
                (sipo-sreg$valid-st st data-size cnt-size))
           (sipo-sreg$valid-st
            (sipo-sreg$step inputs st data-size cnt-size)
            data-size
            cnt-size))
  :hints (("Goal"
           :in-theory (e/d (f-sr
                            joint-act
                            bvp
                            f-and3
                            f-and4
                            pos-len=>cons
                            sipo-sreg$st-format
                            sipo-sreg$valid-st
                            sipo-sreg$step
                            sipo-sreg$in-act
                            sipo-sreg$out-act)
                           (if*)))))

(defthm sipo-sreg$extract-lemma
  (implies (and (sipo-sreg$valid-st st data-size cnt-size)
                (sipo-sreg$out-act inputs st))
           (equal (sipo-sreg$data-out st)
                  (sipo-sreg$extract st)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (joint-act
                            f-and
                            f-and3
                            f-or3
                            sipo-sreg$valid-st
                            sipo-sreg$extract
                            sipo-sreg$out-act
                            sipo-sreg$data-out)
                           ()))))

;; Extract the accepted input sequence

(defun sipo-sreg$in-seq (inputs-seq st data-size cnt-size n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-seq))
         (in-act (sipo-sreg$in-act inputs st))
         (data (sipo-sreg$bit-in inputs)))
      (if (equal in-act t)
          (append (sipo-sreg$in-seq
                   (cdr inputs-seq)
                   (sipo-sreg$step inputs st data-size cnt-size)
                   data-size
                   cnt-size
                   (1- n))
                  (list data))
        (sipo-sreg$in-seq
         (cdr inputs-seq)
         (sipo-sreg$step inputs st data-size cnt-size)
         data-size
         cnt-size
         (1- n))))))

(defun sipo-sreg$in-seq-netlist
    (inputs-seq st netlist data-size n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-seq))
         (outputs (se (si 'sipo-sreg data-size)
                      inputs st netlist))
         (in-act (nth 0 outputs))
         (data (sipo-sreg$bit-in inputs)))
      (if (equal in-act t)
          (append (sipo-sreg$in-seq-netlist
                   (cdr inputs-seq)
                   (de (si 'sipo-sreg data-size)
                       inputs st netlist)
                   netlist
                   data-size
                   (1- n))
                  (list data))
        (sipo-sreg$in-seq-netlist
         (cdr inputs-seq)
         (de (si 'sipo-sreg data-size)
             inputs st netlist)
         netlist
         data-size
         (1- n))))))

(defthm sipo-sreg$in-seq-lemma
  (implies (and (sipo-sreg& netlist data-size cnt-size)
                (sipo-sreg$input-format-n inputs-seq n)
                (sipo-sreg$st-format st data-size cnt-size))
           (equal (sipo-sreg$in-seq-netlist
                   inputs-seq st netlist data-size n)
                  (sipo-sreg$in-seq
                   inputs-seq st data-size cnt-size n)))
  :hints (("Goal" :in-theory (enable sipo-sreg$value-alt
                                     sipo-sreg$state-alt))))

;; Extract the valid output sequence

(defun sipo-sreg$out-seq (inputs-seq st data-size cnt-size n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-seq))
         (out-act (sipo-sreg$out-act inputs st))
         (data (sipo-sreg$data-out st))
         (seq (sipo-sreg$out-seq
               (cdr inputs-seq)
               (sipo-sreg$step inputs st data-size cnt-size)
               data-size
               cnt-size
               (1- n))))
      (if (equal out-act t)
          (append seq (list data))
        seq))))

(defun sipo-sreg$out-seq-netlist
    (inputs-seq st netlist data-size n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-seq))
         (outputs (se (si 'sipo-sreg data-size)
                      inputs st netlist))
         (out-act (nth 1 outputs))
         (data (take data-size (nthcdr 3 outputs)))
         (seq (sipo-sreg$out-seq-netlist
               (cdr inputs-seq)
               (de (si 'sipo-sreg data-size)
                   inputs st netlist)
               netlist
               data-size
               (1- n))))
      (if (equal out-act t)
          (append seq (list data))
        seq))))

(defthm sipo-sreg$out-seq-lemma
  (implies (and (sipo-sreg& netlist data-size cnt-size)
                (sipo-sreg$input-format-n inputs-seq n)
                (sipo-sreg$st-format st data-size cnt-size))
           (equal (sipo-sreg$out-seq-netlist
                   inputs-seq st netlist data-size n)
                  (sipo-sreg$out-seq
                   inputs-seq st data-size cnt-size n)))
  :hints (("Goal" :in-theory (enable sipo-sreg$value-alt
                                     sipo-sreg$state-alt))))

;; The multi-step input-output relationship

(encapsulate
  ()

  (defund append1 (x y)
    (declare (xargs :guard t))
    (if (atom x)
        y
      (append (list x) y)))

  (defund pack-rev (n l)
    (declare (xargs :guard (and (natp n)
                                (true-listp l))))
    (if (or (zp n) (atom l))
        nil
      (if (<= (len l) n)
          (list l)
        (append (pack-rev n (nthcdr n l))
                (list (take n l))))))

  (local
   (defthm sipo-sreg$dataflow-correct-aux
     (implies (and (sipo-sreg$valid-st st data-size cnt-size)
                   (sipo-sreg$inv st)
                   (consp (sipo-sreg$extract st)))
              (equal (pack-rev data-size
                               (sipo-sreg$extract st))
                     (list (sipo-sreg$extract st))))
     :hints
     (("Goal"
       :use len-of-sipo-sreg$extract-upper-bound
       :in-theory (e/d (sipo-sreg$valid-st=>constraint
                        pack-rev)
                       (len-of-sipo-sreg$extract-upper-bound))))))

  (defthmd sipo-sreg$dataflow-correct
    (b* ((extracted-st (sipo-sreg$extract st))
         (final-st (sipo-sreg$run
                    inputs-seq st data-size cnt-size n))
         (final-extracted-st (sipo-sreg$extract final-st)))
      (implies
       (and (sipo-sreg$input-format-n inputs-seq n)
            (sipo-sreg$valid-st st data-size cnt-size)
            (sipo-sreg$inv st))
       (equal (append1 final-extracted-st
                       (sipo-sreg$out-seq
                        inputs-seq st data-size cnt-size n))
              (pack-rev
               data-size
               (append extracted-st
                       (rev (sipo-sreg$in-seq
                             inputs-seq st data-size cnt-size n)))))))
    :hints (("Goal"
             :induct (sipo-sreg$in-seq
                      inputs-seq st data-size cnt-size n)
             :in-theory (enable append1
                                pack-rev
                                sipo-sreg$valid-st=>constraint
                                len-of-sipo-sreg$extract-lemma
                                sipo-sreg$extracted-step))))

  (defthmd sipo-sreg$functionally-correct
    (b* ((extracted-st (sipo-sreg$extract st))
         (final-st (de-n (si 'sipo-sreg data-size)
                         inputs-seq st netlist n))
         (final-extracted-st (sipo-sreg$extract final-st)))
      (implies
       (and (sipo-sreg& netlist data-size cnt-size)
            (sipo-sreg$input-format-n inputs-seq n)
            (sipo-sreg$valid-st st data-size cnt-size)
            (sipo-sreg$inv st))
       (equal (append1 final-extracted-st
                       (sipo-sreg$out-seq-netlist
                        inputs-seq st netlist data-size n))
              (pack-rev
               data-size
               (append extracted-st
                       (rev (sipo-sreg$in-seq-netlist
                             inputs-seq st netlist data-size n)))))))
    :hints (("Goal"
             :use sipo-sreg$dataflow-correct
             :in-theory (enable sipo-sreg$valid-st=>st-format
                                sipo-sreg$de-n))))
  )

