;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; November 2018

(in-package "ADE")

(include-book "../link-joint")
(include-book "../tv-if")
(include-book "../vector-module")
(include-book "../adders/counter")
(include-book "../comparators/fast-zero")

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of PISO-SREG
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of PISO-SREG
;;
;; Construct a DE module generator that generates self-timed parallel-in,
;; serial-out (PISO) shift register modules.  Prove the value and state lemmas
;; for this module generator.

(defconst *piso-sreg$go-num* 2)
(defconst *piso-sreg$st-len* 4)

(defun piso-sreg$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun piso-sreg$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (piso-sreg$data-ins-len data-width)
     *piso-sreg$go-num*))

;; DE module generator of PISO-SREG

(module-generator
 piso-sreg* (data-width cnt-width)
 (si 'piso-sreg data-width)
 (list* 'full-in 'empty-out-
        (append (sis 'data-in 0 data-width)
                (sis 'go 0 *piso-sreg$go-num*)))
 '(in-act out-act bit-out)
 '(r-data r-cnt w-data w-cnt)
 (list
  ;; LINKS
  ;; R-DATA
  (list 'r-data
        (list* 'r-data-status (sis 'r-data-out 0 data-width))
        (si 'link data-width)
        (list* 'buf-act 'shift-act (sis 'r-data-in 0 data-width)))

  ;; R-CNT
  (list 'r-cnt
        (list* 'r-cnt-status (sis 'r-cnt-out 0 cnt-width))
        (si 'link cnt-width)
        (list* 'buf-act 'shift-act (sis 'r-cnt-in 0 cnt-width)))

  ;; W-DATA
  (list 'w-data
        (list* 'w-data-status (sis 'w-data-out 0 data-width))
        (si 'link data-width)
        (list* 'shift-act 'buf-act (sis 'w-data-in 0 data-width)))

  ;; W-CNT
  (list 'w-cnt
        (list* 'w-cnt-status (sis 'w-cnt-out 0 cnt-width))
        (si 'link cnt-width)
        (list* 'shift-act 'buf-act (sis 'w-cnt-in 0 cnt-width)))

  '(g0 (low) vss ())
  '(g1 (high) vdd ())

  ;; JOINTS
  ;; Shift
  (list 'r-cnt=0?
        '(r-cnt=0)
        (si 'fast-zero cnt-width)
        (sis 'r-cnt-out 0 cnt-width))
  '(s0 (r-cnt=0~) b-not (r-cnt=0))
  '(s1 (shift-full-in) b-and4 (r-data-status r-cnt-status r-cnt=0 full-in))
  '(s2 (r-full) b-and3 (r-data-status r-cnt-status r-cnt=0~))
  '(s3 (w-empty-) b-or (w-data-status w-cnt-status))
  '(s4 (shift-empty-out-) b-or3 (w-data-status w-cnt-status empty-out-))

  (list 'in-cntl
        '(in-act)
        'joint-cntl
        (list 'shift-full-in 'w-empty- (si 'go 0)))
  (list 'shift-reg-op0
        (sis 'w-data-in0 0 data-width)
        (si 'v-buf data-width)
        (sis 'data-in 0 data-width))
  (list 'shift-cnt-op0
        (sis 'w-cnt-in0 0 cnt-width)
        (si 'v-buf cnt-width)
        (append (make-list (1- cnt-width) :initial-element 'low)
                '(high)))

  (list 'out-cntl
        '(out-act)
        'joint-cntl
        (list 'r-full 'shift-empty-out- (si 'go 0)))
  (list 'shift-reg-op1
        (sis 'w-data-in1 0 data-width)
        (si 'v-buf data-width)
        (append (sis 'r-data-out 1 (1- data-width))
                '(low)))
  (list 'shift-cnt-op1
        (sis 'w-cnt-in1 0 cnt-width)
        (si 'counter cnt-width)
        (sis 'r-cnt-out 0 cnt-width))

  '(shift-cntl (shift-act) b-or (in-act out-act))
  (list 'shift-reg-op
        (sis 'w-data-in 0 data-width)
        (si 'tv-if (tree-number (make-tree data-width)))
        (cons 'r-cnt=0
              (append (sis 'w-data-in0 0 data-width)
                      (sis 'w-data-in1 0 data-width))))
  (list 'shift-cnt-op
        (sis 'w-cnt-in 0 cnt-width)
        (si 'tv-if (tree-number (make-tree cnt-width)))
        (cons 'r-cnt=0
              (append (sis 'w-cnt-in0 0 cnt-width)
                      (sis 'w-cnt-in1 0 cnt-width))))

  ;; Buffer
  '(b0 (buf-full-in) b-and (w-data-status w-cnt-status))
  '(b1 (buf-empty-out-) b-or (r-data-status r-cnt-status))
  (list 'buf-cntl
        '(buf-act)
        'joint-cntl
        (list 'buf-full-in 'buf-empty-out- (si 'go 1)))
  (list 'buf-reg-op
        (sis 'r-data-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'w-data-out 0 data-width))
  (list 'buf-cnt-op
        (sis 'r-cnt-in 0 cnt-width)
        (si 'v-buf cnt-width)
        (sis 'w-cnt-out 0 cnt-width))

  ;; OUTPUTS
  (list 'out '(bit-out) 'wire (sis 'r-data-out 0 1)))

 (declare (xargs :guard (and (posp data-width) (posp cnt-width)))))

(make-event
 `(progn
    ,@(state-accessors-gen 'piso-sreg
                           '(r-data r-cnt w-data w-cnt)
                           0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; PISO-SREG.

(defund piso-sreg$netlist (data-width cnt-width)
  (declare (xargs :guard (and (posp data-width)
                              (natp cnt-width)
                              (<= 2 cnt-width))))
  (cons (piso-sreg* data-width cnt-width)
        (union$ (link$netlist data-width)
                (link$netlist cnt-width)
                *joint-cntl*
                (fast-zero$netlist cnt-width)
                (counter$netlist cnt-width)
                (v-buf$netlist data-width)
                (v-buf$netlist cnt-width)
                (tv-if$netlist (make-tree data-width))
                (tv-if$netlist (make-tree cnt-width))
                :test 'equal)))

;; Recognizer for PISO-SREG

(defund piso-sreg& (netlist data-width cnt-width)
  (declare (xargs :guard (and (alistp netlist)
                              (posp data-width)
                              (natp cnt-width)
                              (<= 2 cnt-width))))
  (b* ((subnetlist (delete-to-eq (si 'piso-sreg data-width)
                                 netlist)))
    (and (equal (assoc (si 'piso-sreg data-width) netlist)
                (piso-sreg* data-width cnt-width))
         (link& subnetlist data-width)
         (link& subnetlist cnt-width)
         (joint-cntl& subnetlist)
         (fast-zero& subnetlist cnt-width)
         (counter& subnetlist cnt-width)
         (v-buf& subnetlist data-width)
         (v-buf& subnetlist cnt-width)
         (tv-if& subnetlist (make-tree data-width))
         (tv-if& subnetlist (make-tree cnt-width)))))

;; Sanity check

(local
 (defthmd check-piso-sreg$netlist-64-7
   (and (net-syntax-okp (piso-sreg$netlist 64 7))
        (net-arity-okp (piso-sreg$netlist 64 7))
        (piso-sreg& (piso-sreg$netlist 64 7) 64 7))))

;; Constraints on the state of PISO-SREG

(defund piso-sreg$st-format (st data-width cnt-width)
  (b* ((r-data (get-field *piso-sreg$r-data* st))
       (r-cnt (get-field *piso-sreg$r-cnt* st))
       (w-data (get-field *piso-sreg$w-data* st))
       (w-cnt (get-field *piso-sreg$w-cnt* st)))
    (and (posp data-width)
         (natp cnt-width)
         (<= 3 cnt-width)
         (link$st-format r-data data-width)
         (link$st-format r-cnt cnt-width)
         (link$st-format w-data data-width)
         (link$st-format w-cnt cnt-width))))

(defthm piso-sreg$st-format=>constraint
  (implies (piso-sreg$st-format st data-width cnt-width)
           (and (posp data-width)
                (natp cnt-width)
                (<= 3 cnt-width)))
  :hints (("Goal" :in-theory (enable piso-sreg$st-format)))
  :rule-classes :forward-chaining)

(defund piso-sreg$valid-st (st data-width cnt-width)
  (b* ((r-data (get-field *piso-sreg$r-data* st))
       (r-cnt (get-field *piso-sreg$r-cnt* st))
       (w-data (get-field *piso-sreg$w-data* st))
       (w-cnt (get-field *piso-sreg$w-cnt* st)))
    (and (piso-sreg$st-format st data-width cnt-width)
         (equal data-width (expt 2 (1- cnt-width)))
         (link$valid-st r-data data-width)
         (link$valid-st r-cnt cnt-width)
         (link$valid-st w-data data-width)
         (link$valid-st w-cnt cnt-width))))

(local
 (defthm expt-linear-lower-<=-instance
   (implies (and (<= 2 n)
                 (integerp n))
            (<= 4 (expt 2 n)))
   :rule-classes :linear))

(defthmd piso-sreg$valid-st=>constraint
  (implies (piso-sreg$valid-st st data-width cnt-width)
           (and (natp data-width)
                (<= 4 data-width)
                (natp cnt-width)
                (<= 3 cnt-width)))
  :hints (("Goal" :in-theory (enable piso-sreg$valid-st)))
  :rule-classes :forward-chaining)

(defthmd piso-sreg$valid-st=>st-format
  (implies (piso-sreg$valid-st st data-width cnt-width)
           (piso-sreg$st-format st data-width cnt-width))
  :hints (("Goal" :in-theory (enable piso-sreg$valid-st))))

;; Extract the input and output signals for PISO-SREG

(progn
  ;; Extract the input data

  (defun piso-sreg$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 2 inputs)))

  (defthm len-piso-sreg$data-in
    (equal (len (piso-sreg$data-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable piso-sreg$data-in))

  ;; Extract the "in-act" signal

  (defund piso-sreg$in-act (inputs st data-width)
    (b* ((full-in (nth 0 inputs))
         (go-signals (nthcdr (piso-sreg$data-ins-len data-width)
                             inputs))
         (go-shift (nth 0 go-signals))

         (r-data (get-field *piso-sreg$r-data* st))
         (r-data.s (get-field *link$s* r-data))
         (r-cnt (get-field *piso-sreg$r-cnt* st))
         (r-cnt.s (get-field *link$s* r-cnt))
         (r-cnt.d (get-field *link$d* r-cnt))
         (w-data (get-field *piso-sreg$w-data* st))
         (w-data.s (get-field *link$s* w-data))
         (w-cnt (get-field *piso-sreg$w-cnt* st))
         (w-cnt.s (get-field *link$s* w-cnt))

         (r-cnt=0 (f$fast-zero (strip-cars r-cnt.d)))
         (shift-full-in (f-and4 (car r-data.s) (car r-cnt.s)
                                r-cnt=0 full-in))
         (w-empty- (f-or (car w-data.s) (car w-cnt.s))))
      (joint-act shift-full-in w-empty- go-shift)))

  (defthm piso-sreg$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (piso-sreg$in-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable f-and4
                                       piso-sreg$in-act))))

  ;; Extract the "out-act" signal

  (defund piso-sreg$out-act (inputs st data-width)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (piso-sreg$data-ins-len data-width)
                             inputs))
         (go-shift (nth 0 go-signals))

         (r-data (get-field *piso-sreg$r-data* st))
         (r-data.s (get-field *link$s* r-data))
         (r-cnt (get-field *piso-sreg$r-cnt* st))
         (r-cnt.s (get-field *link$s* r-cnt))
         (r-cnt.d (get-field *link$d* r-cnt))
         (w-data (get-field *piso-sreg$w-data* st))
         (w-data.s (get-field *link$s* w-data))
         (w-cnt (get-field *piso-sreg$w-cnt* st))
         (w-cnt.s (get-field *link$s* w-cnt))

         (r-cnt=0~ (f-not (f$fast-zero (strip-cars r-cnt.d))))
         (r-full (f-and3 (car r-data.s) (car r-cnt.s) r-cnt=0~))
         (shift-empty-out- (f-or3 (car w-data.s) (car w-cnt.s) empty-out-)))
      (joint-act r-full shift-empty-out- go-shift)))

  (defthm piso-sreg$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (piso-sreg$out-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable f-or3
                                       piso-sreg$out-act))))

  (defthm piso-sreg$in-out-acts-mutually-exclusive
    (implies (and (piso-sreg$valid-st st data-width cnt-width)
                  (piso-sreg$in-act inputs st data-width))
             (not (piso-sreg$out-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable f-and4
                                       piso-sreg$valid-st
                                       piso-sreg$in-act
                                       piso-sreg$out-act))))

  ;; Extract the output data

  (defund piso-sreg$bit-out (st)
    (b* ((r-data (get-field *piso-sreg$r-data* st))
         (r-data.d (get-field *link$d* r-data)))
      (f-buf (car (strip-cars r-data.d)))))

  (defthm booleanp-piso-sreg$bit-out
    (implies (and (piso-sreg$valid-st st data-width cnt-width)
                  (piso-sreg$out-act inputs st data-width))
             (booleanp (piso-sreg$bit-out st)))
    :hints (("Goal" :in-theory (enable f-and3
                                       f-buf
                                       piso-sreg$valid-st
                                       piso-sreg$out-act
                                       piso-sreg$bit-out)))
    :rule-classes (:rewrite :type-prescription))

  (defun piso-sreg$outputs (inputs st data-width)
    (list (piso-sreg$in-act inputs st data-width)
          (piso-sreg$out-act inputs st data-width)
          (piso-sreg$bit-out st)))
  )

;; The value lemma for PISO-SREG

(defthm piso-sreg$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (piso-sreg& netlist data-width cnt-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *piso-sreg$go-num*)
                  (piso-sreg$st-format st data-width cnt-width))
             (equal (se (si 'piso-sreg data-width) inputs st netlist)
                    (piso-sreg$outputs inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'piso-sreg data-width)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            piso-sreg&
                            piso-sreg*$destructure
                            piso-sreg$data-in
                            piso-sreg$st-format
                            piso-sreg$in-act
                            piso-sreg$out-act
                            piso-sreg$bit-out)
                           (car-cdr-elim
                            de-module-disabled-rules)))))

;; This function specifies the next state of PISO-SREG.

(defun piso-sreg$step (inputs st data-width cnt-width)
  (b* ((data-in    (piso-sreg$data-in inputs data-width))
       (go-signals (nthcdr (piso-sreg$data-ins-len data-width)
                           inputs))
       (go-buf   (nth 1 go-signals))

       (r-data (get-field *piso-sreg$r-data* st))
       (r-data.s (get-field *link$s* r-data))
       (r-data.d (get-field *link$d* r-data))
       (r-cnt (get-field *piso-sreg$r-cnt* st))
       (r-cnt.s (get-field *link$s* r-cnt))
       (r-cnt.d (get-field *link$d* r-cnt))
       (w-data (get-field *piso-sreg$w-data* st))
       (w-data.s (get-field *link$s* w-data))
       (w-data.d (get-field *link$d* w-data))
       (w-cnt (get-field *piso-sreg$w-cnt* st))
       (w-cnt.s (get-field *link$s* w-cnt))
       (w-cnt.d (get-field *link$d* w-cnt))

       (r-cnt=0 (f$fast-zero (strip-cars r-cnt.d)))
       (in-act (piso-sreg$in-act inputs st data-width))
       (out-act (piso-sreg$out-act inputs st data-width))
       (shift-act (f-or in-act out-act))

       (buf-full-in (f-and (car w-data.s) (car w-cnt.s)))
       (buf-empty-out- (f-or (car r-data.s) (car r-cnt.s)))
       (buf-act (joint-act buf-full-in buf-empty-out- go-buf))

       (r-data-inputs (list* buf-act shift-act (strip-cars w-data.d)))
       (r-cnt-inputs (list* buf-act shift-act (strip-cars w-cnt.d)))
       (w-data-inputs (list* shift-act buf-act
                            (fv-if r-cnt=0
                                   data-in
                                   (append (nthcdr 1 (v-threefix
                                                      (strip-cars r-data.d)))
                                           '(nil)))))
       (w-cnt-inputs
        (list* shift-act buf-act
               (fv-if r-cnt=0
                      (append (make-list (1- cnt-width))
                              '(t))
                      (take cnt-width
                            (fv-adder
                             t
                             (strip-cars r-cnt.d)
                             (fv-not
                              (cons t (make-list (1- cnt-width))))))))))
    (list
     ;; R-DATA
     (link$step r-data-inputs r-data data-width)
     ;; R-CNT
     (link$step r-cnt-inputs r-cnt cnt-width)
     ;; W-DATA
     (link$step w-data-inputs w-data data-width)
     ;; W-CNT
     (link$step w-cnt-inputs w-cnt cnt-width))))

(defthm len-of-piso-sreg$step
  (equal (len (piso-sreg$step inputs st data-width cnt-width))
         *piso-sreg$st-len*))

(local
 (defthm len-cdr
   (implies (< 0 (len x))
            (equal (len (cdr x))
                   (1- (len x))))))

;; The state lemma for PISO-SREG

(defthm piso-sreg$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies
     (and (piso-sreg& netlist data-width cnt-width)
          (true-listp data-in)
          (equal (len data-in) data-width)
          (true-listp go-signals)
          (equal (len go-signals) *piso-sreg$go-num*)
          (piso-sreg$st-format st data-width cnt-width))
     (equal (de (si 'piso-sreg data-width) inputs st netlist)
            (piso-sreg$step inputs st data-width cnt-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'piso-sreg data-width)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            piso-sreg&
                            piso-sreg*$destructure
                            piso-sreg$data-in
                            piso-sreg$in-act
                            piso-sreg$out-act
                            piso-sreg$st-format)
                           (append-v-threefix
                            associativity-of-append
                            de-module-disabled-rules)))))

(in-theory (disable piso-sreg$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund piso-sreg$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (piso-sreg$data-in inputs data-width))
       (go-signals (nthcdr (piso-sreg$data-ins-len data-width) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *piso-sreg$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(defthm booleanp-piso-sreg$in-act
  (implies (and (piso-sreg$input-format inputs data-width)
                (piso-sreg$valid-st st data-width cnt-width))
           (booleanp (piso-sreg$in-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (e/d (f-and4
                            piso-sreg$input-format
                            piso-sreg$valid-st
                            piso-sreg$in-act)
                           ())))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-piso-sreg$out-act
  (implies (and (piso-sreg$input-format inputs data-width)
                (piso-sreg$valid-st st data-width cnt-width))
           (booleanp (piso-sreg$out-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (e/d (f-and3
                            piso-sreg$input-format
                            piso-sreg$valid-st
                            piso-sreg$out-act)
                           ())))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma piso-sreg :sizes (data-width cnt-width))

;; ======================================================================

;; 3. Single-Step-Update Property

;; Specify the functionality of PISO-SREG

(defun piso-sreg$op (x)
  (rev x))

(defthm append-of-piso-sreg$op-with-singleton
  (equal (append (piso-sreg$op x) (list a))
         (piso-sreg$op (cons a x))))

(in-theory (disable piso-sreg$op))

;; The operation of PISO-SREG over a data sequence

(defun piso-sreg$op-map (x)
  (if (atom x)
      nil
    (append (piso-sreg$op (car x))
            (piso-sreg$op-map (cdr x)))))

(defthm piso-sreg$op-map-of-append
  (equal (piso-sreg$op-map (append x y))
         (append (piso-sreg$op-map x)
                 (piso-sreg$op-map y))))

;; The extraction function for PISO-SREG

(defund piso-sreg$extract (st)
  (b* ((r-data (get-field *piso-sreg$r-data* st))
       (r-data.s (get-field *link$s* r-data))
       (r-data.d (get-field *link$d* r-data))
       (r-cnt (get-field *piso-sreg$r-cnt* st))
       (r-cnt.d (get-field *link$d* r-cnt))
       (w-data (get-field *piso-sreg$w-data* st))
       (w-data.d (get-field *link$d* w-data))
       (w-cnt (get-field *piso-sreg$w-cnt* st))
       (w-cnt.d (get-field *link$d* w-cnt)))
    (if (fullp r-data.s)
        (take (v-to-nat (strip-cars r-cnt.d))
              (strip-cars r-data.d))
      (take (v-to-nat (strip-cars w-cnt.d))
            (strip-cars w-data.d)))))

(local
 (defthm v-to-nat-of-v-zp
   (equal (v-zp x)
          (equal (v-to-nat x) 0))
   :hints (("Goal" :in-theory (enable v-zp v-nzp v-to-nat)))))

(defthm piso-sreg$extract-not-empty
  (implies (and (piso-sreg$out-act inputs st data-width)
                (piso-sreg$valid-st st data-width cnt-width))
           (< 0 (len (piso-sreg$extract st))))
  :hints (("Goal"
           :in-theory (e/d (f-and3
                            f-or3
                            piso-sreg$valid-st
                            piso-sreg$extract
                            piso-sreg$out-act)
                           ())))
  :rule-classes :linear)

(defthmd len-of-piso-sreg$extract-lemma
  (implies (and (piso-sreg$in-act inputs st data-width)
                (piso-sreg$valid-st st data-width cnt-width))
           (equal (len (piso-sreg$extract st))
                  0))
  :hints (("Goal" :in-theory (e/d (f-and4
                                   piso-sreg$valid-st
                                   piso-sreg$in-act
                                   piso-sreg$extract)
                                  ()))))

(defthm len-of-piso-sreg$extract-contrapositive-lemma-1
  (implies (and (piso-sreg$in-act inputs st data-width)
                (< 0 (len (piso-sreg$extract st))))
                (not (piso-sreg$valid-st st data-width cnt-width)))
  :hints (("Goal" :in-theory (e/d (f-and4
                                   piso-sreg$valid-st
                                   piso-sreg$in-act
                                   piso-sreg$extract)
                                  ()))))

(defthm len-of-piso-sreg$extract-contrapositive-lemma-2
  (implies (and (piso-sreg$valid-st st data-width cnt-width)
                (< 0 (len (piso-sreg$extract st))))
                (not (piso-sreg$in-act inputs st data-width)))
  :hints (("Goal" :in-theory (e/d (f-and4
                                   piso-sreg$valid-st
                                   piso-sreg$in-act
                                   piso-sreg$extract)
                                  ()))))

;; Specify and prove a state invariant

(progn
  (defund piso-sreg$inv (st)
    (b* ((r-data (get-field *piso-sreg$r-data* st))
         (r-data.s (get-field *link$s* r-data))
         (r-data.d (get-field *link$d* r-data))
         (r-cnt (get-field *piso-sreg$r-cnt* st))
         (r-cnt.s (get-field *link$s* r-cnt))
         (r-cnt.d (get-field *link$d* r-cnt))
         (w-data (get-field *piso-sreg$w-data* st))
         (w-data.s (get-field *link$s* w-data))
         (w-data.d (get-field *link$d* w-data))
         (w-cnt (get-field *piso-sreg$w-cnt* st))
         (w-cnt.s (get-field *link$s* w-cnt))
         (w-cnt.d (get-field *link$d* w-cnt)))
      (and (equal r-data.s r-cnt.s)
           (equal w-data.s w-cnt.s)
           (not (equal r-data.s w-data.s))

           (or (emptyp r-cnt.s)
               (<= (v-to-nat (strip-cars r-cnt.d))
                   (len r-data.d)))
           (or (emptyp w-cnt.s)
               (<= (v-to-nat (strip-cars w-cnt.d))
                   (len w-data.d))))))

  (local
   (defthm piso-sreg$input-format-lemma-1
     (implies (piso-sreg$input-format inputs data-width)
              (booleanp (nth 0 inputs)))
     :hints (("Goal" :in-theory (enable piso-sreg$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm piso-sreg$input-format-lemma-2
     (implies (piso-sreg$input-format inputs data-width)
              (booleanp (nth 1 inputs)))
     :hints (("Goal" :in-theory (enable piso-sreg$input-format)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm piso-sreg$input-format-lemma-3
     (implies (and (piso-sreg$input-format inputs data-width)
                   (nth 0 inputs))
              (bvp (piso-sreg$data-in inputs data-width)))
     :hints (("Goal" :in-theory (enable piso-sreg$input-format)))))

  (defthm len-of-piso-sreg$extract-upper-bound
    (implies (and (piso-sreg$valid-st st data-width cnt-width)
                  (piso-sreg$inv st))
             (<= (len (piso-sreg$extract st))
                 data-width))
    :hints (("Goal" :in-theory (e/d (piso-sreg$valid-st
                                     piso-sreg$inv
                                     piso-sreg$extract)
                                    ())))
    :rule-classes :linear)

  (local
   (defthm v-to-nat-of-repeat-lemma
     (equal (v-to-nat (append (repeat n nil) '(t)))
            (expt 2 (nfix n)))
     :hints (("Goal" :in-theory (enable v-to-nat repeat)))))

  (defthm piso-sreg$inv-preserved
    (implies (and (piso-sreg$input-format inputs data-width)
                  (piso-sreg$valid-st st data-width cnt-width)
                  (piso-sreg$inv st))
             (piso-sreg$inv
              (piso-sreg$step inputs st data-width cnt-width)))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              bvp
                              piso-sreg$valid-st
                              piso-sreg$inv
                              piso-sreg$step
                              piso-sreg$in-act
                              piso-sreg$out-act)
                             ()))))
  )

;; The extracted next-state function for PISO-SREG.  Note that this
;; function avoids exploring the internal computation of PISO-SREG.

(defund piso-sreg$extracted-step (inputs st data-width)
  (b* ((data (piso-sreg$data-in inputs data-width))
       (extracted-st (piso-sreg$extract st)))
    (cond
     ((equal (piso-sreg$out-act inputs st data-width) t)
      (cdr extracted-st))
     ((equal (piso-sreg$in-act inputs st data-width) t)
      data)
     (t extracted-st))))

;; The single-step-update property

(defthm piso-sreg$extracted-step-correct
  (b* ((next-st (piso-sreg$step inputs st data-width cnt-width)))
    (implies (and (piso-sreg$input-format inputs data-width)
                  (piso-sreg$valid-st st data-width cnt-width)
                  (piso-sreg$inv st))
             (equal (piso-sreg$extract next-st)
                    (piso-sreg$extracted-step inputs st data-width))))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            f-sr
                            joint-act
                            bvp
                            pos-len=>cons
                            piso-sreg$extracted-step
                            piso-sreg$valid-st
                            piso-sreg$inv
                            piso-sreg$step
                            piso-sreg$in-act
                            piso-sreg$out-act
                            piso-sreg$extract)
                           ()))))

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that piso-sreg$valid-st is an invariant.

(defthm piso-sreg$valid-st-preserved
  (implies (and (piso-sreg$input-format inputs data-width)
                (piso-sreg$valid-st st data-width cnt-width))
           (piso-sreg$valid-st
            (piso-sreg$step inputs st data-width cnt-width)
            data-width
            cnt-width))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            f-sr
                            joint-act
                            bvp
                            f-and3
                            f-and4
                            pos-len=>cons
                            piso-sreg$st-format
                            piso-sreg$valid-st
                            piso-sreg$step
                            piso-sreg$in-act
                            piso-sreg$out-act)
                           (if*
                            v-threefix)))))

(defthm piso-sreg$extract-lemma
  (implies (and (piso-sreg$out-act inputs st data-width)
                (piso-sreg$valid-st st data-width cnt-width))
           (equal (piso-sreg$bit-out st)
                  (car (piso-sreg$extract st))))
  :hints (("Goal" :in-theory (e/d (f-and3
                                   booleanp-car-of-bv
                                   piso-sreg$out-act
                                   piso-sreg$valid-st
                                   piso-sreg$bit-out
                                   piso-sreg$extract)
                                  ()))))

(defthm booleanp-car-of-piso-sreg$extract
  (implies (and (piso-sreg$out-act inputs st data-width)
                (piso-sreg$valid-st st data-width cnt-width))
           (booleanp (car (piso-sreg$extract st))))
  :hints (("Goal"
           :use piso-sreg$extract-lemma
           :in-theory (e/d ()
                           (piso-sreg$extract-lemma))))
  :rule-classes (:rewrite :type-prescription))

;; Extract the accepted input sequence

(seq-gen piso-sreg in in-act 0
         (piso-sreg$data-in inputs data-width)
         :sizes (data-width cnt-width))

;; Extract the valid output sequence

(seq-gen piso-sreg out out-act 1
         (piso-sreg$bit-out st)
         :netlist-data (nth 2 outputs)
         :sizes (data-width cnt-width))

;; The multi-step input-output relationship

(encapsulate
  ()

  (local
   (defthm piso-sreg$op-of-len-0
     (implies (equal (len x) 0)
              (not (piso-sreg$op x)))
     :hints (("Goal" :in-theory (enable piso-sreg$op)))))

  (local
   (defthm piso-sreg$dataflow-correct-aux
     (implies (equal (append x y1)
                     (append (piso-sreg$op-map seq) y2))
              (equal (append x y1 z)
                     (append (piso-sreg$op-map seq)
                             y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (associativity-of-append))))))

  (defthmd piso-sreg$dataflow-correct
    (b* ((extracted-st (piso-sreg$extract st))
         (final-st (piso-sreg$run
                    inputs-seq st data-width cnt-width n))
         (final-extracted-st (piso-sreg$extract final-st)))
      (implies
       (and (piso-sreg$input-format-n inputs-seq data-width n)
            (piso-sreg$valid-st st data-width cnt-width)
            (piso-sreg$inv st))
       (equal (append (piso-sreg$op final-extracted-st)
                      (piso-sreg$out-seq
                       inputs-seq st data-width cnt-width n))
              (append (piso-sreg$op-map
                       (piso-sreg$in-seq
                        inputs-seq st data-width cnt-width n))
                      (piso-sreg$op extracted-st)))))
    :hints (("Goal"
             :in-theory (enable pos-len=>cons
                                len-of-piso-sreg$extract-lemma
                                piso-sreg$extracted-step))))

  (defthmd piso-sreg$functionally-correct
    (b* ((extracted-st (piso-sreg$extract st))
         (final-st (de-n (si 'piso-sreg data-width)
                         inputs-seq st netlist n))
         (final-extracted-st (piso-sreg$extract final-st)))
      (implies
       (and (piso-sreg& netlist data-width cnt-width)
            (piso-sreg$input-format-n inputs-seq data-width n)
            (piso-sreg$valid-st st data-width cnt-width)
            (piso-sreg$inv st))
       (equal (append (piso-sreg$op final-extracted-st)
                      (piso-sreg$netlist-out-seq
                       inputs-seq st netlist data-width n))
              (append (piso-sreg$op-map
                       (piso-sreg$netlist-in-seq
                        inputs-seq st netlist data-width n))
                      (piso-sreg$op extracted-st)))))
    :hints (("Goal"
             :use piso-sreg$dataflow-correct
             :in-theory (enable piso-sreg$valid-st=>st-format
                                piso-sreg$de-n))))
  )

