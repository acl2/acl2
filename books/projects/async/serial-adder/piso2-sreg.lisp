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

(local (include-book "../list-rewrites"))

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

(local
 (deftheory piso2-sreg$disabled-rules
   '(if*
     not
     default-car
     default-cdr
     strip-cars
     v-threefix
     append
     append-v-threefix
     associativity-of-append
     acl2::default-expt-2)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of PISO2-SREG
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of PISO2-SREG
;;
;; Construct a DE module generator for circuits consisting of two PISO shift
;; registers that share the same communication signal at their input ports.
;; Prove the value and state lemmas for this module generator.

(defconst *piso2-sreg$go-num* 5)
(defconst *piso2-sreg$st-len* 8)

(defun piso2-sreg$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 3 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun piso2-sreg$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (piso2-sreg$data-ins-len data-width)
     *piso2-sreg$go-num*))

;; DE module generator of PISO2-SREG

(module-generator
 piso2-sreg* (data-width cnt-width)
 (si 'piso2-sreg data-width)
 (list* 'full-in 'empty-out0- 'empty-out1-
        (append (sis 'data0-in 0 data-width)
                (sis 'data1-in 0 data-width)
                (sis 'go 0 *piso2-sreg$go-num*)))
 '(in-act out0-act out1-act bit0-out bit1-out)
 '(r-data0 r-cnt0 w-data0 w-cnt0 r-data1 r-cnt1 w-data1 w-cnt1)
 (list
  ;; LINKS
  ;; R-DATA0
  (list 'r-data0
        (list* 'r-data0-status (sis 'r-data0-out 0 data-width))
        (si 'link data-width)
        (list* 'buf0-act 'shift0-act (sis 'r-data0-in 0 data-width)))

  ;; R-CNT0
  (list 'r-cnt0
        (list* 'r-cnt0-status (sis 'r-cnt0-out 0 cnt-width))
        (si 'link cnt-width)
        (list* 'buf0-act 'shift0-act (sis 'r-cnt0-in 0 cnt-width)))

  ;; W-DATA0
  (list 'w-data0
        (list* 'w-data0-status (sis 'w-data0-out 0 data-width))
        (si 'link data-width)
        (list* 'shift0-act 'buf0-act (sis 'w-data0-in 0 data-width)))

  ;; W-CNT0
  (list 'w-cnt0
        (list* 'w-cnt0-status (sis 'w-cnt0-out 0 cnt-width))
        (si 'link cnt-width)
        (list* 'shift0-act 'buf0-act (sis 'w-cnt0-in 0 cnt-width)))

  ;; R-DATA1
  (list 'r-data1
        (list* 'r-data1-status (sis 'r-data1-out 0 data-width))
        (si 'link data-width)
        (list* 'buf1-act 'shift1-act (sis 'r-data1-in 0 data-width)))

  ;; R-CNT1
  (list 'r-cnt1
        (list* 'r-cnt1-status (sis 'r-cnt1-out 0 cnt-width))
        (si 'link cnt-width)
        (list* 'buf1-act 'shift1-act (sis 'r-cnt1-in 0 cnt-width)))

  ;; W-DATA1
  (list 'w-data1
        (list* 'w-data1-status (sis 'w-data1-out 0 data-width))
        (si 'link data-width)
        (list* 'shift1-act 'buf1-act (sis 'w-data1-in 0 data-width)))

  ;; W-CNT1
  (list 'w-cnt1
        (list* 'w-cnt1-status (sis 'w-cnt1-out 0 cnt-width))
        (si 'link cnt-width)
        (list* 'shift1-act 'buf1-act (sis 'w-cnt1-in 0 cnt-width)))

  '(g0 (low) vss ())
  '(g1 (high) vdd ())

  ;; JOINTS
  ;; Shift
  (list 'r-cnt0=0?
        '(r-cnt0=0)
        (si 'fast-zero cnt-width)
        (sis 'r-cnt0-out 0 cnt-width))
  '(s0 (r-cnt0=0~) b-not (r-cnt0=0))
  '(s1 (r0-ready-in) b-and3 (r-data0-status r-cnt0-status r-cnt0=0))
  '(s2 (r0-full) b-and3 (r-data0-status r-cnt0-status r-cnt0=0~))
  '(s3 (w0-empty-) b-or (w-data0-status w-cnt0-status))
  '(s4 (shift-empty-out0-) b-or (empty-out0- w0-empty-))

  (list 'r-cnt1=0?
        '(r-cnt1=0)
        (si 'fast-zero cnt-width)
        (sis 'r-cnt1-out 0 cnt-width))
  '(s5 (r-cnt1=0~) b-not (r-cnt1=0))
  '(s6 (r1-ready-in) b-and3 (r-data1-status r-cnt1-status r-cnt1=0))
  '(s7 (r1-full) b-and3 (r-data1-status r-cnt1-status r-cnt1=0~))
  '(s8 (w1-empty-) b-or (w-data1-status w-cnt1-status))
  '(s9 (shift-empty-out1-) b-or (empty-out1- w1-empty-))

  '(s10 (shift-full-in) b-and3 (full-in r0-ready-in r1-ready-in))
  '(s11 (w0+1-empty-) b-or (w0-empty- w1-empty-))
  (list 'in-cntl
        '(in-act)
        'joint-cntl
        (list 'shift-full-in 'w0+1-empty- (si 'go 0)))
  (list 'shift-reg0-op0
        (sis 'w-data0-in0 0 data-width)
        (si 'v-buf data-width)
        (sis 'data0-in 0 data-width))
  (list 'shift-cnt0-op0
        (sis 'w-cnt0-in0 0 cnt-width)
        (si 'v-buf cnt-width)
        (append (make-list (1- cnt-width) :initial-element 'low)
                '(high)))
  (list 'shift-reg1-op0
        (sis 'w-data1-in0 0 data-width)
        (si 'v-buf data-width)
        (sis 'data1-in 0 data-width))
  (list 'shift-cnt1-op0
        (sis 'w-cnt1-in0 0 cnt-width)
        (si 'v-buf cnt-width)
        (append (make-list (1- cnt-width) :initial-element 'low)
                '(high)))

  (list 'out0-cntl
        '(out0-act)
        'joint-cntl
        (list 'r0-full 'shift-empty-out0- (si 'go 1)))
  (list 'shift-reg0-op1
        (sis 'w-data0-in1 0 data-width)
        (si 'v-buf data-width)
        (append (sis 'r-data0-out 1 (1- data-width))
                '(low)))
  (list 'shift-cnt0-op1
        (sis 'w-cnt0-in1 0 cnt-width)
        (si 'counter cnt-width)
        (sis 'r-cnt0-out 0 cnt-width))
  '(shift0-cntl (shift0-act) b-or (in-act out0-act))
  (list 'shift-reg0-op
        (sis 'w-data0-in 0 data-width)
        (si 'tv-if (tree-number (make-tree data-width)))
        (cons 'r-cnt0=0
              (append (sis 'w-data0-in0 0 data-width)
                      (sis 'w-data0-in1 0 data-width))))
  (list 'shift-cnt0-op
        (sis 'w-cnt0-in 0 cnt-width)
        (si 'tv-if (tree-number (make-tree cnt-width)))
        (cons 'r-cnt0=0
              (append (sis 'w-cnt0-in0 0 cnt-width)
                      (sis 'w-cnt0-in1 0 cnt-width))))

  (list 'out1-cntl
        '(out1-act)
        'joint-cntl
        (list 'r1-full 'shift-empty-out1- (si 'go 2)))
  (list 'shift-reg1-op1
        (sis 'w-data1-in1 0 data-width)
        (si 'v-buf data-width)
        (append (sis 'r-data1-out 1 (1- data-width))
                '(low)))
  (list 'shift-cnt1-op1
        (sis 'w-cnt1-in1 0 cnt-width)
        (si 'counter cnt-width)
        (sis 'r-cnt1-out 0 cnt-width))
  '(shift1-cntl (shift1-act) b-or (in-act out1-act))
  (list 'shift-reg1-op
        (sis 'w-data1-in 0 data-width)
        (si 'tv-if (tree-number (make-tree data-width)))
        (cons 'r-cnt1=0
              (append (sis 'w-data1-in0 0 data-width)
                      (sis 'w-data1-in1 0 data-width))))
  (list 'shift-cnt1-op
        (sis 'w-cnt1-in 0 cnt-width)
        (si 'tv-if (tree-number (make-tree cnt-width)))
        (cons 'r-cnt1=0
              (append (sis 'w-cnt1-in0 0 cnt-width)
                      (sis 'w-cnt1-in1 0 cnt-width))))

  ;; Buffer0
  '(b0 (buf0-full-in) b-and (w-data0-status w-cnt0-status))
  '(b1 (buf0-empty-out-) b-or (r-data0-status r-cnt0-status))
  (list 'buf0-cntl
        '(buf0-act)
        'joint-cntl
        (list 'buf0-full-in 'buf0-empty-out- (si 'go 3)))
  (list 'buf0-reg-op
        (sis 'r-data0-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'w-data0-out 0 data-width))
  (list 'buf0-cnt-op
        (sis 'r-cnt0-in 0 cnt-width)
        (si 'v-buf cnt-width)
        (sis 'w-cnt0-out 0 cnt-width))

  ;; Buffer1
  '(b2 (buf1-full-in) b-and (w-data1-status w-cnt1-status))
  '(b3 (buf1-empty-out-) b-or (r-data1-status r-cnt1-status))
  (list 'buf1-cntl
        '(buf1-act)
        'joint-cntl
        (list 'buf1-full-in 'buf1-empty-out- (si 'go 4)))
  (list 'buf1-reg-op
        (sis 'r-data1-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'w-data1-out 0 data-width))
  (list 'buf1-cnt-op
        (sis 'r-cnt1-in 0 cnt-width)
        (si 'v-buf cnt-width)
        (sis 'w-cnt1-out 0 cnt-width))

  ;; OUTPUTS
  (list 'out0 '(bit0-out) 'wire (sis 'r-data0-out 0 1))
  (list 'out1 '(bit1-out) 'wire (sis 'r-data1-out 0 1)))

 (declare (xargs :guard (and (posp data-width) (posp cnt-width)))))

(make-event
 `(progn
    ,@(state-accessors-gen 'piso2-sreg
                           '(r-data0 r-cnt0 w-data0 w-cnt0
                                    r-data1 r-cnt1 w-data1 w-cnt1)
                           0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; PISO2-SREG.

(defund piso2-sreg$netlist (data-width cnt-width)
  (declare (xargs :guard (and (posp data-width)
                              (natp cnt-width)
                              (<= 2 cnt-width))))
  (cons (piso2-sreg* data-width cnt-width)
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

;; Recognizer for PISO2-SREG

(defund piso2-sreg& (netlist data-width cnt-width)
  (declare (xargs :guard (and (alistp netlist)
                              (posp data-width)
                              (natp cnt-width)
                              (<= 2 cnt-width))))
  (b* ((subnetlist (delete-to-eq (si 'piso2-sreg data-width)
                                 netlist)))
    (and (equal (assoc (si 'piso2-sreg data-width) netlist)
                (piso2-sreg* data-width cnt-width))
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
 (defthmd check-piso2-sreg$netlist-64-7
   (and (net-syntax-okp (piso2-sreg$netlist 64 7))
        (net-arity-okp (piso2-sreg$netlist 64 7))
        (piso2-sreg& (piso2-sreg$netlist 64 7) 64 7))))

;; Constraints on the state of PISO2-SREG

(defund piso2-sreg$st-format (st data-width cnt-width)
  (b* ((r-data0 (get-field *piso2-sreg$r-data0* st))
       (r-cnt0 (get-field *piso2-sreg$r-cnt0* st))
       (w-data0 (get-field *piso2-sreg$w-data0* st))
       (w-cnt0 (get-field *piso2-sreg$w-cnt0* st))
       (r-data1 (get-field *piso2-sreg$r-data1* st))
       (r-cnt1 (get-field *piso2-sreg$r-cnt1* st))
       (w-data1 (get-field *piso2-sreg$w-data1* st))
       (w-cnt1 (get-field *piso2-sreg$w-cnt1* st)))
    (and (posp data-width)
         (natp cnt-width)
         (<= 3 cnt-width)
         (link$st-format r-data0 data-width)
         (link$st-format r-cnt0 cnt-width)
         (link$st-format w-data0 data-width)
         (link$st-format w-cnt0 cnt-width)
         (link$st-format r-data1 data-width)
         (link$st-format r-cnt1 cnt-width)
         (link$st-format w-data1 data-width)
         (link$st-format w-cnt1 cnt-width))))

(defthm piso2-sreg$st-format=>constraint
  (implies (piso2-sreg$st-format st data-width cnt-width)
           (and (posp data-width)
                (natp cnt-width)
                (<= 3 cnt-width)))
  :hints (("Goal" :in-theory (enable piso2-sreg$st-format)))
  :rule-classes :forward-chaining)

(defund piso2-sreg$valid-st (st data-width cnt-width)
  (b* ((r-data0 (get-field *piso2-sreg$r-data0* st))
       (r-cnt0 (get-field *piso2-sreg$r-cnt0* st))
       (w-data0 (get-field *piso2-sreg$w-data0* st))
       (w-cnt0 (get-field *piso2-sreg$w-cnt0* st))
       (r-data1 (get-field *piso2-sreg$r-data1* st))
       (r-cnt1 (get-field *piso2-sreg$r-cnt1* st))
       (w-data1 (get-field *piso2-sreg$w-data1* st))
       (w-cnt1 (get-field *piso2-sreg$w-cnt1* st)))
    (and (piso2-sreg$st-format st data-width cnt-width)
         (equal data-width (expt 2 (1- cnt-width)))
         (link$valid-st r-data0 data-width)
         (link$valid-st r-cnt0 cnt-width)
         (link$valid-st w-data0 data-width)
         (link$valid-st w-cnt0 cnt-width)
         (link$valid-st r-data1 data-width)
         (link$valid-st r-cnt1 cnt-width)
         (link$valid-st w-data1 data-width)
         (link$valid-st w-cnt1 cnt-width))))

(local
 (defthm expt-linear-lower-<=-instance
   (implies (and (<= 2 n)
                 (integerp n))
            (<= 4 (expt 2 n)))
   :rule-classes :linear))

(defthmd piso2-sreg$valid-st=>constraint
  (implies (piso2-sreg$valid-st st data-width cnt-width)
           (and (natp data-width)
                (<= 4 data-width)
                (natp cnt-width)
                (<= 3 cnt-width)))
  :hints (("Goal" :in-theory (e/d (piso2-sreg$valid-st)
                                  (piso2-sreg$disabled-rules))))
  :rule-classes :forward-chaining)

(defthmd piso2-sreg$valid-st=>st-format
  (implies (piso2-sreg$valid-st st data-width cnt-width)
           (piso2-sreg$st-format st data-width cnt-width))
  :hints (("Goal" :in-theory (enable piso2-sreg$valid-st))))

;; Extract the input and output signals for PISO2-SREG

(progn
  ;; Extract the input data

  (defun piso2-sreg$data0-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 3 inputs)))

  (defthm len-piso2-sreg$data0-in
    (equal (len (piso2-sreg$data0-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable piso2-sreg$data0-in))

  (defun piso2-sreg$data1-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (b* ((width (mbe :logic (nfix data-width)
                     :exec  data-width)))
      (take width
            (nthcdr (+ 3 width) inputs))))

  (defthm len-piso2-sreg$data1-in
    (equal (len (piso2-sreg$data1-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable piso2-sreg$data1-in))

  ;; Extract the "in-act" signal

  (defund piso2-sreg$in-act (inputs st data-width)
    (b* ((full-in (nth 0 inputs))
         (go-signals (nthcdr (piso2-sreg$data-ins-len data-width)
                             inputs))
         (go-in (nth 0 go-signals))

         (r-data0 (get-field *piso2-sreg$r-data0* st))
         (r-data0.s (get-field *link$s* r-data0))
         (r-cnt0 (get-field *piso2-sreg$r-cnt0* st))
         (r-cnt0.s (get-field *link$s* r-cnt0))
         (r-cnt0.d (get-field *link$d* r-cnt0))
         (w-data0 (get-field *piso2-sreg$w-data0* st))
         (w-data0.s (get-field *link$s* w-data0))
         (w-cnt0 (get-field *piso2-sreg$w-cnt0* st))
         (w-cnt0.s (get-field *link$s* w-cnt0))

         (r-data1 (get-field *piso2-sreg$r-data1* st))
         (r-data1.s (get-field *link$s* r-data1))
         (r-cnt1 (get-field *piso2-sreg$r-cnt1* st))
         (r-cnt1.s (get-field *link$s* r-cnt1))
         (r-cnt1.d (get-field *link$d* r-cnt1))
         (w-data1 (get-field *piso2-sreg$w-data1* st))
         (w-data1.s (get-field *link$s* w-data1))
         (w-cnt1 (get-field *piso2-sreg$w-cnt1* st))
         (w-cnt1.s (get-field *link$s* w-cnt1))

         (r-cnt0=0 (f$fast-zero (strip-cars r-cnt0.d)))
         (r0-ready-in (f-and3 (car r-data0.s) (car r-cnt0.s) r-cnt0=0))
         (w0-empty- (f-or (car w-data0.s) (car w-cnt0.s)))

         (r-cnt1=0 (f$fast-zero (strip-cars r-cnt1.d)))
         (r1-ready-in (f-and3 (car r-data1.s) (car r-cnt1.s) r-cnt1=0))
         (w1-empty- (f-or (car w-data1.s) (car w-cnt1.s)))

         (shift-full-in (f-and3 full-in r0-ready-in r1-ready-in))
         (w0+1-empty- (f-or w0-empty- w1-empty-)))
      (joint-act shift-full-in w0+1-empty- go-in)))

  (defthm piso2-sreg$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (piso2-sreg$in-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable f-and3
                                       piso2-sreg$in-act))))

  ;; Extract the "out0-act" signal

  (defund piso2-sreg$out0-act (inputs st data-width)
    (b* ((empty-out0- (nth 1 inputs))
         (go-signals (nthcdr (piso2-sreg$data-ins-len data-width)
                             inputs))
         (go-out0 (nth 1 go-signals))

         (r-data0 (get-field *piso2-sreg$r-data0* st))
         (r-data0.s (get-field *link$s* r-data0))
         (r-cnt0 (get-field *piso2-sreg$r-cnt0* st))
         (r-cnt0.s (get-field *link$s* r-cnt0))
         (r-cnt0.d (get-field *link$d* r-cnt0))
         (w-data0 (get-field *piso2-sreg$w-data0* st))
         (w-data0.s (get-field *link$s* w-data0))
         (w-cnt0 (get-field *piso2-sreg$w-cnt0* st))
         (w-cnt0.s (get-field *link$s* w-cnt0))

         (r-cnt0=0~ (f-not (f$fast-zero (strip-cars r-cnt0.d))))
         (r0-full (f-and3 (car r-data0.s) (car r-cnt0.s) r-cnt0=0~))
         (w0-empty- (f-or (car w-data0.s) (car w-cnt0.s)))
         (shift-empty-out0- (f-or empty-out0- w0-empty-)))
      (joint-act r0-full shift-empty-out0- go-out0)))

  (defthm piso2-sreg$out0-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (piso2-sreg$out0-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable piso2-sreg$out0-act))))

  ;; Extract the "out1-act" signal

  (defund piso2-sreg$out1-act (inputs st data-width)
    (b* ((empty-out1- (nth 2 inputs))
         (go-signals (nthcdr (piso2-sreg$data-ins-len data-width)
                             inputs))
         (go-out1 (nth 2 go-signals))

         (r-data1 (get-field *piso2-sreg$r-data1* st))
         (r-data1.s (get-field *link$s* r-data1))
         (r-cnt1 (get-field *piso2-sreg$r-cnt1* st))
         (r-cnt1.s (get-field *link$s* r-cnt1))
         (r-cnt1.d (get-field *link$d* r-cnt1))
         (w-data1 (get-field *piso2-sreg$w-data1* st))
         (w-data1.s (get-field *link$s* w-data1))
         (w-cnt1 (get-field *piso2-sreg$w-cnt1* st))
         (w-cnt1.s (get-field *link$s* w-cnt1))

         (r-cnt1=0~ (f-not (f$fast-zero (strip-cars r-cnt1.d))))
         (r1-full (f-and3 (car r-data1.s) (car r-cnt1.s) r-cnt1=0~))
         (w1-empty- (f-or (car w-data1.s) (car w-cnt1.s)))
         (shift-empty-out1- (f-or empty-out1- w1-empty-)))
      (joint-act r1-full shift-empty-out1- go-out1)))

  (defthm piso2-sreg$out1-act-inactive
    (implies (equal (nth 2 inputs) t)
             (not (piso2-sreg$out1-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable piso2-sreg$out1-act))))

  (local
   (defthm booleanp-f$fast-zero
     (implies (bvp v)
              (booleanp (f$fast-zero v)))
     :hints (("Goal" :in-theory (enable f-gates f$fast-zero)))
     :rule-classes (:rewrite :type-prescription)))

  (defthm piso2-sreg$in-out-acts-mutually-exclusive
    (implies (and (piso2-sreg$valid-st st data-width cnt-width)
                  (piso2-sreg$in-act inputs st data-width))
             (and (not (piso2-sreg$out0-act inputs st data-width))
                  (not (piso2-sreg$out1-act inputs st data-width))))
    :hints (("Goal" :in-theory (e/d (f-and3
                                     piso2-sreg$valid-st
                                     piso2-sreg$in-act
                                     piso2-sreg$out0-act
                                     piso2-sreg$out1-act)
                                    (link$st-format
                                     piso2-sreg$disabled-rules)))))

  ;; Extract the output data

  (defund piso2-sreg$bit0-out (st)
    (b* ((r-data0 (get-field *piso2-sreg$r-data0* st))
         (r-data0.d (get-field *link$d* r-data0)))
      (f-buf (car (strip-cars r-data0.d)))))

  (defthm booleanp-piso2-sreg$bit0-out
    (implies (and (piso2-sreg$valid-st st data-width cnt-width)
                  (piso2-sreg$out0-act inputs st data-width))
             (booleanp (piso2-sreg$bit0-out st)))
    :hints (("Goal" :in-theory (e/d (f-and3
                                     piso2-sreg$valid-st
                                     piso2-sreg$out0-act
                                     piso2-sreg$bit0-out)
                                    (link$st-format
                                     piso2-sreg$disabled-rules))))
    :rule-classes (:rewrite :type-prescription))

  (defund piso2-sreg$bit1-out (st)
    (b* ((r-data1 (get-field *piso2-sreg$r-data1* st))
         (r-data1.d (get-field *link$d* r-data1)))
      (f-buf (car (strip-cars r-data1.d)))))

  (defthm booleanp-piso2-sreg$bit1-out
    (implies (and (piso2-sreg$valid-st st data-width cnt-width)
                  (piso2-sreg$out1-act inputs st data-width))
             (booleanp (piso2-sreg$bit1-out st)))
    :hints (("Goal" :in-theory (e/d (f-and3
                                     piso2-sreg$valid-st
                                     piso2-sreg$out1-act
                                     piso2-sreg$bit1-out)
                                    (link$st-format
                                     piso2-sreg$disabled-rules))))
    :rule-classes (:rewrite :type-prescription))

  (defun piso2-sreg$outputs (inputs st data-width)
    (list (piso2-sreg$in-act inputs st data-width)
          (piso2-sreg$out0-act inputs st data-width)
          (piso2-sreg$out1-act inputs st data-width)
          (piso2-sreg$bit0-out st)
          (piso2-sreg$bit1-out st)))
  )

;; The value lemma for PISO2-SREG

(defthm piso2-sreg$value
  (b* ((inputs (list* full-in empty-out0- empty-out1-
                      (append data0-in data1-in go-signals))))
    (implies
     (and (piso2-sreg& netlist data-width cnt-width)
          (true-listp data0-in)
          (equal (len data0-in) data-width)
          (true-listp data1-in)
          (equal (len data1-in) data-width)
          (true-listp go-signals)
          (equal (len go-signals) *piso2-sreg$go-num*)
          (piso2-sreg$st-format st data-width cnt-width))
     (equal (se (si 'piso2-sreg data-width) inputs st netlist)
            (piso2-sreg$outputs inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'piso2-sreg data-width)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            piso2-sreg&
                            piso2-sreg*$destructure
                            piso2-sreg$data0-in
                            piso2-sreg$data1-in
                            piso2-sreg$st-format
                            piso2-sreg$in-act
                            piso2-sreg$out0-act
                            piso2-sreg$out1-act
                            piso2-sreg$bit0-out
                            piso2-sreg$bit1-out)
                           (piso2-sreg$disabled-rules
                            de-module-disabled-rules)))))

;; This function specifies the next state of PISO2-SREG.

(defun piso2-sreg$step (inputs st data-width cnt-width)
  (b* ((data0-in   (piso2-sreg$data0-in inputs data-width))
       (data1-in   (piso2-sreg$data1-in inputs data-width))
       (go-signals (nthcdr (piso2-sreg$data-ins-len data-width)
                           inputs))
       (go-buf0 (nth 3 go-signals))
       (go-buf1 (nth 4 go-signals))

       (r-data0 (get-field *piso2-sreg$r-data0* st))
       (r-data0.s (get-field *link$s* r-data0))
       (r-data0.d (get-field *link$d* r-data0))
       (r-cnt0 (get-field *piso2-sreg$r-cnt0* st))
       (r-cnt0.s (get-field *link$s* r-cnt0))
       (r-cnt0.d (get-field *link$d* r-cnt0))
       (w-data0 (get-field *piso2-sreg$w-data0* st))
       (w-data0.s (get-field *link$s* w-data0))
       (w-data0.d (get-field *link$d* w-data0))
       (w-cnt0 (get-field *piso2-sreg$w-cnt0* st))
       (w-cnt0.s (get-field *link$s* w-cnt0))
       (w-cnt0.d (get-field *link$d* w-cnt0))

       (r-data1 (get-field *piso2-sreg$r-data1* st))
       (r-data1.s (get-field *link$s* r-data1))
       (r-data1.d (get-field *link$d* r-data1))
       (r-cnt1 (get-field *piso2-sreg$r-cnt1* st))
       (r-cnt1.s (get-field *link$s* r-cnt1))
       (r-cnt1.d (get-field *link$d* r-cnt1))
       (w-data1 (get-field *piso2-sreg$w-data1* st))
       (w-data1.s (get-field *link$s* w-data1))
       (w-data1.d (get-field *link$d* w-data1))
       (w-cnt1 (get-field *piso2-sreg$w-cnt1* st))
       (w-cnt1.s (get-field *link$s* w-cnt1))
       (w-cnt1.d (get-field *link$d* w-cnt1))

       (r-cnt0=0 (f$fast-zero (strip-cars r-cnt0.d)))
       (r-cnt1=0 (f$fast-zero (strip-cars r-cnt1.d)))

       (in-act (piso2-sreg$in-act inputs st data-width))
       (out0-act (piso2-sreg$out0-act inputs st data-width))
       (out1-act (piso2-sreg$out1-act inputs st data-width))

       (shift0-act (f-or in-act out0-act))
       (shift1-act (f-or in-act out1-act))

       (buf0-full-in (f-and (car w-data0.s) (car w-cnt0.s)))
       (buf0-empty-out- (f-or (car r-data0.s) (car r-cnt0.s)))
       (buf0-act (joint-act buf0-full-in buf0-empty-out- go-buf0))

       (buf1-full-in (f-and (car w-data1.s) (car w-cnt1.s)))
       (buf1-empty-out- (f-or (car r-data1.s) (car r-cnt1.s)))
       (buf1-act (joint-act buf1-full-in buf1-empty-out- go-buf1))

       (r-data0-inputs (list* buf0-act shift0-act (strip-cars w-data0.d)))
       (r-cnt0-inputs (list* buf0-act shift0-act (strip-cars w-cnt0.d)))
       (w-data0-inputs (list* shift0-act buf0-act
                             (fv-if r-cnt0=0
                                    data0-in
                                    (append (nthcdr 1 (v-threefix
                                                       (strip-cars r-data0.d)))
                                            '(nil)))))
       (w-cnt0-inputs
        (list* shift0-act buf0-act
               (fv-if r-cnt0=0
                      (append (make-list (1- cnt-width))
                              '(t))
                      (take cnt-width
                            (fv-adder
                             t
                             (strip-cars r-cnt0.d)
                             (fv-not
                              (cons t (make-list (1- cnt-width)))))))))

       (r-data1-inputs (list* buf1-act shift1-act (strip-cars w-data1.d)))
       (r-cnt1-inputs (list* buf1-act shift1-act (strip-cars w-cnt1.d)))
       (w-data1-inputs (list* shift1-act buf1-act
                             (fv-if r-cnt1=0
                                    data1-in
                                    (append (nthcdr 1 (v-threefix
                                                       (strip-cars r-data1.d)))
                                            '(nil)))))
       (w-cnt1-inputs
        (list* shift1-act buf1-act
               (fv-if r-cnt1=0
                      (append (make-list (1- cnt-width))
                              '(t))
                      (take cnt-width
                            (fv-adder
                             t
                             (strip-cars r-cnt1.d)
                             (fv-not
                              (cons t (make-list (1- cnt-width))))))))))
    (list
     ;; R-DATA0
     (link$step r-data0-inputs r-data0 data-width)
     ;; R-CNT0
     (link$step r-cnt0-inputs r-cnt0 cnt-width)
     ;; W-DATA0
     (link$step w-data0-inputs w-data0 data-width)
     ;; W-CNT0
     (link$step w-cnt0-inputs w-cnt0 cnt-width)
     ;; R-DATA1
     (link$step r-data1-inputs r-data1 data-width)
     ;; R-CNT1
     (link$step r-cnt1-inputs r-cnt1 cnt-width)
     ;; W-DATA1
     (link$step w-data1-inputs w-data1 data-width)
     ;; W-CNT1
     (link$step w-cnt1-inputs w-cnt1 cnt-width))))

(defthm len-of-piso2-sreg$step
  (equal (len (piso2-sreg$step inputs st data-width cnt-width))
         *piso2-sreg$st-len*))

(local
 (defthm len-cdr
   (implies (< 0 (len x))
            (equal (len (cdr x))
                   (1- (len x))))))

;; The state lemma for PISO2-SREG

(defthm piso2-sreg$state
  (b* ((inputs (list* full-in empty-out0- empty-out1-
                      (append data0-in data1-in go-signals))))
    (implies
     (and (piso2-sreg& netlist data-width cnt-width)
          (true-listp data0-in)
          (equal (len data0-in) data-width)
          (true-listp data1-in)
          (equal (len data1-in) data-width)
          (true-listp go-signals)
          (equal (len go-signals) *piso2-sreg$go-num*)
          (piso2-sreg$st-format st data-width cnt-width))
     (equal (de (si 'piso2-sreg data-width) inputs st netlist)
            (piso2-sreg$step inputs st data-width cnt-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'piso2-sreg data-width)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            piso2-sreg&
                            piso2-sreg*$destructure
                            piso2-sreg$data0-in
                            piso2-sreg$data1-in
                            piso2-sreg$in-act
                            piso2-sreg$out0-act
                            piso2-sreg$out1-act
                            piso2-sreg$st-format)
                           (piso2-sreg$disabled-rules
                            de-module-disabled-rules)))))

(in-theory (disable piso2-sreg$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund piso2-sreg$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in     (nth 0 inputs))
       (empty-out0- (nth 1 inputs))
       (empty-out1- (nth 2 inputs))
       (data0-in    (piso2-sreg$data0-in inputs data-width))
       (data1-in    (piso2-sreg$data1-in inputs data-width))
       (go-signals  (nthcdr (piso2-sreg$data-ins-len data-width)
                            inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out0-)
     (booleanp empty-out1-)
     (or (not full-in)
         (and (bvp data0-in) (bvp data1-in)))
     (true-listp go-signals)
     (= (len go-signals) *piso2-sreg$go-num*)
     (equal inputs
            (list* full-in empty-out0- empty-out1-
                   (append data0-in data1-in go-signals))))))

(local
 (defthm piso2-sreg$input-format-lemma-1
   (implies (piso2-sreg$input-format inputs data-width)
            (booleanp (nth 0 inputs)))
   :hints (("Goal" :in-theory (enable piso2-sreg$input-format)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm piso2-sreg$input-format-lemma-2
   (implies (piso2-sreg$input-format inputs data-width)
            (booleanp (nth 1 inputs)))
   :hints (("Goal" :in-theory (enable piso2-sreg$input-format)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm piso2-sreg$input-format-lemma-3
   (implies (piso2-sreg$input-format inputs data-width)
            (booleanp (nth 2 inputs)))
   :hints (("Goal" :in-theory (enable piso2-sreg$input-format)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm piso2-sreg$input-format-lemma-4
   (implies (and (piso2-sreg$input-format inputs data-width)
                 (nth 0 inputs))
            (and (bvp (piso2-sreg$data0-in inputs data-width))
                 (bvp (piso2-sreg$data1-in inputs data-width))))
   :hints (("Goal" :in-theory (enable piso2-sreg$input-format)))))

(defthm booleanp-piso2-sreg$in-act
  (implies (and (piso2-sreg$input-format inputs data-width)
                (piso2-sreg$valid-st st data-width cnt-width))
           (booleanp (piso2-sreg$in-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (e/d (f-and3
                            piso2-sreg$valid-st
                            piso2-sreg$in-act)
                           (piso2-sreg$disabled-rules
                            link$st-format))))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-piso2-sreg$out0-act
  (implies (and (piso2-sreg$input-format inputs data-width)
                (piso2-sreg$valid-st st data-width cnt-width))
           (booleanp (piso2-sreg$out0-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (e/d (f-and3
                            piso2-sreg$valid-st
                            piso2-sreg$out0-act)
                           (piso2-sreg$disabled-rules
                            link$st-format))))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-piso2-sreg$out1-act
  (implies (and (piso2-sreg$input-format inputs data-width)
                (piso2-sreg$valid-st st data-width cnt-width))
           (booleanp (piso2-sreg$out1-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (e/d (f-and3
                            piso2-sreg$valid-st
                            piso2-sreg$out1-act)
                           (piso2-sreg$disabled-rules
                            link$st-format))))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma piso2-sreg :sizes (data-width cnt-width))

;; ======================================================================

;; 3. Single-Step-Update Property

;; Specify the functionality of PISO2-SREG

(defun piso2-sreg$op (x)
  (rev x))

(defthm append-of-piso2-sreg$op-with-singleton
  (equal (append (piso2-sreg$op x) (list a))
         (piso2-sreg$op (cons a x))))

(in-theory (disable piso2-sreg$op))

;; The operation of PISO2-SREG over a data sequence

(defun piso2-sreg$op-map (x)
  (if (atom x)
      nil
    (append (piso2-sreg$op (car x))
            (piso2-sreg$op-map (cdr x)))))

(defthm piso2-sreg$op-map-of-append
  (equal (piso2-sreg$op-map (append x y))
         (append (piso2-sreg$op-map x)
                 (piso2-sreg$op-map y))))

;; The extraction function for PISO2-SREG

(defund piso2-sreg$extract0 (st)
  (b* ((r-data0 (get-field *piso2-sreg$r-data0* st))
       (r-data0.s (get-field *link$s* r-data0))
       (r-data0.d (get-field *link$d* r-data0))
       (r-cnt0 (get-field *piso2-sreg$r-cnt0* st))
       (r-cnt0.d (get-field *link$d* r-cnt0))
       (w-data0 (get-field *piso2-sreg$w-data0* st))
       (w-data0.d (get-field *link$d* w-data0))
       (w-cnt0 (get-field *piso2-sreg$w-cnt0* st))
       (w-cnt0.d (get-field *link$d* w-cnt0)))
    (if (fullp r-data0.s)
        (take (v-to-nat (strip-cars r-cnt0.d))
              (strip-cars r-data0.d))
      (take (v-to-nat (strip-cars w-cnt0.d))
            (strip-cars w-data0.d)))))

(defund piso2-sreg$extract1 (st)
  (b* ((r-data1 (get-field *piso2-sreg$r-data1* st))
       (r-data1.s (get-field *link$s* r-data1))
       (r-data1.d (get-field *link$d* r-data1))
       (r-cnt1 (get-field *piso2-sreg$r-cnt1* st))
       (r-cnt1.d (get-field *link$d* r-cnt1))
       (w-data1 (get-field *piso2-sreg$w-data1* st))
       (w-data1.d (get-field *link$d* w-data1))
       (w-cnt1 (get-field *piso2-sreg$w-cnt1* st))
       (w-cnt1.d (get-field *link$d* w-cnt1)))
    (if (fullp r-data1.s)
        (take (v-to-nat (strip-cars r-cnt1.d))
              (strip-cars r-data1.d))
      (take (v-to-nat (strip-cars w-cnt1.d))
            (strip-cars w-data1.d)))))

(local
 (defthm v-to-nat-of-v-zp
   (equal (v-zp x)
          (equal (v-to-nat x) 0))
   :hints (("Goal" :in-theory (enable v-zp v-nzp v-to-nat)))))

(defthm piso2-sreg$extract0-not-empty
  (implies (and (piso2-sreg$out0-act inputs st data-width)
                (piso2-sreg$valid-st st data-width cnt-width))
           (< 0 (len (piso2-sreg$extract0 st))))
  :hints (("Goal"
           :in-theory (e/d (f-and3
                            piso2-sreg$valid-st
                            piso2-sreg$extract0
                            piso2-sreg$out0-act)
                           (acl2::default-expt-2))))
  :rule-classes :linear)

(defthm piso2-sreg$extract1-not-empty
  (implies (and (piso2-sreg$out1-act inputs st data-width)
                (piso2-sreg$valid-st st data-width cnt-width))
           (< 0 (len (piso2-sreg$extract1 st))))
  :hints (("Goal"
           :in-theory (e/d (f-and3
                            piso2-sreg$valid-st
                            piso2-sreg$extract1
                            piso2-sreg$out1-act)
                           (acl2::default-expt-2))))
  :rule-classes :linear)

(defthmd lens-of-piso2-sreg$extracts-lemma
  (implies (and (piso2-sreg$in-act inputs st data-width)
                (piso2-sreg$valid-st st data-width cnt-width))
           (and (equal (len (piso2-sreg$extract0 st))
                       0)
                (equal (len (piso2-sreg$extract1 st))
                       0)))
  :hints (("Goal" :in-theory (e/d (f-and3
                                   piso2-sreg$valid-st
                                   piso2-sreg$in-act
                                   piso2-sreg$extract0
                                   piso2-sreg$extract1)
                                  (acl2::default-expt-2)))))

(defthm lens-of-piso2-sreg$extracts-contrapositive-lemma-1
  (implies (and (piso2-sreg$in-act inputs st data-width)
                (or (< 0 (len (piso2-sreg$extract0 st)))
                    (< 0 (len (piso2-sreg$extract1 st)))))
           (not (piso2-sreg$valid-st st data-width cnt-width)))
  :hints (("Goal" :in-theory (e/d (f-and3
                                   piso2-sreg$valid-st
                                   piso2-sreg$in-act
                                   piso2-sreg$extract0
                                   piso2-sreg$extract1)
                                  (acl2::default-expt-2)))))

(defthm lens-of-piso2-sreg$extracts-contrapositive-lemma-2
  (implies (and (piso2-sreg$valid-st st data-width cnt-width)
                (or (< 0 (len (piso2-sreg$extract0 st)))
                    (< 0 (len (piso2-sreg$extract1 st)))))
           (not (piso2-sreg$in-act inputs st data-width)))
  :hints (("Goal" :in-theory (e/d (f-and3
                                   piso2-sreg$valid-st
                                   piso2-sreg$in-act
                                   piso2-sreg$extract0
                                   piso2-sreg$extract1)
                                  (acl2::default-expt-2)))))

;; Specify and prove a state invariant

(progn
  (defund piso2-sreg$inv (st)
    (b* ((r-data0 (get-field *piso2-sreg$r-data0* st))
         (r-data0.s (get-field *link$s* r-data0))
         (r-data0.d (get-field *link$d* r-data0))
         (r-cnt0 (get-field *piso2-sreg$r-cnt0* st))
         (r-cnt0.s (get-field *link$s* r-cnt0))
         (r-cnt0.d (get-field *link$d* r-cnt0))
         (w-data0 (get-field *piso2-sreg$w-data0* st))
         (w-data0.s (get-field *link$s* w-data0))
         (w-data0.d (get-field *link$d* w-data0))
         (w-cnt0 (get-field *piso2-sreg$w-cnt0* st))
         (w-cnt0.s (get-field *link$s* w-cnt0))
         (w-cnt0.d (get-field *link$d* w-cnt0))

         (r-data1 (get-field *piso2-sreg$r-data1* st))
         (r-data1.s (get-field *link$s* r-data1))
         (r-data1.d (get-field *link$d* r-data1))
         (r-cnt1 (get-field *piso2-sreg$r-cnt1* st))
         (r-cnt1.s (get-field *link$s* r-cnt1))
         (r-cnt1.d (get-field *link$d* r-cnt1))
         (w-data1 (get-field *piso2-sreg$w-data1* st))
         (w-data1.s (get-field *link$s* w-data1))
         (w-data1.d (get-field *link$d* w-data1))
         (w-cnt1 (get-field *piso2-sreg$w-cnt1* st))
         (w-cnt1.s (get-field *link$s* w-cnt1))
         (w-cnt1.d (get-field *link$d* w-cnt1)))
      (and (equal r-data0.s r-cnt0.s)
           (equal w-data0.s w-cnt0.s)
           (not (equal r-data0.s w-data0.s))

           (or (emptyp r-cnt0.s)
               (<= (v-to-nat (strip-cars r-cnt0.d))
                   (len r-data0.d)))
           (or (emptyp w-cnt0.s)
               (<= (v-to-nat (strip-cars w-cnt0.d))
                   (len w-data0.d)))

           (equal r-data1.s r-cnt1.s)
           (equal w-data1.s w-cnt1.s)
           (not (equal r-data1.s w-data1.s))

           (or (emptyp r-cnt1.s)
               (<= (v-to-nat (strip-cars r-cnt1.d))
                   (len r-data1.d)))
           (or (emptyp w-cnt1.s)
               (<= (v-to-nat (strip-cars w-cnt1.d))
                   (len w-data1.d))))))

  (defthm lens-of-piso2-sreg$extracts-upper-bound
    (implies (and (piso2-sreg$valid-st st data-width cnt-width)
                  (piso2-sreg$inv st))
             (and (<= (len (piso2-sreg$extract0 st))
                      data-width)
                  (<= (len (piso2-sreg$extract1 st))
                      data-width)))
    :hints (("Goal" :in-theory (e/d (piso2-sreg$valid-st
                                     piso2-sreg$inv
                                     piso2-sreg$extract0
                                     piso2-sreg$extract1)
                                    (piso2-sreg$disabled-rules))))
    :rule-classes :linear)

  (local
   (defthm v-to-nat-of-repeat-lemma
     (equal (v-to-nat (append (repeat n nil) '(t)))
            (expt 2 (nfix n)))
     :hints (("Goal" :in-theory (enable v-to-nat repeat)))))

  (defthm piso2-sreg$inv-preserved
    (implies (and (piso2-sreg$input-format inputs data-width)
                  (piso2-sreg$valid-st st data-width cnt-width)
                  (piso2-sreg$inv st))
             (piso2-sreg$inv
              (piso2-sreg$step inputs st data-width cnt-width)))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              bvp
                              pos-len=>cons
                              piso2-sreg$valid-st
                              piso2-sreg$inv
                              piso2-sreg$step
                              piso2-sreg$in-act
                              piso2-sreg$out0-act
                              piso2-sreg$out1-act)
                             (piso2-sreg$disabled-rules)))))
  )

;; The extracted next-state function for PISO2-SREG.  Note that this
;; function avoids exploring the internal computation of PISO2-SREG.

(defund piso2-sreg$extracted0-step (inputs st data-width)
  (b* ((data (piso2-sreg$data0-in inputs data-width))
       (extracted-st (piso2-sreg$extract0 st)))
    (cond
     ((equal (piso2-sreg$out0-act inputs st data-width) t)
      (cdr extracted-st))
     ((equal (piso2-sreg$in-act inputs st data-width) t)
      data)
     (t extracted-st))))

(defund piso2-sreg$extracted1-step (inputs st data-width)
  (b* ((data (piso2-sreg$data1-in inputs data-width))
       (extracted-st (piso2-sreg$extract1 st)))
    (cond
     ((equal (piso2-sreg$out1-act inputs st data-width) t)
      (cdr extracted-st))
     ((equal (piso2-sreg$in-act inputs st data-width) t)
      data)
     (t extracted-st))))

;; The single-step-update property

(defthm piso2-sreg$extracted-step-correct
  (b* ((next-st (piso2-sreg$step inputs st data-width cnt-width)))
    (implies (and (piso2-sreg$input-format inputs data-width)
                  (piso2-sreg$valid-st st data-width cnt-width)
                  (piso2-sreg$inv st))
             (and
              (equal (piso2-sreg$extract0 next-st)
                     (piso2-sreg$extracted0-step
                      inputs st data-width))
              (equal (piso2-sreg$extract1 next-st)
                     (piso2-sreg$extracted1-step
                      inputs st data-width)))))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            f-sr
                            bvp
                            pos-len=>cons
                            piso2-sreg$extracted0-step
                            piso2-sreg$extracted1-step
                            piso2-sreg$valid-st
                            piso2-sreg$inv
                            piso2-sreg$step
                            piso2-sreg$in-act
                            piso2-sreg$out0-act
                            piso2-sreg$out1-act
                            piso2-sreg$extract0
                            piso2-sreg$extract1)
                           (piso2-sreg$disabled-rules)))))

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that piso2-sreg$valid-st is an invariant.

(encapsulate
  ()

  (local
   (defthm piso2-sreg$valid-st-preserved-aux
     (implies (len-1-true-listp x)
              (len-1-true-listp (cons (list e) x)))
     :hints (("Goal" :in-theory (enable len-1-true-listp)))))

  (defthm piso2-sreg$valid-st-preserved
    (implies (and (piso2-sreg$input-format inputs data-width)
                  (piso2-sreg$valid-st st data-width cnt-width))
             (piso2-sreg$valid-st
              (piso2-sreg$step inputs st data-width cnt-width)
              data-width
              cnt-width))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              f-and3
                              bvp
                              pos-len=>cons
                              piso2-sreg$st-format
                              piso2-sreg$valid-st
                              piso2-sreg$step
                              piso2-sreg$in-act
                              piso2-sreg$out0-act
                              piso2-sreg$out1-act)
                             (piso2-sreg$disabled-rules)))))
  )

(defthm piso2-sreg$extract0-lemma
  (implies (and (piso2-sreg$out0-act inputs st data-width)
                (piso2-sreg$valid-st st data-width cnt-width))
           (equal (piso2-sreg$bit0-out st)
                  (car (piso2-sreg$extract0 st))))
  :hints (("Goal" :in-theory (e/d (f-and3
                                   booleanp-car-of-bv
                                   piso2-sreg$out0-act
                                   piso2-sreg$valid-st
                                   piso2-sreg$bit0-out
                                   piso2-sreg$extract0)
                                  (acl2::default-expt-2)))))

(defthm booleanp-car-of-piso2-sreg$extract0
  (implies (and (piso2-sreg$out0-act inputs st data-width)
                (piso2-sreg$valid-st st data-width cnt-width))
           (booleanp (car (piso2-sreg$extract0 st))))
  :hints (("Goal"
           :use piso2-sreg$extract0-lemma
           :in-theory (e/d ()
                           (piso2-sreg$extract0-lemma))))
  :rule-classes (:rewrite :type-prescription))

(defthm piso2-sreg$extract1-lemma
  (implies (and (piso2-sreg$out1-act inputs st data-width)
                (piso2-sreg$valid-st st data-width cnt-width))
           (equal (piso2-sreg$bit1-out st)
                  (car (piso2-sreg$extract1 st))))
  :hints (("Goal" :in-theory (e/d (f-and3
                                   booleanp-car-of-bv
                                   piso2-sreg$out1-act
                                   piso2-sreg$valid-st
                                   piso2-sreg$bit1-out
                                   piso2-sreg$extract1)
                                  (acl2::default-expt-2)))))

(defthm booleanp-car-of-piso2-sreg$extract1
  (implies (and (piso2-sreg$out1-act inputs st data-width)
                (piso2-sreg$valid-st st data-width cnt-width))
           (booleanp (car (piso2-sreg$extract1 st))))
  :hints (("Goal"
           :use piso2-sreg$extract1-lemma
           :in-theory (e/d ()
                           (piso2-sreg$extract1-lemma))))
  :rule-classes (:rewrite :type-prescription))

;; Extract the accepted input sequences

(seq-gen piso2-sreg in in-act 0
         (cons (piso2-sreg$data0-in inputs data-width)
               (piso2-sreg$data1-in inputs data-width))
         :sizes (data-width cnt-width))

(seq-gen piso2-sreg in0 in-act 0
         (piso2-sreg$data0-in inputs data-width)
         :sizes (data-width cnt-width))

(seq-gen piso2-sreg in1 in-act 0
         (piso2-sreg$data1-in inputs data-width)
         :sizes (data-width cnt-width))

;; Extract the valid output sequences

(seq-gen piso2-sreg out0 out0-act 1
         (piso2-sreg$bit0-out st)
         :netlist-data (nth 3 outputs)
         :sizes (data-width cnt-width))

(seq-gen piso2-sreg out1 out1-act 2
         (piso2-sreg$bit1-out st)
         :netlist-data (nth 4 outputs)
         :sizes (data-width cnt-width))

;; The multi-step input-output relationship

(encapsulate
  ()

  (local
   (defthm piso2-sreg$op-of-len-0
     (implies (equal (len x) 0)
              (not (piso2-sreg$op x)))
     :hints (("Goal" :in-theory (enable piso2-sreg$op)))))

  (local
   (defthm piso2-sreg$dataflow-correct-aux
     (implies (equal (append x y1)
                     (append (piso2-sreg$op-map seq) y2))
              (equal (append x y1 z)
                     (append (piso2-sreg$op-map seq)
                             y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (associativity-of-append))))))

  (defthmd piso2-sreg$dataflow0-correct
    (b* ((extracted-st (piso2-sreg$extract0 st))
         (final-st (piso2-sreg$run
                    inputs-seq st data-width cnt-width n))
         (final-extracted-st (piso2-sreg$extract0 final-st)))
      (implies
       (and (piso2-sreg$input-format-n inputs-seq data-width n)
            (piso2-sreg$valid-st st data-width cnt-width)
            (piso2-sreg$inv st))
       (equal (append (piso2-sreg$op final-extracted-st)
                      (piso2-sreg$out0-seq
                       inputs-seq st data-width cnt-width n))
              (append (piso2-sreg$op-map
                       (piso2-sreg$in0-seq
                        inputs-seq st data-width cnt-width n))
                      (piso2-sreg$op extracted-st)))))
    :hints (("Goal"
             :in-theory (enable pos-len=>cons
                                lens-of-piso2-sreg$extracts-lemma
                                piso2-sreg$extracted0-step))))

  (defthmd piso2-sreg$dataflow1-correct
    (b* ((extracted-st (piso2-sreg$extract1 st))
         (final-st (piso2-sreg$run
                    inputs-seq st data-width cnt-width n))
         (final-extracted-st (piso2-sreg$extract1 final-st)))
      (implies
       (and (piso2-sreg$input-format-n inputs-seq data-width n)
            (piso2-sreg$valid-st st data-width cnt-width)
            (piso2-sreg$inv st))
       (equal (append (piso2-sreg$op final-extracted-st)
                      (piso2-sreg$out1-seq
                       inputs-seq st data-width cnt-width n))
              (append (piso2-sreg$op-map
                       (piso2-sreg$in1-seq
                        inputs-seq st data-width cnt-width n))
                      (piso2-sreg$op extracted-st)))))
    :hints (("Goal"
             :in-theory (enable pos-len=>cons
                                lens-of-piso2-sreg$extracts-lemma
                                piso2-sreg$extracted1-step))))

  (defthmd piso2-sreg$functionally-correct-1
    (b* ((extracted-st (piso2-sreg$extract0 st))
         (final-st (de-n (si 'piso2-sreg data-width)
                         inputs-seq st netlist n))
         (final-extracted-st (piso2-sreg$extract0 final-st)))
      (implies
       (and (piso2-sreg& netlist data-width cnt-width)
            (piso2-sreg$input-format-n inputs-seq data-width n)
            (piso2-sreg$valid-st st data-width cnt-width)
            (piso2-sreg$inv st))
       (equal (append (piso2-sreg$op final-extracted-st)
                      (piso2-sreg$netlist-out0-seq
                       inputs-seq st netlist data-width n))
              (append (piso2-sreg$op-map
                       (piso2-sreg$netlist-in0-seq
                        inputs-seq st netlist data-width n))
                      (piso2-sreg$op extracted-st)))))
    :hints (("Goal"
             :use piso2-sreg$dataflow0-correct
             :in-theory (enable piso2-sreg$valid-st=>st-format
                                piso2-sreg$de-n))))

  (defthmd piso2-sreg$functionally-correct-2
    (b* ((extracted-st (piso2-sreg$extract1 st))
         (final-st (de-n (si 'piso2-sreg data-width)
                         inputs-seq st netlist n))
         (final-extracted-st (piso2-sreg$extract1 final-st)))
      (implies
       (and (piso2-sreg& netlist data-width cnt-width)
            (piso2-sreg$input-format-n inputs-seq data-width n)
            (piso2-sreg$valid-st st data-width cnt-width)
            (piso2-sreg$inv st))
       (equal (append (piso2-sreg$op final-extracted-st)
                      (piso2-sreg$netlist-out1-seq
                       inputs-seq st netlist data-width n))
              (append (piso2-sreg$op-map
                       (piso2-sreg$netlist-in1-seq
                        inputs-seq st netlist data-width n))
                      (piso2-sreg$op extracted-st)))))
    :hints (("Goal"
             :use piso2-sreg$dataflow1-correct
             :in-theory (enable piso2-sreg$valid-st=>st-format
                                piso2-sreg$de-n))))
  )

