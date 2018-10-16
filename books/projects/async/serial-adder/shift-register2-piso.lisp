;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2018

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
 (deftheory shift-register2-piso$disabled-rules
   '(if*
     not
     default-car
     default-cdr
     strip-cars
     v-threefix
     append
     append-v-threefix
     acl2::associativity-of-append
     acl2::default-expt-2)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of SHIFT-REGISTER2-PISO
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of SHIFT-REGISTER2-PISO
;;
;; Construct a DE module generator for circuits consisting of two PISO shift
;; registers that share the same communication signal at their input ports.
;; Prove the value and state lemmas for this module generator.

(defconst *shift-register2-piso$go-num* 5)
(defconst *shift-register2-piso$st-len* 8)

(defun shift-register2-piso$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 3 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun shift-register2-piso$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (shift-register2-piso$data-ins-len data-width)
     *shift-register2-piso$go-num*))

;; DE module generator of SHIFT-REGISTER2-PISO

(module-generator
 shift-register2-piso* (data-width cnt-width)
 (si 'shift-register2-piso data-width)
 (list* 'full-in 'empty-out0- 'empty-out1-
        (append (sis 'data0-in 0 data-width)
                (sis 'data1-in 0 data-width)
                (sis 'go 0 *shift-register2-piso$go-num*)))
 '(in-act out0-act out1-act bit0-out bit1-out)
 '(r-reg0 r-cnt0 w-reg0 w-cnt0 r-reg1 r-cnt1 w-reg1 w-cnt1)
 (list
  ;; LINKS
  ;; R-REG0
  (list 'r-reg0
        (list* 'r-reg0-status (sis 'r-reg0-out 0 data-width))
        (si 'link data-width)
        (list* 'buf0-act 'shift0-act (sis 'r-reg0-in 0 data-width)))

  ;; R-CNT0
  (list 'r-cnt0
        (list* 'r-cnt0-status (sis 'r-cnt0-out 0 cnt-width))
        (si 'link cnt-width)
        (list* 'buf0-act 'shift0-act (sis 'r-cnt0-in 0 cnt-width)))

  ;; W-REG0
  (list 'w-reg0
        (list* 'w-reg0-status (sis 'w-reg0-out 0 data-width))
        (si 'link data-width)
        (list* 'shift0-act 'buf0-act (sis 'w-reg0-in 0 data-width)))

  ;; W-CNT0
  (list 'w-cnt0
        (list* 'w-cnt0-status (sis 'w-cnt0-out 0 cnt-width))
        (si 'link cnt-width)
        (list* 'shift0-act 'buf0-act (sis 'w-cnt0-in 0 cnt-width)))

  ;; R-REG1
  (list 'r-reg1
        (list* 'r-reg1-status (sis 'r-reg1-out 0 data-width))
        (si 'link data-width)
        (list* 'buf1-act 'shift1-act (sis 'r-reg1-in 0 data-width)))

  ;; R-CNT1
  (list 'r-cnt1
        (list* 'r-cnt1-status (sis 'r-cnt1-out 0 cnt-width))
        (si 'link cnt-width)
        (list* 'buf1-act 'shift1-act (sis 'r-cnt1-in 0 cnt-width)))

  ;; W-REG1
  (list 'w-reg1
        (list* 'w-reg1-status (sis 'w-reg1-out 0 data-width))
        (si 'link data-width)
        (list* 'shift1-act 'buf1-act (sis 'w-reg1-in 0 data-width)))

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
  '(s1 (r0-ready-in) b-and3 (r-reg0-status r-cnt0-status r-cnt0=0))
  '(s2 (r0-full) b-and3 (r-reg0-status r-cnt0-status r-cnt0=0~))
  '(s3 (w0-empty-) b-or (w-reg0-status w-cnt0-status))
  '(s4 (shift-empty-out0-) b-or (empty-out0- w0-empty-))

  (list 'r-cnt1=0?
        '(r-cnt1=0)
        (si 'fast-zero cnt-width)
        (sis 'r-cnt1-out 0 cnt-width))
  '(s5 (r-cnt1=0~) b-not (r-cnt1=0))
  '(s6 (r1-ready-in) b-and3 (r-reg1-status r-cnt1-status r-cnt1=0))
  '(s7 (r1-full) b-and3 (r-reg1-status r-cnt1-status r-cnt1=0~))
  '(s8 (w1-empty-) b-or (w-reg1-status w-cnt1-status))
  '(s9 (shift-empty-out1-) b-or (empty-out1- w1-empty-))

  '(s10 (shift-full-in) b-and3 (full-in r0-ready-in r1-ready-in))
  '(s11 (w0+1-empty-) b-or (w0-empty- w1-empty-))
  (list 'in-cntl
        '(in-act)
        'joint-cntl
        (list 'shift-full-in 'w0+1-empty- (si 'go 0)))
  (list 'shift-reg0-op0
        (sis 'w-reg0-in0 0 data-width)
        (si 'v-buf data-width)
        (sis 'data0-in 0 data-width))
  (list 'shift-cnt0-op0
        (sis 'w-cnt0-in0 0 cnt-width)
        (si 'v-buf cnt-width)
        (append (make-list (1- cnt-width) :initial-element 'low)
                '(high)))
  (list 'shift-reg1-op0
        (sis 'w-reg1-in0 0 data-width)
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
        (sis 'w-reg0-in1 0 data-width)
        (si 'v-buf data-width)
        (append (sis 'r-reg0-out 1 (1- data-width))
                '(low)))
  (list 'shift-cnt0-op1
        (sis 'w-cnt0-in1 0 cnt-width)
        (si 'counter cnt-width)
        (sis 'r-cnt0-out 0 cnt-width))
  '(shift0-cntl (shift0-act) b-or (in-act out0-act))
  (list 'shift-reg0-op
        (sis 'w-reg0-in 0 data-width)
        (si 'tv-if (tree-number (make-tree data-width)))
        (cons 'r-cnt0=0
              (append (sis 'w-reg0-in0 0 data-width)
                      (sis 'w-reg0-in1 0 data-width))))
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
        (sis 'w-reg1-in1 0 data-width)
        (si 'v-buf data-width)
        (append (sis 'r-reg1-out 1 (1- data-width))
                '(low)))
  (list 'shift-cnt1-op1
        (sis 'w-cnt1-in1 0 cnt-width)
        (si 'counter cnt-width)
        (sis 'r-cnt1-out 0 cnt-width))
  '(shift1-cntl (shift1-act) b-or (in-act out1-act))
  (list 'shift-reg1-op
        (sis 'w-reg1-in 0 data-width)
        (si 'tv-if (tree-number (make-tree data-width)))
        (cons 'r-cnt1=0
              (append (sis 'w-reg1-in0 0 data-width)
                      (sis 'w-reg1-in1 0 data-width))))
  (list 'shift-cnt1-op
        (sis 'w-cnt1-in 0 cnt-width)
        (si 'tv-if (tree-number (make-tree cnt-width)))
        (cons 'r-cnt1=0
              (append (sis 'w-cnt1-in0 0 cnt-width)
                      (sis 'w-cnt1-in1 0 cnt-width))))

  ;; Buffer0
  '(b0 (buf0-full-in) b-and (w-reg0-status w-cnt0-status))
  '(b1 (buf0-empty-out-) b-or (r-reg0-status r-cnt0-status))
  (list 'buf0-cntl
        '(buf0-act)
        'joint-cntl
        (list 'buf0-full-in 'buf0-empty-out- (si 'go 3)))
  (list 'buf0-reg-op
        (sis 'r-reg0-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'w-reg0-out 0 data-width))
  (list 'buf0-cnt-op
        (sis 'r-cnt0-in 0 cnt-width)
        (si 'v-buf cnt-width)
        (sis 'w-cnt0-out 0 cnt-width))

  ;; Buffer1
  '(b2 (buf1-full-in) b-and (w-reg1-status w-cnt1-status))
  '(b3 (buf1-empty-out-) b-or (r-reg1-status r-cnt1-status))
  (list 'buf1-cntl
        '(buf1-act)
        'joint-cntl
        (list 'buf1-full-in 'buf1-empty-out- (si 'go 4)))
  (list 'buf1-reg-op
        (sis 'r-reg1-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'w-reg1-out 0 data-width))
  (list 'buf1-cnt-op
        (sis 'r-cnt1-in 0 cnt-width)
        (si 'v-buf cnt-width)
        (sis 'w-cnt1-out 0 cnt-width))

  ;; OUTPUTS
  (list 'out0 '(bit0-out) 'wire (sis 'r-reg0-out 0 1))
  (list 'out1 '(bit1-out) 'wire (sis 'r-reg1-out 0 1)))

 :guard (and (posp data-width) (posp cnt-width)))

(make-event
 `(progn
    ,@(state-accessors-gen 'shift-register2-piso
                           '(r-reg0 r-cnt0 w-reg0 w-cnt0
                                    r-reg1 r-cnt1 w-reg1 w-cnt1)
                           0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; SHIFT-REGISTER2-PISO.

(defun shift-register2-piso$netlist (data-width cnt-width)
  (declare (xargs :guard (and (posp data-width)
                              (natp cnt-width)
                              (<= 2 cnt-width))))
  (cons (shift-register2-piso* data-width cnt-width)
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

;; Recognizer for SHIFT-REGISTER2-PISO

(defund shift-register2-piso& (netlist data-width cnt-width)
  (declare (xargs :guard (and (alistp netlist)
                              (posp data-width)
                              (natp cnt-width)
                              (<= 2 cnt-width))))
  (and (equal (assoc (si 'shift-register2-piso data-width) netlist)
              (shift-register2-piso* data-width cnt-width))
       (b* ((netlist (delete-to-eq (si 'shift-register2-piso data-width)
                                   netlist)))
         (and (link& netlist data-width)
              (link& netlist cnt-width)
              (joint-cntl& netlist)
              (fast-zero& netlist cnt-width)
              (counter& netlist cnt-width)
              (v-buf& netlist data-width)
              (v-buf& netlist cnt-width)
              (tv-if& netlist (make-tree data-width))
              (tv-if& netlist (make-tree cnt-width))))))

;; Sanity check

(local
 (defthmd check-shift-register2-piso$netlist-64-7
   (and (net-syntax-okp (shift-register2-piso$netlist 64 7))
        (net-arity-okp (shift-register2-piso$netlist 64 7))
        (shift-register2-piso& (shift-register2-piso$netlist 64 7) 64 7))))

;; Constraints on the state of SHIFT-REGISTER2-PISO

(defund shift-register2-piso$st-format (st data-width cnt-width)
  (b* ((r-reg0 (get-field *shift-register2-piso$r-reg0* st))
       (r-cnt0 (get-field *shift-register2-piso$r-cnt0* st))
       (w-reg0 (get-field *shift-register2-piso$w-reg0* st))
       (w-cnt0 (get-field *shift-register2-piso$w-cnt0* st))
       (r-reg1 (get-field *shift-register2-piso$r-reg1* st))
       (r-cnt1 (get-field *shift-register2-piso$r-cnt1* st))
       (w-reg1 (get-field *shift-register2-piso$w-reg1* st))
       (w-cnt1 (get-field *shift-register2-piso$w-cnt1* st)))
    (and (posp data-width)
         (natp cnt-width)
         (<= 3 cnt-width)
         (link$st-format r-reg0 data-width)
         (link$st-format r-cnt0 cnt-width)
         (link$st-format w-reg0 data-width)
         (link$st-format w-cnt0 cnt-width)
         (link$st-format r-reg1 data-width)
         (link$st-format r-cnt1 cnt-width)
         (link$st-format w-reg1 data-width)
         (link$st-format w-cnt1 cnt-width))))

(defthm shift-register2-piso$st-format=>contraints
  (implies (shift-register2-piso$st-format st data-width cnt-width)
           (and (posp data-width)
                (natp cnt-width)
                (<= 3 cnt-width)))
  :hints (("Goal" :in-theory (enable shift-register2-piso$st-format)))
  :rule-classes :forward-chaining)

(defund shift-register2-piso$valid-st (st data-width cnt-width)
  (b* ((r-reg0 (get-field *shift-register2-piso$r-reg0* st))
       (r-cnt0 (get-field *shift-register2-piso$r-cnt0* st))
       (w-reg0 (get-field *shift-register2-piso$w-reg0* st))
       (w-cnt0 (get-field *shift-register2-piso$w-cnt0* st))
       (r-reg1 (get-field *shift-register2-piso$r-reg1* st))
       (r-cnt1 (get-field *shift-register2-piso$r-cnt1* st))
       (w-reg1 (get-field *shift-register2-piso$w-reg1* st))
       (w-cnt1 (get-field *shift-register2-piso$w-cnt1* st)))
    (and (shift-register2-piso$st-format st data-width cnt-width)
         (equal data-width (expt 2 (1- cnt-width)))
         (link$valid-st r-reg0 data-width)
         (link$valid-st r-cnt0 cnt-width)
         (link$valid-st w-reg0 data-width)
         (link$valid-st w-cnt0 cnt-width)
         (link$valid-st r-reg1 data-width)
         (link$valid-st r-cnt1 cnt-width)
         (link$valid-st w-reg1 data-width)
         (link$valid-st w-cnt1 cnt-width))))

(local
 (defthm expt-linear-lower-<=-instance
   (implies (and (<= 2 n)
                 (integerp n))
            (<= 4 (expt 2 n)))
   :rule-classes :linear))

(defthmd shift-register2-piso$valid-st=>constraints
  (implies (shift-register2-piso$valid-st st data-width cnt-width)
           (and (natp data-width)
                (<= 4 data-width)
                (natp cnt-width)
                (<= 3 cnt-width)))
  :hints (("Goal" :in-theory (e/d (shift-register2-piso$valid-st)
                                  (shift-register2-piso$disabled-rules))))
  :rule-classes :forward-chaining)

(defthmd shift-register2-piso$valid-st=>st-format
  (implies (shift-register2-piso$valid-st st data-width cnt-width)
           (shift-register2-piso$st-format st data-width cnt-width))
  :hints (("Goal" :in-theory (enable shift-register2-piso$valid-st))))

;; Extract the input and output signals for SHIFT-REGISTER2-PISO

(progn
  ;; Extract the input data

  (defun shift-register2-piso$data0-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 3 inputs)))

  (defthm len-shift-register2-piso$data0-in
    (equal (len (shift-register2-piso$data0-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable shift-register2-piso$data0-in))

  (defun shift-register2-piso$data1-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (b* ((width (mbe :logic (nfix data-width)
                     :exec  data-width)))
      (take width
            (nthcdr (+ 3 width) inputs))))

  (defthm len-shift-register2-piso$data1-in
    (equal (len (shift-register2-piso$data1-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable shift-register2-piso$data1-in))

  ;; Extract the "in-act" signal

  (defund shift-register2-piso$in-act (inputs st data-width)
    (b* ((full-in (nth 0 inputs))
         (go-signals (nthcdr (shift-register2-piso$data-ins-len data-width)
                             inputs))
         (go-in (nth 0 go-signals))

         (r-reg0 (get-field *shift-register2-piso$r-reg0* st))
         (r-reg0.s (get-field *link$s* r-reg0))
         (r-cnt0 (get-field *shift-register2-piso$r-cnt0* st))
         (r-cnt0.s (get-field *link$s* r-cnt0))
         (r-cnt0.d (get-field *link$d* r-cnt0))
         (w-reg0 (get-field *shift-register2-piso$w-reg0* st))
         (w-reg0.s (get-field *link$s* w-reg0))
         (w-cnt0 (get-field *shift-register2-piso$w-cnt0* st))
         (w-cnt0.s (get-field *link$s* w-cnt0))

         (r-reg1 (get-field *shift-register2-piso$r-reg1* st))
         (r-reg1.s (get-field *link$s* r-reg1))
         (r-cnt1 (get-field *shift-register2-piso$r-cnt1* st))
         (r-cnt1.s (get-field *link$s* r-cnt1))
         (r-cnt1.d (get-field *link$d* r-cnt1))
         (w-reg1 (get-field *shift-register2-piso$w-reg1* st))
         (w-reg1.s (get-field *link$s* w-reg1))
         (w-cnt1 (get-field *shift-register2-piso$w-cnt1* st))
         (w-cnt1.s (get-field *link$s* w-cnt1))

         (r-cnt0=0 (f$fast-zero (strip-cars r-cnt0.d)))
         (r0-ready-in (f-and3 (car r-reg0.s) (car r-cnt0.s) r-cnt0=0))
         (w0-empty- (f-or (car w-reg0.s) (car w-cnt0.s)))

         (r-cnt1=0 (f$fast-zero (strip-cars r-cnt1.d)))
         (r1-ready-in (f-and3 (car r-reg1.s) (car r-cnt1.s) r-cnt1=0))
         (w1-empty- (f-or (car w-reg1.s) (car w-cnt1.s)))

         (shift-full-in (f-and3 full-in r0-ready-in r1-ready-in))
         (w0+1-empty- (f-or w0-empty- w1-empty-)))
      (joint-act shift-full-in w0+1-empty- go-in)))

  (defthm shift-register2-piso$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (shift-register2-piso$in-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable f-and3
                                       shift-register2-piso$in-act))))

  ;; Extract the "out0-act" signal

  (defund shift-register2-piso$out0-act (inputs st data-width)
    (b* ((empty-out0- (nth 1 inputs))
         (go-signals (nthcdr (shift-register2-piso$data-ins-len data-width)
                             inputs))
         (go-out0 (nth 1 go-signals))

         (r-reg0 (get-field *shift-register2-piso$r-reg0* st))
         (r-reg0.s (get-field *link$s* r-reg0))
         (r-cnt0 (get-field *shift-register2-piso$r-cnt0* st))
         (r-cnt0.s (get-field *link$s* r-cnt0))
         (r-cnt0.d (get-field *link$d* r-cnt0))
         (w-reg0 (get-field *shift-register2-piso$w-reg0* st))
         (w-reg0.s (get-field *link$s* w-reg0))
         (w-cnt0 (get-field *shift-register2-piso$w-cnt0* st))
         (w-cnt0.s (get-field *link$s* w-cnt0))

         (r-cnt0=0~ (f-not (f$fast-zero (strip-cars r-cnt0.d))))
         (r0-full (f-and3 (car r-reg0.s) (car r-cnt0.s) r-cnt0=0~))
         (w0-empty- (f-or (car w-reg0.s) (car w-cnt0.s)))
         (shift-empty-out0- (f-or empty-out0- w0-empty-)))
      (joint-act r0-full shift-empty-out0- go-out0)))

  (defthm shift-register2-piso$out0-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (shift-register2-piso$out0-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable shift-register2-piso$out0-act))))

  ;; Extract the "out1-act" signal

  (defund shift-register2-piso$out1-act (inputs st data-width)
    (b* ((empty-out1- (nth 2 inputs))
         (go-signals (nthcdr (shift-register2-piso$data-ins-len data-width)
                             inputs))
         (go-out1 (nth 2 go-signals))

         (r-reg1 (get-field *shift-register2-piso$r-reg1* st))
         (r-reg1.s (get-field *link$s* r-reg1))
         (r-cnt1 (get-field *shift-register2-piso$r-cnt1* st))
         (r-cnt1.s (get-field *link$s* r-cnt1))
         (r-cnt1.d (get-field *link$d* r-cnt1))
         (w-reg1 (get-field *shift-register2-piso$w-reg1* st))
         (w-reg1.s (get-field *link$s* w-reg1))
         (w-cnt1 (get-field *shift-register2-piso$w-cnt1* st))
         (w-cnt1.s (get-field *link$s* w-cnt1))

         (r-cnt1=0~ (f-not (f$fast-zero (strip-cars r-cnt1.d))))
         (r1-full (f-and3 (car r-reg1.s) (car r-cnt1.s) r-cnt1=0~))
         (w1-empty- (f-or (car w-reg1.s) (car w-cnt1.s)))
         (shift-empty-out1- (f-or empty-out1- w1-empty-)))
      (joint-act r1-full shift-empty-out1- go-out1)))

  (defthm shift-register2-piso$out1-act-inactive
    (implies (equal (nth 2 inputs) t)
             (not (shift-register2-piso$out1-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable shift-register2-piso$out1-act))))

  (local
   (defthm booleanp-f$fast-zero
     (implies (bvp v)
              (booleanp (f$fast-zero v)))
     :hints (("Goal" :in-theory (enable f-gates f$fast-zero)))
     :rule-classes :type-prescription))

  (defthm shift-register2-piso$in-out-acts-mutually-exclusive
    (implies (and (shift-register2-piso$valid-st st data-width cnt-width)
                  (shift-register2-piso$in-act inputs st data-width))
             (and (not (shift-register2-piso$out0-act inputs st data-width))
                  (not (shift-register2-piso$out1-act inputs st data-width))))
    :hints (("Goal" :in-theory (e/d (f-and3
                                     shift-register2-piso$valid-st
                                     shift-register2-piso$in-act
                                     shift-register2-piso$out0-act
                                     shift-register2-piso$out1-act)
                                    (link$st-format
                                     shift-register2-piso$disabled-rules)))))

  ;; Extract the output data

  (defund shift-register2-piso$bit0-out (st)
    (b* ((r-reg0 (get-field *shift-register2-piso$r-reg0* st))
         (r-reg0.d (get-field *link$d* r-reg0)))
      (f-buf (car (strip-cars r-reg0.d)))))

  (defthm booleanp-shift-register2-piso$bit0-out
    (implies (and (shift-register2-piso$valid-st st data-width cnt-width)
                  (shift-register2-piso$out0-act inputs st data-width))
             (booleanp (shift-register2-piso$bit0-out st)))
    :hints (("Goal" :in-theory (e/d (f-and3
                                     shift-register2-piso$valid-st
                                     shift-register2-piso$out0-act
                                     shift-register2-piso$bit0-out)
                                    (link$st-format
                                     shift-register2-piso$disabled-rules))))
    :rule-classes :type-prescription)

  (defund shift-register2-piso$bit1-out (st)
    (b* ((r-reg1 (get-field *shift-register2-piso$r-reg1* st))
         (r-reg1.d (get-field *link$d* r-reg1)))
      (f-buf (car (strip-cars r-reg1.d)))))

  (defthm booleanp-shift-register2-piso$bit1-out
    (implies (and (shift-register2-piso$valid-st st data-width cnt-width)
                  (shift-register2-piso$out1-act inputs st data-width))
             (booleanp (shift-register2-piso$bit1-out st)))
    :hints (("Goal" :in-theory (e/d (f-and3
                                     shift-register2-piso$valid-st
                                     shift-register2-piso$out1-act
                                     shift-register2-piso$bit1-out)
                                    (link$st-format
                                     shift-register2-piso$disabled-rules))))
    :rule-classes :type-prescription)

  (defun shift-register2-piso$outputs (inputs st data-width)
    (list (shift-register2-piso$in-act inputs st data-width)
          (shift-register2-piso$out0-act inputs st data-width)
          (shift-register2-piso$out1-act inputs st data-width)
          (shift-register2-piso$bit0-out st)
          (shift-register2-piso$bit1-out st)))
  )

;; Prove that SHIFT-REGISTER2-PISO is not a DE primitive.

(not-primp-lemma shift-register2-piso)

;; The value lemma for SHIFT-REGISTER2-PISO

(defthm shift-register2-piso$value
  (b* ((inputs (list* full-in empty-out0- empty-out1-
                      (append data0-in data1-in go-signals))))
    (implies
     (and (shift-register2-piso& netlist data-width cnt-width)
          (true-listp data0-in)
          (equal (len data0-in) data-width)
          (true-listp data1-in)
          (equal (len data1-in) data-width)
          (true-listp go-signals)
          (equal (len go-signals) *shift-register2-piso$go-num*)
          (shift-register2-piso$st-format st data-width cnt-width))
     (equal (se (si 'shift-register2-piso data-width) inputs st netlist)
            (shift-register2-piso$outputs inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'shift-register2-piso data-width)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            shift-register2-piso&
                            shift-register2-piso*$destructure
                            shift-register2-piso$data0-in
                            shift-register2-piso$data1-in
                            shift-register2-piso$st-format
                            shift-register2-piso$in-act
                            shift-register2-piso$out0-act
                            shift-register2-piso$out1-act
                            shift-register2-piso$bit0-out
                            shift-register2-piso$bit1-out)
                           (shift-register2-piso$disabled-rules
                            de-module-disabled-rules)))))

;; This function specifies the next state of SHIFT-REGISTER2-PISO.

(defun shift-register2-piso$step (inputs st data-width cnt-width)
  (b* ((data0-in   (shift-register2-piso$data0-in inputs data-width))
       (data1-in   (shift-register2-piso$data1-in inputs data-width))
       (go-signals (nthcdr (shift-register2-piso$data-ins-len data-width)
                           inputs))
       (go-buf0 (nth 3 go-signals))
       (go-buf1 (nth 4 go-signals))

       (r-reg0 (get-field *shift-register2-piso$r-reg0* st))
       (r-reg0.s (get-field *link$s* r-reg0))
       (r-reg0.d (get-field *link$d* r-reg0))
       (r-cnt0 (get-field *shift-register2-piso$r-cnt0* st))
       (r-cnt0.s (get-field *link$s* r-cnt0))
       (r-cnt0.d (get-field *link$d* r-cnt0))
       (w-reg0 (get-field *shift-register2-piso$w-reg0* st))
       (w-reg0.s (get-field *link$s* w-reg0))
       (w-reg0.d (get-field *link$d* w-reg0))
       (w-cnt0 (get-field *shift-register2-piso$w-cnt0* st))
       (w-cnt0.s (get-field *link$s* w-cnt0))
       (w-cnt0.d (get-field *link$d* w-cnt0))

       (r-reg1 (get-field *shift-register2-piso$r-reg1* st))
       (r-reg1.s (get-field *link$s* r-reg1))
       (r-reg1.d (get-field *link$d* r-reg1))
       (r-cnt1 (get-field *shift-register2-piso$r-cnt1* st))
       (r-cnt1.s (get-field *link$s* r-cnt1))
       (r-cnt1.d (get-field *link$d* r-cnt1))
       (w-reg1 (get-field *shift-register2-piso$w-reg1* st))
       (w-reg1.s (get-field *link$s* w-reg1))
       (w-reg1.d (get-field *link$d* w-reg1))
       (w-cnt1 (get-field *shift-register2-piso$w-cnt1* st))
       (w-cnt1.s (get-field *link$s* w-cnt1))
       (w-cnt1.d (get-field *link$d* w-cnt1))

       (r-cnt0=0 (f$fast-zero (strip-cars r-cnt0.d)))
       (r-cnt1=0 (f$fast-zero (strip-cars r-cnt1.d)))

       (in-act (shift-register2-piso$in-act inputs st data-width))
       (out0-act (shift-register2-piso$out0-act inputs st data-width))
       (out1-act (shift-register2-piso$out1-act inputs st data-width))

       (shift0-act (f-or in-act out0-act))
       (shift1-act (f-or in-act out1-act))

       (buf0-full-in (f-and (car w-reg0.s) (car w-cnt0.s)))
       (buf0-empty-out- (f-or (car r-reg0.s) (car r-cnt0.s)))
       (buf0-act (joint-act buf0-full-in buf0-empty-out- go-buf0))

       (buf1-full-in (f-and (car w-reg1.s) (car w-cnt1.s)))
       (buf1-empty-out- (f-or (car r-reg1.s) (car r-cnt1.s)))
       (buf1-act (joint-act buf1-full-in buf1-empty-out- go-buf1))

       (r-reg0-inputs (list* buf0-act shift0-act (strip-cars w-reg0.d)))
       (r-cnt0-inputs (list* buf0-act shift0-act (strip-cars w-cnt0.d)))
       (w-reg0-inputs (list* shift0-act buf0-act
                             (fv-if r-cnt0=0
                                    data0-in
                                    (append (nthcdr 1 (v-threefix
                                                       (strip-cars r-reg0.d)))
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

       (r-reg1-inputs (list* buf1-act shift1-act (strip-cars w-reg1.d)))
       (r-cnt1-inputs (list* buf1-act shift1-act (strip-cars w-cnt1.d)))
       (w-reg1-inputs (list* shift1-act buf1-act
                             (fv-if r-cnt1=0
                                    data1-in
                                    (append (nthcdr 1 (v-threefix
                                                       (strip-cars r-reg1.d)))
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
     ;; R-REG0
     (link$step r-reg0-inputs r-reg0 data-width)
     ;; R-CNT0
     (link$step r-cnt0-inputs r-cnt0 cnt-width)
     ;; W-REG0
     (link$step w-reg0-inputs w-reg0 data-width)
     ;; W-CNT0
     (link$step w-cnt0-inputs w-cnt0 cnt-width)
     ;; R-REG1
     (link$step r-reg1-inputs r-reg1 data-width)
     ;; R-CNT1
     (link$step r-cnt1-inputs r-cnt1 cnt-width)
     ;; W-REG1
     (link$step w-reg1-inputs w-reg1 data-width)
     ;; W-CNT1
     (link$step w-cnt1-inputs w-cnt1 cnt-width))))

(defthm len-of-shift-register2-piso$step
  (equal (len (shift-register2-piso$step inputs st data-width cnt-width))
         *shift-register2-piso$st-len*))

;; The state lemma for SHIFT-REGISTER2-PISO

(defthm shift-register2-piso$state
  (b* ((inputs (list* full-in empty-out0- empty-out1-
                      (append data0-in data1-in go-signals))))
    (implies
     (and (shift-register2-piso& netlist data-width cnt-width)
          (true-listp data0-in)
          (equal (len data0-in) data-width)
          (true-listp data1-in)
          (equal (len data1-in) data-width)
          (true-listp go-signals)
          (equal (len go-signals) *shift-register2-piso$go-num*)
          (shift-register2-piso$st-format st data-width cnt-width))
     (equal (de (si 'shift-register2-piso data-width) inputs st netlist)
            (shift-register2-piso$step inputs st data-width cnt-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'shift-register2-piso data-width)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            shift-register2-piso&
                            shift-register2-piso*$destructure
                            shift-register2-piso$data0-in
                            shift-register2-piso$data1-in
                            shift-register2-piso$in-act
                            shift-register2-piso$out0-act
                            shift-register2-piso$out1-act
                            shift-register2-piso$st-format)
                           (shift-register2-piso$disabled-rules
                            de-module-disabled-rules)))))

(in-theory (disable shift-register2-piso$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund shift-register2-piso$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in     (nth 0 inputs))
       (empty-out0- (nth 1 inputs))
       (empty-out1- (nth 2 inputs))
       (data0-in    (shift-register2-piso$data0-in inputs data-width))
       (data1-in    (shift-register2-piso$data1-in inputs data-width))
       (go-signals  (nthcdr (shift-register2-piso$data-ins-len data-width)
                            inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out0-)
     (booleanp empty-out1-)
     (or (not full-in)
         (and (bvp data0-in) (bvp data1-in)))
     (true-listp go-signals)
     (= (len go-signals) *shift-register2-piso$go-num*)
     (equal inputs
            (list* full-in empty-out0- empty-out1-
                   (append data0-in data1-in go-signals))))))

(local
 (defthm shift-register2-piso$input-format-lemma-1
   (implies (shift-register2-piso$input-format inputs data-width)
            (booleanp (nth 0 inputs)))
   :hints (("Goal" :in-theory (enable shift-register2-piso$input-format)))
   :rule-classes :type-prescription))

(local
 (defthm shift-register2-piso$input-format-lemma-2
   (implies (shift-register2-piso$input-format inputs data-width)
            (booleanp (nth 1 inputs)))
   :hints (("Goal" :in-theory (enable shift-register2-piso$input-format)))
   :rule-classes :type-prescription))

(local
 (defthm shift-register2-piso$input-format-lemma-3
   (implies (shift-register2-piso$input-format inputs data-width)
            (booleanp (nth 2 inputs)))
   :hints (("Goal" :in-theory (enable shift-register2-piso$input-format)))
   :rule-classes :type-prescription))

(local
 (defthm shift-register2-piso$input-format-lemma-4
   (implies (and (shift-register2-piso$input-format inputs data-width)
                 (nth 0 inputs))
            (and (bvp (shift-register2-piso$data0-in inputs data-width))
                 (bvp (shift-register2-piso$data1-in inputs data-width))))
   :hints (("Goal" :in-theory (enable shift-register2-piso$input-format)))))

(defthm booleanp-shift-register2-piso$in-act
  (implies (and (shift-register2-piso$input-format inputs data-width)
                (shift-register2-piso$valid-st st data-width cnt-width))
           (booleanp (shift-register2-piso$in-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (e/d (f-and3
                            shift-register2-piso$valid-st
                            shift-register2-piso$in-act)
                           (shift-register2-piso$disabled-rules
                            link$st-format))))
  :rule-classes :type-prescription)

(defthm booleanp-shift-register2-piso$out0-act
  (implies (and (shift-register2-piso$input-format inputs data-width)
                (shift-register2-piso$valid-st st data-width cnt-width))
           (booleanp (shift-register2-piso$out0-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (e/d (f-and3
                            shift-register2-piso$valid-st
                            shift-register2-piso$out0-act)
                           (shift-register2-piso$disabled-rules
                            link$st-format))))
  :rule-classes :type-prescription)

(defthm booleanp-shift-register2-piso$out1-act
  (implies (and (shift-register2-piso$input-format inputs data-width)
                (shift-register2-piso$valid-st st data-width cnt-width))
           (booleanp (shift-register2-piso$out1-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (e/d (f-and3
                            shift-register2-piso$valid-st
                            shift-register2-piso$out1-act)
                           (shift-register2-piso$disabled-rules
                            link$st-format))))
  :rule-classes :type-prescription)

(simulate-lemma shift-register2-piso :sizes (data-width cnt-width))

;; ======================================================================

;; 3. Single-Step-Update Property

;; Specify the functionality of SHIFT-REGISTER2-PISO

(defun shift-register2-piso$op (x)
  (rev x))

(defthm append-of-shift-register2-piso$op-with-singleton
  (equal (append (shift-register2-piso$op x) (list a))
         (shift-register2-piso$op (cons a x))))

(in-theory (disable shift-register2-piso$op))

;; The operation of SHIFT-REGISTER2-PISO over a data sequence

(defun shift-register2-piso$op-map (x)
  (if (atom x)
      nil
    (append (shift-register2-piso$op (car x))
            (shift-register2-piso$op-map (cdr x)))))

(defthm shift-register2-piso$op-map-of-append
  (equal (shift-register2-piso$op-map (append x y))
         (append (shift-register2-piso$op-map x)
                 (shift-register2-piso$op-map y))))

;; The extraction function for SHIFT-REGISTER2-PISO

(defund shift-register2-piso$extract0 (st)
  (b* ((r-reg0 (get-field *shift-register2-piso$r-reg0* st))
       (r-reg0.s (get-field *link$s* r-reg0))
       (r-reg0.d (get-field *link$d* r-reg0))
       (r-cnt0 (get-field *shift-register2-piso$r-cnt0* st))
       (r-cnt0.d (get-field *link$d* r-cnt0))
       (w-reg0 (get-field *shift-register2-piso$w-reg0* st))
       (w-reg0.d (get-field *link$d* w-reg0))
       (w-cnt0 (get-field *shift-register2-piso$w-cnt0* st))
       (w-cnt0.d (get-field *link$d* w-cnt0)))
    (if (fullp r-reg0.s)
        (take (v-to-nat (strip-cars r-cnt0.d))
              (strip-cars r-reg0.d))
      (take (v-to-nat (strip-cars w-cnt0.d))
            (strip-cars w-reg0.d)))))

(defund shift-register2-piso$extract1 (st)
  (b* ((r-reg1 (get-field *shift-register2-piso$r-reg1* st))
       (r-reg1.s (get-field *link$s* r-reg1))
       (r-reg1.d (get-field *link$d* r-reg1))
       (r-cnt1 (get-field *shift-register2-piso$r-cnt1* st))
       (r-cnt1.d (get-field *link$d* r-cnt1))
       (w-reg1 (get-field *shift-register2-piso$w-reg1* st))
       (w-reg1.d (get-field *link$d* w-reg1))
       (w-cnt1 (get-field *shift-register2-piso$w-cnt1* st))
       (w-cnt1.d (get-field *link$d* w-cnt1)))
    (if (fullp r-reg1.s)
        (take (v-to-nat (strip-cars r-cnt1.d))
              (strip-cars r-reg1.d))
      (take (v-to-nat (strip-cars w-cnt1.d))
            (strip-cars w-reg1.d)))))

(local
 (defthm v-to-nat-of-v-zp
   (equal (v-zp x)
          (equal (v-to-nat x) 0))
   :hints (("Goal" :in-theory (enable v-zp v-nzp v-to-nat)))))

(defthm shift-register2-piso$extract0-not-empty
  (implies (and (shift-register2-piso$out0-act inputs st data-width)
                (shift-register2-piso$valid-st st data-width cnt-width))
           (< 0 (len (shift-register2-piso$extract0 st))))
  :hints (("Goal"
           :in-theory (e/d (f-and3
                            shift-register2-piso$valid-st
                            shift-register2-piso$extract0
                            shift-register2-piso$out0-act)
                           (acl2::default-expt-2))))
  :rule-classes :linear)

(defthm shift-register2-piso$extract1-not-empty
  (implies (and (shift-register2-piso$out1-act inputs st data-width)
                (shift-register2-piso$valid-st st data-width cnt-width))
           (< 0 (len (shift-register2-piso$extract1 st))))
  :hints (("Goal"
           :in-theory (e/d (f-and3
                            shift-register2-piso$valid-st
                            shift-register2-piso$extract1
                            shift-register2-piso$out1-act)
                           (acl2::default-expt-2))))
  :rule-classes :linear)

(defthmd lens-of-shift-register2-piso$extracts-lemma
  (implies (and (shift-register2-piso$in-act inputs st data-width)
                (shift-register2-piso$valid-st st data-width cnt-width))
           (and (equal (len (shift-register2-piso$extract0 st))
                       0)
                (equal (len (shift-register2-piso$extract1 st))
                       0)))
  :hints (("Goal" :in-theory (e/d (f-and3
                                   shift-register2-piso$valid-st
                                   shift-register2-piso$in-act
                                   shift-register2-piso$extract0
                                   shift-register2-piso$extract1)
                                  (acl2::default-expt-2)))))

(defthm lens-of-shift-register2-piso$extracts-contrapositive-lemma-1
  (implies (and (shift-register2-piso$in-act inputs st data-width)
                (or (< 0 (len (shift-register2-piso$extract0 st)))
                    (< 0 (len (shift-register2-piso$extract1 st)))))
           (not (shift-register2-piso$valid-st st data-width cnt-width)))
  :hints (("Goal" :in-theory (e/d (f-and3
                                   shift-register2-piso$valid-st
                                   shift-register2-piso$in-act
                                   shift-register2-piso$extract0
                                   shift-register2-piso$extract1)
                                  (acl2::default-expt-2)))))

(defthm lens-of-shift-register2-piso$extracts-contrapositive-lemma-2
  (implies (and (shift-register2-piso$valid-st st data-width cnt-width)
                (or (< 0 (len (shift-register2-piso$extract0 st)))
                    (< 0 (len (shift-register2-piso$extract1 st)))))
           (not (shift-register2-piso$in-act inputs st data-width)))
  :hints (("Goal" :in-theory (e/d (f-and3
                                   shift-register2-piso$valid-st
                                   shift-register2-piso$in-act
                                   shift-register2-piso$extract0
                                   shift-register2-piso$extract1)
                                  (acl2::default-expt-2)))))

;; Specify and prove a state invariant

(progn
  (defund shift-register2-piso$inv (st)
    (b* ((r-reg0 (get-field *shift-register2-piso$r-reg0* st))
         (r-reg0.s (get-field *link$s* r-reg0))
         (r-reg0.d (get-field *link$d* r-reg0))
         (r-cnt0 (get-field *shift-register2-piso$r-cnt0* st))
         (r-cnt0.s (get-field *link$s* r-cnt0))
         (r-cnt0.d (get-field *link$d* r-cnt0))
         (w-reg0 (get-field *shift-register2-piso$w-reg0* st))
         (w-reg0.s (get-field *link$s* w-reg0))
         (w-reg0.d (get-field *link$d* w-reg0))
         (w-cnt0 (get-field *shift-register2-piso$w-cnt0* st))
         (w-cnt0.s (get-field *link$s* w-cnt0))
         (w-cnt0.d (get-field *link$d* w-cnt0))

         (r-reg1 (get-field *shift-register2-piso$r-reg1* st))
         (r-reg1.s (get-field *link$s* r-reg1))
         (r-reg1.d (get-field *link$d* r-reg1))
         (r-cnt1 (get-field *shift-register2-piso$r-cnt1* st))
         (r-cnt1.s (get-field *link$s* r-cnt1))
         (r-cnt1.d (get-field *link$d* r-cnt1))
         (w-reg1 (get-field *shift-register2-piso$w-reg1* st))
         (w-reg1.s (get-field *link$s* w-reg1))
         (w-reg1.d (get-field *link$d* w-reg1))
         (w-cnt1 (get-field *shift-register2-piso$w-cnt1* st))
         (w-cnt1.s (get-field *link$s* w-cnt1))
         (w-cnt1.d (get-field *link$d* w-cnt1)))
      (and (equal r-reg0.s r-cnt0.s)
           (equal w-reg0.s w-cnt0.s)
           (not (equal r-reg0.s w-reg0.s))

           (or (emptyp r-cnt0.s)
               (<= (v-to-nat (strip-cars r-cnt0.d))
                   (len r-reg0.d)))
           (or (emptyp w-cnt0.s)
               (<= (v-to-nat (strip-cars w-cnt0.d))
                   (len w-reg0.d)))

           (equal r-reg1.s r-cnt1.s)
           (equal w-reg1.s w-cnt1.s)
           (not (equal r-reg1.s w-reg1.s))

           (or (emptyp r-cnt1.s)
               (<= (v-to-nat (strip-cars r-cnt1.d))
                   (len r-reg1.d)))
           (or (emptyp w-cnt1.s)
               (<= (v-to-nat (strip-cars w-cnt1.d))
                   (len w-reg1.d))))))

  (defthm lens-of-shift-register2-piso$extracts-upper-bound
    (implies (and (shift-register2-piso$valid-st st data-width cnt-width)
                  (shift-register2-piso$inv st))
             (and (<= (len (shift-register2-piso$extract0 st))
                      data-width)
                  (<= (len (shift-register2-piso$extract1 st))
                      data-width)))
    :hints (("Goal" :in-theory (e/d (shift-register2-piso$valid-st
                                     shift-register2-piso$inv
                                     shift-register2-piso$extract0
                                     shift-register2-piso$extract1)
                                    (shift-register2-piso$disabled-rules))))
    :rule-classes :linear)

  (local
   (defthm v-to-nat-of-repeat-lemma
     (equal (v-to-nat (append (repeat n nil) '(t)))
            (expt 2 (nfix n)))
     :hints (("Goal" :in-theory (enable v-to-nat repeat)))))

  (defthm shift-register2-piso$inv-preserved
    (implies (and (shift-register2-piso$input-format inputs data-width)
                  (shift-register2-piso$valid-st st data-width cnt-width)
                  (shift-register2-piso$inv st))
             (shift-register2-piso$inv
              (shift-register2-piso$step inputs st data-width cnt-width)))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              bvp
                              shift-register2-piso$valid-st
                              shift-register2-piso$inv
                              shift-register2-piso$step
                              shift-register2-piso$in-act
                              shift-register2-piso$out0-act
                              shift-register2-piso$out1-act)
                             (shift-register2-piso$disabled-rules)))))
  )

;; The extracted next-state function for SHIFT-REGISTER2-PISO.  Note that this
;; function avoids exploring the internal computation of SHIFT-REGISTER2-PISO.

(defund shift-register2-piso$extracted0-step (inputs st data-width)
  (b* ((data (shift-register2-piso$data0-in inputs data-width))
       (extracted-st (shift-register2-piso$extract0 st)))
    (cond
     ((equal (shift-register2-piso$out0-act inputs st data-width) t)
      (cdr extracted-st))
     ((equal (shift-register2-piso$in-act inputs st data-width) t)
      data)
     (t extracted-st))))

(defund shift-register2-piso$extracted1-step (inputs st data-width)
  (b* ((data (shift-register2-piso$data1-in inputs data-width))
       (extracted-st (shift-register2-piso$extract1 st)))
    (cond
     ((equal (shift-register2-piso$out1-act inputs st data-width) t)
      (cdr extracted-st))
     ((equal (shift-register2-piso$in-act inputs st data-width) t)
      data)
     (t extracted-st))))

;; The single-step-update property

(progn
  (local
   (defthm len-cdr
     (implies (< 0 (len x))
              (equal (len (cdr x))
                     (1- (len x))))))

  (defthm shift-register2-piso$extracted-step-correct
    (b* ((next-st (shift-register2-piso$step inputs st data-width cnt-width)))
      (implies (and (shift-register2-piso$input-format inputs data-width)
                    (shift-register2-piso$valid-st st data-width cnt-width)
                    (shift-register2-piso$inv st))
               (and
                (equal (shift-register2-piso$extract0 next-st)
                       (shift-register2-piso$extracted0-step
                        inputs st data-width))
                (equal (shift-register2-piso$extract1 next-st)
                       (shift-register2-piso$extracted1-step
                        inputs st data-width)))))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              bvp
                              pos-len=>cons
                              shift-register2-piso$extracted0-step
                              shift-register2-piso$extracted1-step
                              shift-register2-piso$valid-st
                              shift-register2-piso$inv
                              shift-register2-piso$step
                              shift-register2-piso$in-act
                              shift-register2-piso$out0-act
                              shift-register2-piso$out1-act
                              shift-register2-piso$extract0
                              shift-register2-piso$extract1)
                             (shift-register2-piso$disabled-rules)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that shift-register2-piso$valid-st is an invariant.

(encapsulate
  ()

  (local
   (defthm shift-register2-piso$valid-st-preserved-aux
     (implies (len-1-true-listp x)
              (len-1-true-listp (cons (list e) x)))
     :hints (("Goal" :in-theory (enable len-1-true-listp)))))

  (defthm shift-register2-piso$valid-st-preserved
    (implies (and (shift-register2-piso$input-format inputs data-width)
                  (shift-register2-piso$valid-st st data-width cnt-width))
             (shift-register2-piso$valid-st
              (shift-register2-piso$step inputs st data-width cnt-width)
              data-width
              cnt-width))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              f-and3
                              bvp
                              pos-len=>cons
                              shift-register2-piso$st-format
                              shift-register2-piso$valid-st
                              shift-register2-piso$step
                              shift-register2-piso$in-act
                              shift-register2-piso$out0-act
                              shift-register2-piso$out1-act)
                             (shift-register2-piso$disabled-rules)))))
  )

(defthm shift-register2-piso$extract0-lemma
  (implies (and (shift-register2-piso$out0-act inputs st data-width)
                (shift-register2-piso$valid-st st data-width cnt-width))
           (equal (shift-register2-piso$bit0-out st)
                  (car (shift-register2-piso$extract0 st))))
  :hints (("Goal" :in-theory (e/d (f-and3
                                   booleanp-car-of-bv
                                   shift-register2-piso$out0-act
                                   shift-register2-piso$valid-st
                                   shift-register2-piso$bit0-out
                                   shift-register2-piso$extract0)
                                  (acl2::default-expt-2)))))

(defthm booleanp-car-of-shift-register2-piso$extract0
  (implies (and (shift-register2-piso$out0-act inputs st data-width)
                (shift-register2-piso$valid-st st data-width cnt-width))
           (booleanp (car (shift-register2-piso$extract0 st))))
  :hints (("Goal"
           :use shift-register2-piso$extract0-lemma
           :in-theory (e/d ()
                           (shift-register2-piso$extract0-lemma))))
  :rule-classes :type-prescription)

(defthm shift-register2-piso$extract1-lemma
  (implies (and (shift-register2-piso$out1-act inputs st data-width)
                (shift-register2-piso$valid-st st data-width cnt-width))
           (equal (shift-register2-piso$bit1-out st)
                  (car (shift-register2-piso$extract1 st))))
  :hints (("Goal" :in-theory (e/d (f-and3
                                   booleanp-car-of-bv
                                   shift-register2-piso$out1-act
                                   shift-register2-piso$valid-st
                                   shift-register2-piso$bit1-out
                                   shift-register2-piso$extract1)
                                  (acl2::default-expt-2)))))

(defthm booleanp-car-of-shift-register2-piso$extract1
  (implies (and (shift-register2-piso$out1-act inputs st data-width)
                (shift-register2-piso$valid-st st data-width cnt-width))
           (booleanp (car (shift-register2-piso$extract1 st))))
  :hints (("Goal"
           :use shift-register2-piso$extract1-lemma
           :in-theory (e/d ()
                           (shift-register2-piso$extract1-lemma))))
  :rule-classes :type-prescription)

;; Extract the accepted input sequences

(seq-gen shift-register2-piso in in-act 0
         (cons (shift-register2-piso$data0-in inputs data-width)
               (shift-register2-piso$data1-in inputs data-width))
         :sizes (data-width cnt-width))

(seq-gen shift-register2-piso in0 in-act 0
         (shift-register2-piso$data0-in inputs data-width)
         :sizes (data-width cnt-width))

(seq-gen shift-register2-piso in1 in-act 0
         (shift-register2-piso$data1-in inputs data-width)
         :sizes (data-width cnt-width))

;; Extract the valid output sequences

(seq-gen shift-register2-piso out0 out0-act 1
         (shift-register2-piso$bit0-out st)
         :netlist-data (nth 3 outputs)
         :sizes (data-width cnt-width))

(seq-gen shift-register2-piso out1 out1-act 2
         (shift-register2-piso$bit1-out st)
         :netlist-data (nth 4 outputs)
         :sizes (data-width cnt-width))

;; The multi-step input-output relationship

(encapsulate
  ()

  (local
   (defthm shift-register2-piso$op-of-len-0
     (implies (equal (len x) 0)
              (not (shift-register2-piso$op x)))
     :hints (("Goal" :in-theory (enable shift-register2-piso$op)))))

  (local
   (defthm shift-register2-piso$dataflow-correct-aux
     (implies (equal (append x y1)
                     (append (shift-register2-piso$op-map seq) y2))
              (equal (append x y1 z)
                     (append (shift-register2-piso$op-map seq)
                             y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (acl2::associativity-of-append))))))

  (defthmd shift-register2-piso$dataflow0-correct
    (b* ((extracted-st (shift-register2-piso$extract0 st))
         (final-st (shift-register2-piso$run
                    inputs-seq st data-width cnt-width n))
         (final-extracted-st (shift-register2-piso$extract0 final-st)))
      (implies
       (and (shift-register2-piso$input-format-n inputs-seq data-width n)
            (shift-register2-piso$valid-st st data-width cnt-width)
            (shift-register2-piso$inv st))
       (equal (append (shift-register2-piso$op final-extracted-st)
                      (shift-register2-piso$out0-seq
                       inputs-seq st data-width cnt-width n))
              (append (shift-register2-piso$op-map
                       (shift-register2-piso$in0-seq
                        inputs-seq st data-width cnt-width n))
                      (shift-register2-piso$op extracted-st)))))
    :hints (("Goal"
             :in-theory (enable pos-len=>cons
                                lens-of-shift-register2-piso$extracts-lemma
                                shift-register2-piso$extracted0-step))))

  (defthmd shift-register2-piso$dataflow1-correct
    (b* ((extracted-st (shift-register2-piso$extract1 st))
         (final-st (shift-register2-piso$run
                    inputs-seq st data-width cnt-width n))
         (final-extracted-st (shift-register2-piso$extract1 final-st)))
      (implies
       (and (shift-register2-piso$input-format-n inputs-seq data-width n)
            (shift-register2-piso$valid-st st data-width cnt-width)
            (shift-register2-piso$inv st))
       (equal (append (shift-register2-piso$op final-extracted-st)
                      (shift-register2-piso$out1-seq
                       inputs-seq st data-width cnt-width n))
              (append (shift-register2-piso$op-map
                       (shift-register2-piso$in1-seq
                        inputs-seq st data-width cnt-width n))
                      (shift-register2-piso$op extracted-st)))))
    :hints (("Goal"
             :in-theory (enable pos-len=>cons
                                lens-of-shift-register2-piso$extracts-lemma
                                shift-register2-piso$extracted1-step))))

  (defthmd shift-register2-piso$functionally-correct-1
    (b* ((extracted-st (shift-register2-piso$extract0 st))
         (final-st (de-n (si 'shift-register2-piso data-width)
                         inputs-seq st netlist n))
         (final-extracted-st (shift-register2-piso$extract0 final-st)))
      (implies
       (and (shift-register2-piso& netlist data-width cnt-width)
            (shift-register2-piso$input-format-n inputs-seq data-width n)
            (shift-register2-piso$valid-st st data-width cnt-width)
            (shift-register2-piso$inv st))
       (equal (append (shift-register2-piso$op final-extracted-st)
                      (shift-register2-piso$netlist-out0-seq
                       inputs-seq st netlist data-width n))
              (append (shift-register2-piso$op-map
                       (shift-register2-piso$netlist-in0-seq
                        inputs-seq st netlist data-width n))
                      (shift-register2-piso$op extracted-st)))))
    :hints (("Goal"
             :use shift-register2-piso$dataflow0-correct
             :in-theory (enable shift-register2-piso$valid-st=>st-format
                                shift-register2-piso$de-n))))

  (defthmd shift-register2-piso$functionally-correct-2
    (b* ((extracted-st (shift-register2-piso$extract1 st))
         (final-st (de-n (si 'shift-register2-piso data-width)
                         inputs-seq st netlist n))
         (final-extracted-st (shift-register2-piso$extract1 final-st)))
      (implies
       (and (shift-register2-piso& netlist data-width cnt-width)
            (shift-register2-piso$input-format-n inputs-seq data-width n)
            (shift-register2-piso$valid-st st data-width cnt-width)
            (shift-register2-piso$inv st))
       (equal (append (shift-register2-piso$op final-extracted-st)
                      (shift-register2-piso$netlist-out1-seq
                       inputs-seq st netlist data-width n))
              (append (shift-register2-piso$op-map
                       (shift-register2-piso$netlist-in1-seq
                        inputs-seq st netlist data-width n))
                      (shift-register2-piso$op extracted-st)))))
    :hints (("Goal"
             :use shift-register2-piso$dataflow1-correct
             :in-theory (enable shift-register2-piso$valid-st=>st-format
                                shift-register2-piso$de-n))))
  )

