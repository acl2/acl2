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

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of SHIFT-REGISTER-SIPO
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of SHIFT-REGISTER-SIPO
;;
;; Construct a DE module generator that generates self-timed
;; shift-register-sipo modules.  Prove the value and state lemmas for this
;; module generator.

(defconst *shift-register-sipo$go-num* 2)
(defconst *shift-register-sipo$st-len* 4)

(defconst *shift-register-sipo$data-ins-len* 3)

(defconst *shift-register-sipo$ins-len*
  (+ *shift-register-sipo$data-ins-len*
     *shift-register-sipo$go-num*))

;; DE module generator of SHIFT-REGISTER-SIPO

(module-generator
 shift-register-sipo* (data-width cnt-width)
 (si 'shift-register-sipo data-width)
 (list* 'full-in 'empty-out- 'bit-in
        (sis 'go 0 *shift-register-sipo$go-num*))
 (list* 'in-act 'out-act (append (sis 'data-out 0 data-width)
                                 (sis 'cnt-out 0 cnt-width)))
 '(r-reg r-cnt w-reg w-cnt)
 (list
  ;; LINKS
  ;; R-REG
  (list 'r-reg
        (list* 'r-reg-status (sis 'r-reg-out 0 data-width))
        (si 'link data-width)
        (list* 'buf-act 'shift-act (sis 'r-reg-in 0 data-width)))

  ;; R-CNT
  (list 'r-cnt
        (list* 'r-cnt-status (sis 'r-cnt-out 0 cnt-width))
        (si 'link cnt-width)
        (list* 'buf-act 'shift-act (sis 'r-cnt-in 0 cnt-width)))

  ;; W-REG
  (list 'w-reg
        (list* 'w-reg-status (sis 'w-reg-out 0 data-width))
        (si 'link data-width)
        (list* 'shift-act 'buf-act (sis 'w-reg-in 0 data-width)))

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
  '(s1 (shift-full-in) b-and4 (r-reg-status r-cnt-status r-cnt=0~ full-in))
  '(s2 (r-full) b-and3 (r-reg-status r-cnt-status r-cnt=0))
  '(s3 (w-empty-) b-or (w-reg-status w-cnt-status))
  '(s4 (shift-empty-out-) b-or3 (w-reg-status w-cnt-status empty-out-))

  (list 'in-cntl
        '(in-act)
        'joint-cntl
        (list 'shift-full-in 'w-empty- (si 'go 0)))
  (list 'shift-reg-op0
        (sis 'w-reg-in0 0 data-width)
        (si 'v-buf data-width)
        (append (sis 'r-reg-out 1 (1- data-width))
                '(bit-in)))
  (list 'shift-cnt-op0
        (sis 'w-cnt-in0 0 cnt-width)
        (si 'counter cnt-width)
        (sis 'r-cnt-out 0 cnt-width))

  (list 'out-cntl
        '(out-act)
        'joint-cntl
        (list 'r-full 'shift-empty-out- (si 'go 0)))
  (list 'shift-reg-op1
        (sis 'w-reg-in1 0 data-width)
        (si 'v-buf data-width)
        (sis 'r-reg-out 0 data-width))
  (list 'shift-cnt-op1
        (sis 'w-cnt-in1 0 cnt-width)
        (si 'v-buf cnt-width)
        (append (make-list (1- cnt-width) :initial-element 'low)
                '(high)))

  '(shift-cntl (shift-act) b-or (in-act out-act))
  (list 'shift-reg-op
        (sis 'w-reg-in 0 data-width)
        (si 'tv-if (tree-number (make-tree data-width)))
        (cons 'r-cnt=0
              (append (sis 'w-reg-in1 0 data-width)
                      (sis 'w-reg-in0 0 data-width))))
  (list 'shift-cnt-op
        (sis 'w-cnt-in 0 cnt-width)
        (si 'tv-if (tree-number (make-tree cnt-width)))
        (cons 'r-cnt=0
              (append (sis 'w-cnt-in1 0 cnt-width)
                      (sis 'w-cnt-in0 0 cnt-width))))

  ;; Buffer
  '(b0 (buf-full-in) b-and (w-reg-status w-cnt-status))
  '(b1 (buf-empty-out-) b-or (r-reg-status r-cnt-status))
  (list 'buf-cntl
        '(buf-act)
        'joint-cntl
        (list 'buf-full-in 'buf-empty-out- (si 'go 1)))
  (list 'buf-reg-op
        (sis 'r-reg-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'w-reg-out 0 data-width))
  (list 'buf-cnt-op
        (sis 'r-cnt-in 0 cnt-width)
        (si 'v-buf cnt-width)
        (sis 'w-cnt-out 0 cnt-width))

  ;; OUTPUTS
  (list 'reg-out
        (sis 'data-out 0 data-width)
        (si 'v-wire data-width)
        (sis 'r-reg-out 0 data-width))
  (list 'cnt-out
        (sis 'cnt-out 0 cnt-width)
        (si 'v-wire cnt-width)
        (sis 'r-cnt-out 0 cnt-width)))

 :guard (and (posp data-width) (posp cnt-width)))

(make-event
 `(progn
    ,@(state-accessors-gen 'shift-register-sipo
                           '(r-reg r-cnt w-reg w-cnt)
                           0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; SHIFT-REGISTER-SIPO.

(defun shift-register-sipo$netlist (data-width cnt-width)
  (declare (xargs :guard (and (posp data-width)
                              (natp cnt-width)
                              (<= 2 cnt-width))))
  (cons (shift-register-sipo* data-width cnt-width)
        (union$ (link$netlist data-width)
                (link$netlist cnt-width)
                *joint-cntl*
                (fast-zero$netlist cnt-width)
                (counter$netlist cnt-width)
                (v-buf$netlist data-width)
                (v-buf$netlist cnt-width)
                (v-wire$netlist data-width)
                (v-wire$netlist cnt-width)
                (tv-if$netlist (make-tree data-width))
                (tv-if$netlist (make-tree cnt-width))
                :test 'equal)))

;; Recognizer for SHIFT-REGISTER-SIPO

(defund shift-register-sipo& (netlist data-width cnt-width)
  (declare (xargs :guard (and (alistp netlist)
                              (posp data-width)
                              (natp cnt-width)
                              (<= 2 cnt-width))))
  (and (equal (assoc (si 'shift-register-sipo data-width) netlist)
              (shift-register-sipo* data-width cnt-width))
       (b* ((netlist (delete-to-eq (si 'shift-register-sipo data-width)
                                   netlist)))
         (and (link& netlist data-width)
              (link& netlist cnt-width)
              (joint-cntl& netlist)
              (fast-zero& netlist cnt-width)
              (counter& netlist cnt-width)
              (v-buf& netlist data-width)
              (v-buf& netlist cnt-width)
              (v-wire& netlist data-width)
              (v-wire& netlist cnt-width)
              (tv-if& netlist (make-tree data-width))
              (tv-if& netlist (make-tree cnt-width))))))

;; Sanity check

(local
 (defthmd check-shift-register-sipo$netlist-64-7
   (and (net-syntax-okp (shift-register-sipo$netlist 64 7))
        (net-arity-okp (shift-register-sipo$netlist 64 7))
        (shift-register-sipo& (shift-register-sipo$netlist 64 7) 64 7))))

;; Constraints on the state of SHIFT-REGISTER-SIPO

(defund shift-register-sipo$st-format (st data-width cnt-width)
  (b* ((r-reg (get-field *shift-register-sipo$r-reg* st))
       (r-cnt (get-field *shift-register-sipo$r-cnt* st))
       (w-reg (get-field *shift-register-sipo$w-reg* st))
       (w-cnt (get-field *shift-register-sipo$w-cnt* st)))
    (and (posp data-width)
         (natp cnt-width)
         (<= 3 cnt-width)
         (link$st-format r-reg data-width)
         (link$st-format r-cnt cnt-width)
         (link$st-format w-reg data-width)
         (link$st-format w-cnt cnt-width))))

(defthm shift-register-sipo$st-format=>contraints
  (implies (shift-register-sipo$st-format st data-width cnt-width)
           (and (posp data-width)
                (natp cnt-width)
                (<= 3 cnt-width)))
  :hints (("Goal" :in-theory (enable shift-register-sipo$st-format)))
  :rule-classes :forward-chaining)

(defund shift-register-sipo$valid-st (st data-width cnt-width)
  (b* ((r-reg (get-field *shift-register-sipo$r-reg* st))
       (r-cnt (get-field *shift-register-sipo$r-cnt* st))
       (w-reg (get-field *shift-register-sipo$w-reg* st))
       (w-cnt (get-field *shift-register-sipo$w-cnt* st)))
    (and (shift-register-sipo$st-format st data-width cnt-width)
         (equal data-width (expt 2 (1- cnt-width)))
         (link$valid-st r-reg data-width)
         (link$valid-st r-cnt cnt-width)
         (link$valid-st w-reg data-width)
         (link$valid-st w-cnt cnt-width))))

(local
 (defthm expt-linear-lower-<=-instance
   (implies (and (<= 2 n)
                 (integerp n))
            (<= 4 (expt 2 n)))
   :rule-classes :linear))

(defthmd shift-register-sipo$valid-st=>constraints
  (implies (shift-register-sipo$valid-st st data-width cnt-width)
           (and (natp data-width)
                (<= 4 data-width)
                (natp cnt-width)
                (<= 3 cnt-width)))
  :hints (("Goal" :in-theory (enable shift-register-sipo$valid-st)))
  :rule-classes :forward-chaining)

(defthmd shift-register-sipo$valid-st=>st-format
  (implies (shift-register-sipo$valid-st st data-width cnt-width)
           (shift-register-sipo$st-format st data-width cnt-width))
  :hints (("Goal" :in-theory (enable shift-register-sipo$valid-st))))

;; Extract the input and output signals for SHIFT-REGISTER-SIPO

(progn
  ;; Extract the input data

  (defun shift-register-sipo$bit-in (inputs)
    (declare (xargs :guard (true-listp inputs)))
    (nth 2 inputs))

  (in-theory (disable shift-register-sipo$bit-in))

  ;; Extract the "in-act" signal

  (defund shift-register-sipo$in-act (inputs st)
    (b* ((full-in (nth 0 inputs))
         (go-signals (nthcdr *shift-register-sipo$data-ins-len* inputs))
         (go-shift (nth 0 go-signals))

         (r-reg (get-field *shift-register-sipo$r-reg* st))
         (r-reg.s (get-field *link$s* r-reg))
         (r-cnt (get-field *shift-register-sipo$r-cnt* st))
         (r-cnt.s (get-field *link$s* r-cnt))
         (r-cnt.d (get-field *link$d* r-cnt))
         (w-reg (get-field *shift-register-sipo$w-reg* st))
         (w-reg.s (get-field *link$s* w-reg))
         (w-cnt (get-field *shift-register-sipo$w-cnt* st))
         (w-cnt.s (get-field *link$s* w-cnt))

         (r-cnt=0~ (f-not (f$fast-zero (strip-cars r-cnt.d))))
         (shift-full-in (f-and4 (car r-reg.s) (car r-cnt.s)
                                r-cnt=0~ full-in))
         (w-empty- (f-or (car w-reg.s) (car w-cnt.s))))
      (joint-act shift-full-in w-empty- go-shift)))

  (defthm shift-register-sipo$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (shift-register-sipo$in-act inputs st)))
    :hints (("Goal" :in-theory (enable f-and4
                                       shift-register-sipo$in-act))))

  ;; Extract the "out-act" signal

  (defund shift-register-sipo$out-act (inputs st)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr *shift-register-sipo$data-ins-len* inputs))
         (go-shift (nth 0 go-signals))

         (r-reg (get-field *shift-register-sipo$r-reg* st))
         (r-reg.s (get-field *link$s* r-reg))
         (r-cnt (get-field *shift-register-sipo$r-cnt* st))
         (r-cnt.s (get-field *link$s* r-cnt))
         (r-cnt.d (get-field *link$d* r-cnt))
         (w-reg (get-field *shift-register-sipo$w-reg* st))
         (w-reg.s (get-field *link$s* w-reg))
         (w-cnt (get-field *shift-register-sipo$w-cnt* st))
         (w-cnt.s (get-field *link$s* w-cnt))

         (r-cnt=0 (f$fast-zero (strip-cars r-cnt.d)))
         (r-full (f-and3 (car r-reg.s) (car r-cnt.s) r-cnt=0))
         (shift-empty-out- (f-or3 (car w-reg.s) (car w-cnt.s) empty-out-)))
      (joint-act r-full shift-empty-out- go-shift)))

  (defthm shift-register-sipo$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (shift-register-sipo$out-act inputs st)))
    :hints (("Goal" :in-theory (enable f-or3
                                       shift-register-sipo$out-act))))

  (defthm shift-register-sipo$in-out-acts-mutually-exclusive
    (implies (and (shift-register-sipo$valid-st st data-width cnt-width)
                  (shift-register-sipo$in-act inputs st))
             (not (shift-register-sipo$out-act inputs st)))
    :hints (("Goal" :in-theory (enable f-and4
                                       shift-register-sipo$valid-st
                                       shift-register-sipo$in-act
                                       shift-register-sipo$out-act))))

  ;; Extract the output data

  (defund shift-register-sipo$data-out (st)
    (b* ((r-reg (get-field *shift-register-sipo$r-reg* st))
         (r-reg.d (get-field *link$d* r-reg)))
      (v-threefix (strip-cars r-reg.d))))

  (defthm len-shift-register-sipo$data-out-1
    (implies (shift-register-sipo$st-format st data-width cnt-width)
             (equal (len (shift-register-sipo$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable shift-register-sipo$st-format
                                       shift-register-sipo$data-out))))

  (defthm len-shift-register-sipo$data-out-2
    (implies (shift-register-sipo$valid-st st data-width cnt-width)
             (equal (len (shift-register-sipo$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable shift-register-sipo$valid-st
                                       shift-register-sipo$data-out))))

  (defthm bvp-shift-register-sipo$data-out-1
    (implies (and (shift-register-sipo$valid-st st data-width cnt-width)
                  (shift-register-sipo$in-act inputs st))
             (bvp (shift-register-sipo$data-out st)))
    :hints (("Goal" :in-theory (enable f-and4
                                       shift-register-sipo$valid-st
                                       shift-register-sipo$in-act
                                       shift-register-sipo$data-out))))

  (defthm bvp-shift-register-sipo$data-out-2
    (implies (and (shift-register-sipo$valid-st st data-width cnt-width)
                  (shift-register-sipo$out-act inputs st))
             (bvp (shift-register-sipo$data-out st)))
    :hints (("Goal" :in-theory (enable f-and3
                                       shift-register-sipo$valid-st
                                       shift-register-sipo$out-act
                                       shift-register-sipo$data-out))))

  (defund shift-register-sipo$cnt-out (st)
    (b* ((r-cnt (get-field *shift-register-sipo$r-cnt* st))
         (r-cnt.d (get-field *link$d* r-cnt)))
      (v-threefix (strip-cars r-cnt.d))))

  (defthm len-shift-register-sipo$cnt-out-1
    (implies (shift-register-sipo$st-format st data-width cnt-width)
             (equal (len (shift-register-sipo$cnt-out st))
                    cnt-width))
    :hints (("Goal" :in-theory (enable shift-register-sipo$st-format
                                       shift-register-sipo$cnt-out))))

  (defthm len-shift-register-sipo$cnt-out-2
    (implies (shift-register-sipo$valid-st st data-width cnt-width)
             (equal (len (shift-register-sipo$cnt-out st))
                    cnt-width))
    :hints (("Goal" :in-theory (enable shift-register-sipo$valid-st
                                       shift-register-sipo$data-out))))

  (defthm bvp-shift-register-sipo$cnt-out-1
    (implies (and (shift-register-sipo$valid-st st data-width cnt-width)
                  (shift-register-sipo$in-act inputs st))
             (bvp (shift-register-sipo$cnt-out st)))
    :hints (("Goal" :in-theory (enable f-and4
                                       shift-register-sipo$valid-st
                                       shift-register-sipo$in-act
                                       shift-register-sipo$cnt-out))))

  (defthm bvp-shift-register-sipo$cnt-out-2
    (implies (and (shift-register-sipo$valid-st st data-width cnt-width)
                  (shift-register-sipo$out-act inputs st))
             (bvp (shift-register-sipo$cnt-out st)))
    :hints (("Goal" :in-theory (enable f-and3
                                       shift-register-sipo$valid-st
                                       shift-register-sipo$out-act
                                       shift-register-sipo$cnt-out))))

  (defun shift-register-sipo$outputs (inputs st)
    (list* (shift-register-sipo$in-act inputs st)
           (shift-register-sipo$out-act inputs st)
           (append (shift-register-sipo$data-out st)
                   (shift-register-sipo$cnt-out st))))
  )

;; Prove that SHIFT-REGISTER-SIPO is not a DE primitive.

(not-primp-lemma shift-register-sipo)

;; The value lemma for SHIFT-REGISTER-SIPO

(defthmd shift-register-sipo$value
  (b* ((inputs (list* full-in empty-out- bit-in go-signals)))
    (implies (and (shift-register-sipo& netlist data-width cnt-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *shift-register-sipo$go-num*)
                  (shift-register-sipo$st-format st data-width cnt-width))
             (equal (se (si 'shift-register-sipo data-width) inputs st netlist)
                    (shift-register-sipo$outputs inputs st))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'shift-register-sipo data-width)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            shift-register-sipo&
                            shift-register-sipo*$destructure
                            link$value
                            joint-cntl$value
                            fast-zero$value
                            counter$value
                            v-buf$value
                            v-wire$value
                            tv-if$value
                            shift-register-sipo$st-format
                            shift-register-sipo$in-act
                            shift-register-sipo$out-act
                            shift-register-sipo$data-out
                            shift-register-sipo$cnt-out)
                           ((shift-register-sipo*)
                            car-cdr-elim
                            de-module-disabled-rules)))))

;; This function specifies the next state of SHIFT-REGISTER-SIPO.

(defun shift-register-sipo$step (inputs st data-width cnt-width)
  (b* ((bit-in     (shift-register-sipo$bit-in inputs))
       (go-signals (nthcdr *shift-register-sipo$data-ins-len* inputs))
       (go-buf (nth 1 go-signals))

       (r-reg (get-field *shift-register-sipo$r-reg* st))
       (r-reg.s (get-field *link$s* r-reg))
       (r-reg.d (get-field *link$d* r-reg))
       (r-cnt (get-field *shift-register-sipo$r-cnt* st))
       (r-cnt.s (get-field *link$s* r-cnt))
       (r-cnt.d (get-field *link$d* r-cnt))
       (w-reg (get-field *shift-register-sipo$w-reg* st))
       (w-reg.s (get-field *link$s* w-reg))
       (w-reg.d (get-field *link$d* w-reg))
       (w-cnt (get-field *shift-register-sipo$w-cnt* st))
       (w-cnt.s (get-field *link$s* w-cnt))
       (w-cnt.d (get-field *link$d* w-cnt))

       (r-cnt=0 (f$fast-zero (strip-cars r-cnt.d)))
       (in-act (shift-register-sipo$in-act inputs st))
       (out-act (shift-register-sipo$out-act inputs st))
       (shift-act (f-or in-act out-act))

       (buf-full-in (f-and (car w-reg.s) (car w-cnt.s)))
       (buf-empty-out- (f-or (car r-reg.s) (car r-cnt.s)))
       (buf-act (joint-act buf-full-in buf-empty-out- go-buf))

       (r-reg-inputs (list* buf-act shift-act (strip-cars w-reg.d)))
       (r-cnt-inputs (list* buf-act shift-act (strip-cars w-cnt.d)))
       (w-reg-inputs (list* shift-act buf-act
                            (fv-if r-cnt=0
                                   (strip-cars r-reg.d)
                                   (append (nthcdr 1 (v-threefix
                                                      (strip-cars r-reg.d)))
                                           (list bit-in)))))
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
     ;; R-REG
     (link$step r-reg-inputs r-reg data-width)
     ;; R-CNT
     (link$step r-cnt-inputs r-cnt cnt-width)
     ;; W-REG
     (link$step w-reg-inputs w-reg data-width)
     ;; W-CNT
     (link$step w-cnt-inputs w-cnt cnt-width))))

(defthm len-of-shift-register-sipo$step
  (equal (len (shift-register-sipo$step inputs st data-width cnt-width))
         *shift-register-sipo$st-len*))

;; The state lemma for SHIFT-REGISTER-SIPO

(defthmd shift-register-sipo$state
  (b* ((inputs (list* full-in empty-out- bit-in go-signals)))
    (implies
     (and (shift-register-sipo& netlist data-width cnt-width)
          (true-listp go-signals)
          (equal (len go-signals) *shift-register-sipo$go-num*)
          (shift-register-sipo$st-format st data-width cnt-width))
     (equal (de (si 'shift-register-sipo data-width) inputs st netlist)
            (shift-register-sipo$step inputs st data-width cnt-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'shift-register-sipo data-width)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            shift-register-sipo&
                            shift-register-sipo*$destructure
                            link$value
                            link$state
                            joint-cntl$value
                            fast-zero$value
                            counter$value
                            v-buf$value
                            v-wire$value
                            tv-if$value
                            shift-register-sipo$bit-in
                            shift-register-sipo$in-act
                            shift-register-sipo$out-act
                            shift-register-sipo$st-format)
                           ((shift-register-sipo*)
                            append-v-threefix
                            acl2::associativity-of-append
                            de-module-disabled-rules)))))

(in-theory (disable shift-register-sipo$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund shift-register-sipo$input-format (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (bit-in     (shift-register-sipo$bit-in inputs))
       (go-signals (nthcdr *shift-register-sipo$data-ins-len* inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (booleanp bit-in))
     (true-listp go-signals)
     (= (len go-signals) *shift-register-sipo$go-num*)
     (equal inputs
            (list* full-in empty-out- bit-in go-signals)))))

(defthm booleanp-shift-register-sipo$in-act
  (implies (and (shift-register-sipo$input-format inputs)
                (shift-register-sipo$valid-st st data-width cnt-width))
           (booleanp (shift-register-sipo$in-act inputs st)))
  :hints (("Goal"
           :in-theory (e/d (f-and4
                            shift-register-sipo$input-format
                            shift-register-sipo$valid-st
                            shift-register-sipo$in-act)
                           ())))
  :rule-classes :type-prescription)

(defthm booleanp-shift-register-sipo$out-act
  (implies (and (shift-register-sipo$input-format inputs)
                (shift-register-sipo$valid-st st data-width cnt-width))
           (booleanp (shift-register-sipo$out-act inputs st)))
  :hints (("Goal"
           :in-theory (e/d (f-and3
                            shift-register-sipo$input-format
                            shift-register-sipo$valid-st
                            shift-register-sipo$out-act)
                           ())))
  :rule-classes :type-prescription)

;;(simulate-lemma shift-register-sipo nil data-width cnt-width)

(progn
  (defthm shift-register-sipo$st-format-preserved
    (implies
     (shift-register-sipo$st-format st data-width cnt-width)
     (shift-register-sipo$st-format (shift-register-sipo$step
                                     inputs st data-width cnt-width)
                                    data-width
                                    cnt-width))
    :hints (("Goal" :in-theory (enable get-field
                                       shift-register-sipo$step
                                       shift-register-sipo$st-format))))

  (defthmd shift-register-sipo$value-alt
    (implies
     (and (shift-register-sipo& netlist data-width cnt-width)
          (shift-register-sipo$input-format inputs)
          (shift-register-sipo$st-format st data-width cnt-width))
     (equal (se (si 'shift-register-sipo data-width) inputs st netlist)
            (shift-register-sipo$outputs inputs st)))
    :hints (("Goal" :in-theory (enable shift-register-sipo$input-format
                                       shift-register-sipo$value))))

  (defthmd shift-register-sipo$state-alt
    (implies
     (and (shift-register-sipo& netlist data-width cnt-width)
          (shift-register-sipo$input-format inputs)
          (shift-register-sipo$st-format st data-width cnt-width))
     (equal (de (si 'shift-register-sipo data-width) inputs st netlist)
            (shift-register-sipo$step inputs st data-width cnt-width)))
    :hints (("Goal" :in-theory (enable shift-register-sipo$input-format
                                       shift-register-sipo$state))))

  (run-gen shift-register-sipo data-width cnt-width)
  (input-format-n-gen shift-register-sipo)

  (defthmd shift-register-sipo$de-n
    (implies (and (shift-register-sipo& netlist data-width cnt-width)
                  (shift-register-sipo$input-format-n inputs-seq n)
                  (shift-register-sipo$st-format st data-width cnt-width))
             (equal (de-n (si 'shift-register-sipo data-width)
                          inputs-seq st netlist n)
                    (shift-register-sipo$run
                     inputs-seq st data-width cnt-width n)))
    :hints (("Goal" :in-theory (enable shift-register-sipo$run
                                       shift-register-sipo$state-alt)))))

;; ======================================================================

;; 3. Single-Step-Update Property

;; The extraction function for SHIFT-REGISTER-SIPO

(defund shift-register-sipo$extract (st)
  (b* ((r-reg (get-field *shift-register-sipo$r-reg* st))
       (r-reg.s (get-field *link$s* r-reg))
       (r-reg.d (get-field *link$d* r-reg))
       (r-cnt (get-field *shift-register-sipo$r-cnt* st))
       (r-cnt.d (get-field *link$d* r-cnt))
       (w-reg (get-field *shift-register-sipo$w-reg* st))
       (w-reg.d (get-field *link$d* w-reg))
       (w-cnt (get-field *shift-register-sipo$w-cnt* st))
       (w-cnt.d (get-field *link$d* w-cnt)))
    (if (fullp r-reg.s)
        (nthcdr (v-to-nat (strip-cars r-cnt.d))
                (strip-cars r-reg.d))
      (nthcdr (v-to-nat (strip-cars w-cnt.d))
              (strip-cars w-reg.d)))))

(local
 (defthm v-to-nat-of-v-zp
   (equal (v-zp x)
          (equal (v-to-nat x) 0))
   :hints (("Goal" :in-theory (enable v-zp v-nzp v-to-nat)))))

(defthm shift-register-sipo$extract-not-empty
  (implies (and (shift-register-sipo$out-act inputs st)
                (shift-register-sipo$valid-st st data-width cnt-width))
           (< 0 (len (shift-register-sipo$extract st))))
  :hints (("Goal"
           :in-theory (e/d (f-and
                            f-and3
                            shift-register-sipo$valid-st
                            shift-register-sipo$extract
                            shift-register-sipo$out-act)
                           ())))
  :rule-classes :linear)

(defthmd len-of-shift-register-sipo$extract-lemma
  (implies (and (shift-register-sipo$out-act inputs st)
                (shift-register-sipo$valid-st st data-width cnt-width))
           (equal (len (shift-register-sipo$extract st))
                  data-width))
  :hints (("Goal" :in-theory (enable f-and3
                                     f-and
                                     f-or3
                                     joint-act
                                     shift-register-sipo$valid-st
                                     shift-register-sipo$out-act
                                     shift-register-sipo$extract))))

(defthm len-of-shift-register-sipo$extract-contrapositive-lemma-1
  (implies (and (shift-register-sipo$out-act inputs st)
                (not (equal (len (shift-register-sipo$extract st))
                            data-width)))
           (not (shift-register-sipo$valid-st st data-width cnt-width)))
  :hints (("Goal" :in-theory (enable f-and3
                                     f-and
                                     f-or3
                                     joint-act
                                     shift-register-sipo$valid-st
                                     shift-register-sipo$out-act
                                     shift-register-sipo$extract))))

(defthm len-of-shift-register-sipo$extract-contrapositive-lemma-2
  (implies (and (shift-register-sipo$valid-st st data-width cnt-width)
                (not (equal (len (shift-register-sipo$extract st))
                            data-width)))
           (not (shift-register-sipo$out-act inputs st)))
  :hints (("Goal" :in-theory (enable f-and3
                                     f-and
                                     f-or3
                                     joint-act
                                     shift-register-sipo$valid-st
                                     shift-register-sipo$out-act
                                     shift-register-sipo$extract))))

;; Specify and prove a state invariant

(progn
  (defund shift-register-sipo$inv (st)
    (b* ((r-reg (get-field *shift-register-sipo$r-reg* st))
         (r-reg.s (get-field *link$s* r-reg))
         (r-reg.d (get-field *link$d* r-reg))
         (r-cnt (get-field *shift-register-sipo$r-cnt* st))
         (r-cnt.s (get-field *link$s* r-cnt))
         (r-cnt.d (get-field *link$d* r-cnt))
         (w-reg (get-field *shift-register-sipo$w-reg* st))
         (w-reg.s (get-field *link$s* w-reg))
         (w-reg.d (get-field *link$d* w-reg))
         (w-cnt (get-field *shift-register-sipo$w-cnt* st))
         (w-cnt.s (get-field *link$s* w-cnt))
         (w-cnt.d (get-field *link$d* w-cnt)))
      (and (equal r-reg.s r-cnt.s)
           (equal w-reg.s w-cnt.s)
           (not (equal r-reg.s w-reg.s))

           (or (emptyp r-cnt.s)
               (<= (v-to-nat (strip-cars r-cnt.d))
                   (len r-reg.d)))
           (or (emptyp w-cnt.s)
               (<= (v-to-nat (strip-cars w-cnt.d))
                   (len w-reg.d))))))

  (defthm len-of-shift-register-sipo$extract-upper-bound
    (implies (and (shift-register-sipo$valid-st st data-width cnt-width)
                  (shift-register-sipo$inv st))
             (<= (len (shift-register-sipo$extract st))
                 data-width))
    :hints (("Goal" :in-theory (enable shift-register-sipo$valid-st
                                       shift-register-sipo$inv
                                       shift-register-sipo$extract)))
    :rule-classes :linear)

  (defthm len-of-shift-register-sipo$extract-upper-bound-when-in-act
    (implies (and (shift-register-sipo$in-act inputs st)
                  (shift-register-sipo$valid-st st data-width cnt-width)
                  (shift-register-sipo$inv st))
             (< (len (shift-register-sipo$extract st))
                data-width))
    :hints (("Goal" :in-theory (e/d (f-and4
                                     shift-register-sipo$valid-st
                                     shift-register-sipo$st-format
                                     shift-register-sipo$inv
                                     shift-register-sipo$in-act
                                     shift-register-sipo$extract)
                                    (acl2::prefer-positive-addends-equal))))
    :rule-classes :linear)

  (local
   (defthm shift-register-sipo$input-format-lemma-1
     (implies (shift-register-sipo$input-format inputs)
              (booleanp (nth 0 inputs)))
     :hints (("Goal" :in-theory (enable shift-register-sipo$input-format)))
     :rule-classes :type-prescription))

  (local
   (defthm shift-register-sipo$input-format-lemma-2
     (implies (shift-register-sipo$input-format inputs)
              (booleanp (nth 1 inputs)))
     :hints (("Goal" :in-theory (enable shift-register-sipo$input-format)))
     :rule-classes :type-prescription))

  (local
   (defthm shift-register-sipo$input-format-lemma-3
     (implies (and (shift-register-sipo$input-format inputs)
                   (nth 0 inputs))
              (booleanp (shift-register-sipo$bit-in inputs)))
     :hints (("Goal" :in-theory (enable shift-register-sipo$input-format)))
     :rule-classes :type-prescription))

  (local
   (defthm v-to-nat-of-repeat-lemma
     (equal (v-to-nat (append (repeat n nil) '(t)))
            (expt 2 (nfix n)))
     :hints (("Goal" :in-theory (enable v-to-nat repeat)))))

  (defthm shift-register-sipo$inv-preserved
    (implies (and (shift-register-sipo$input-format inputs)
                  (shift-register-sipo$valid-st st data-width cnt-width)
                  (shift-register-sipo$inv st))
             (shift-register-sipo$inv
              (shift-register-sipo$step inputs st data-width cnt-width)))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              bvp
                              shift-register-sipo$st-format
                              shift-register-sipo$valid-st
                              shift-register-sipo$inv
                              shift-register-sipo$step
                              shift-register-sipo$in-act
                              shift-register-sipo$out-act)
                             ()))))
  )

;; The extracted next-state function for SHIFT-REGISTER-SIPO.  Note that this
;; function avoids exploring the internal computation of SHIFT-REGISTER-SIPO.

(defund shift-register-sipo$extracted-step (inputs st)
  (b* ((data (shift-register-sipo$bit-in inputs))
       (extracted-st (shift-register-sipo$extract st)))
    (cond
     ((equal (shift-register-sipo$out-act inputs st) t)
      nil)
     ((equal (shift-register-sipo$in-act inputs st) t)
      (append extracted-st (list data)))
     (t extracted-st))))

;; The single-step-update property

(progn
  (local
   (defthm len-cdr
     (implies (< 0 (len x))
              (equal (len (cdr x))
                     (1- (len x))))))

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

  (defthm shift-register-sipo$extracted-step-correct
    (b* ((next-st (shift-register-sipo$step inputs st data-width cnt-width)))
      (implies (and (shift-register-sipo$input-format inputs)
                    (shift-register-sipo$valid-st st data-width cnt-width)
                    (shift-register-sipo$inv st))
               (equal (shift-register-sipo$extract next-st)
                      (shift-register-sipo$extracted-step inputs st))))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              joint-act
                              bvp
                              pos-len=>cons
                              shift-register-sipo$extracted-step
                              shift-register-sipo$valid-st
                              shift-register-sipo$inv
                              shift-register-sipo$step
                              shift-register-sipo$in-act
                              shift-register-sipo$out-act
                              shift-register-sipo$extract)
                             ()))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that shift-register-sipo$valid-st is an invariant.

(defthm shift-register-sipo$valid-st-preserved
  (implies (and (shift-register-sipo$input-format inputs)
                (shift-register-sipo$valid-st st data-width cnt-width))
           (shift-register-sipo$valid-st
            (shift-register-sipo$step inputs st data-width cnt-width)
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
                            shift-register-sipo$st-format
                            shift-register-sipo$valid-st
                            shift-register-sipo$step
                            shift-register-sipo$in-act
                            shift-register-sipo$out-act)
                           (if*)))))

(defthm shift-register-sipo$extract-lemma
  (implies (and (shift-register-sipo$valid-st st data-width cnt-width)
                (shift-register-sipo$out-act inputs st))
           (equal (shift-register-sipo$data-out st)
                  (shift-register-sipo$extract st)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (joint-act
                            f-and
                            f-and3
                            f-or3
                            shift-register-sipo$valid-st
                            shift-register-sipo$extract
                            shift-register-sipo$out-act
                            shift-register-sipo$data-out)
                           ()))))

;; Extract the accepted input sequence

(defun shift-register-sipo$in-seq (inputs-seq st data-width cnt-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-seq))
         (in-act (shift-register-sipo$in-act inputs st))
         (data (shift-register-sipo$bit-in inputs)))
      (if (equal in-act t)
          (append (shift-register-sipo$in-seq
                   (cdr inputs-seq)
                   (shift-register-sipo$step inputs st data-width cnt-width)
                   data-width
                   cnt-width
                   (1- n))
                  (list data))
        (shift-register-sipo$in-seq
         (cdr inputs-seq)
         (shift-register-sipo$step inputs st data-width cnt-width)
         data-width
         cnt-width
         (1- n))))))

(defun shift-register-sipo$netlist-in-seq
    (inputs-seq st netlist data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-seq))
         (outputs (se (si 'shift-register-sipo data-width)
                      inputs st netlist))
         (in-act (nth 0 outputs))
         (data (shift-register-sipo$bit-in inputs)))
      (if (equal in-act t)
          (append (shift-register-sipo$netlist-in-seq
                   (cdr inputs-seq)
                   (de (si 'shift-register-sipo data-width)
                       inputs st netlist)
                   netlist
                   data-width
                   (1- n))
                  (list data))
        (shift-register-sipo$netlist-in-seq
         (cdr inputs-seq)
         (de (si 'shift-register-sipo data-width)
             inputs st netlist)
         netlist
         data-width
         (1- n))))))

(defthm shift-register-sipo$in-seq-lemma
  (implies (and (shift-register-sipo& netlist data-width cnt-width)
                (shift-register-sipo$input-format-n inputs-seq n)
                (shift-register-sipo$st-format st data-width cnt-width))
           (equal (shift-register-sipo$netlist-in-seq
                   inputs-seq st netlist data-width n)
                  (shift-register-sipo$in-seq
                   inputs-seq st data-width cnt-width n)))
  :hints (("Goal" :in-theory (enable shift-register-sipo$value-alt
                                     shift-register-sipo$state-alt))))

;; Extract the valid output sequence

(defun shift-register-sipo$out-seq (inputs-seq st data-width cnt-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-seq))
         (out-act (shift-register-sipo$out-act inputs st))
         (data (shift-register-sipo$data-out st)))
      (if (equal out-act t)
          (append (shift-register-sipo$out-seq
                   (cdr inputs-seq)
                   (shift-register-sipo$step inputs st data-width cnt-width)
                   data-width
                   cnt-width
                   (1- n))
                  (list data))
        (shift-register-sipo$out-seq
         (cdr inputs-seq)
         (shift-register-sipo$step inputs st data-width cnt-width)
         data-width
         cnt-width
         (1- n))))))

(defun shift-register-sipo$netlist-out-seq
    (inputs-seq st netlist data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-seq))
         (outputs (se (si 'shift-register-sipo data-width)
                      inputs st netlist))
         (out-act (nth 1 outputs))
         (data (take data-width (nthcdr 2 outputs))))
      (if (equal out-act t)
          (append (shift-register-sipo$netlist-out-seq
                   (cdr inputs-seq)
                   (de (si 'shift-register-sipo data-width)
                       inputs st netlist)
                   netlist
                   data-width
                   (1- n))
                  (list data))
        (shift-register-sipo$netlist-out-seq
         (cdr inputs-seq)
         (de (si 'shift-register-sipo data-width)
             inputs st netlist)
         netlist
         data-width
         (1- n))))))

(defthm shift-register-sipo$out-seq-lemma
  (implies (and (shift-register-sipo& netlist data-width cnt-width)
                (shift-register-sipo$input-format-n inputs-seq n)
                (shift-register-sipo$st-format st data-width cnt-width))
           (equal (shift-register-sipo$netlist-out-seq
                   inputs-seq st netlist data-width n)
                  (shift-register-sipo$out-seq
                   inputs-seq st data-width cnt-width n)))
  :hints (("Goal" :in-theory (enable shift-register-sipo$value-alt
                                     shift-register-sipo$state-alt))))

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
   (defthm shift-register-sipo$dataflow-correct-aux
     (implies (and (shift-register-sipo$valid-st st data-width cnt-width)
                   (shift-register-sipo$inv st)
                   (consp (shift-register-sipo$extract st)))
              (equal (pack-rev data-width
                               (shift-register-sipo$extract st))
                     (list (shift-register-sipo$extract st))))
     :hints
     (("Goal"
       :use len-of-shift-register-sipo$extract-upper-bound
       :in-theory (e/d (shift-register-sipo$valid-st=>constraints
                        pack-rev)
                       (len-of-shift-register-sipo$extract-upper-bound))))))

  (defthmd shift-register-sipo$dataflow-correct
    (b* ((extracted-st (shift-register-sipo$extract st))
         (final-st (shift-register-sipo$run
                    inputs-seq st data-width cnt-width n))
         (final-extracted-st (shift-register-sipo$extract final-st)))
      (implies
       (and (shift-register-sipo$input-format-n inputs-seq n)
            (shift-register-sipo$valid-st st data-width cnt-width)
            (shift-register-sipo$inv st))
       (equal (append1 final-extracted-st
                       (shift-register-sipo$out-seq
                        inputs-seq st data-width cnt-width n))
              (pack-rev
               data-width
               (append extracted-st
                       (rev (shift-register-sipo$in-seq
                             inputs-seq st data-width cnt-width n)))))))
    :hints (("Goal"
             :induct (shift-register-sipo$in-seq
                      inputs-seq st data-width cnt-width n)
             :in-theory (enable append1
                                pack-rev
                                shift-register-sipo$valid-st=>constraints
                                len-of-shift-register-sipo$extract-lemma
                                shift-register-sipo$extracted-step))))

  (defthmd shift-register-sipo$functionally-correct
    (b* ((extracted-st (shift-register-sipo$extract st))
         (final-st (de-n (si 'shift-register-sipo data-width)
                         inputs-seq st netlist n))
         (final-extracted-st (shift-register-sipo$extract final-st)))
      (implies
       (and (shift-register-sipo& netlist data-width cnt-width)
            (shift-register-sipo$input-format-n inputs-seq n)
            (shift-register-sipo$valid-st st data-width cnt-width)
            (shift-register-sipo$inv st))
       (equal (append1 final-extracted-st
                       (shift-register-sipo$netlist-out-seq
                        inputs-seq st netlist data-width n))
              (pack-rev
               data-width
               (append extracted-st
                       (rev (shift-register-sipo$netlist-in-seq
                             inputs-seq st netlist data-width n)))))))
    :hints (("Goal"
             :use shift-register-sipo$dataflow-correct
             :in-theory (enable shift-register-sipo$valid-st=>st-format
                                shift-register-sipo$de-n))))
  )

