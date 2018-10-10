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

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of SHIFT-REGISTER-PISO
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of SHIFT-REGISTER-PISO
;;
;; Construct a DE module generator that generates self-timed parallel-in,
;; serial-out (PISO) shift register modules.  Prove the value and state lemmas
;; for this module generator.

(defconst *shift-register-piso$go-num* 2)
(defconst *shift-register-piso$st-len* 4)

(defun shift-register-piso$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun shift-register-piso$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (shift-register-piso$data-ins-len data-width)
     *shift-register-piso$go-num*))

;; DE module generator of SHIFT-REGISTER-PISO

(module-generator
 shift-register-piso* (data-width cnt-width)
 (si 'shift-register-piso data-width)
 (list* 'full-in 'empty-out-
        (append (sis 'data-in 0 data-width)
                (sis 'go 0 *shift-register-piso$go-num*)))
 '(in-act out-act bit-out)
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
  '(s1 (shift-full-in) b-and4 (r-reg-status r-cnt-status r-cnt=0 full-in))
  '(s2 (r-full) b-and3 (r-reg-status r-cnt-status r-cnt=0~))
  '(s3 (w-empty-) b-or (w-reg-status w-cnt-status))
  '(s4 (shift-empty-out-) b-or3 (w-reg-status w-cnt-status empty-out-))

  (list 'in-cntl
        '(in-act)
        'joint-cntl
        (list 'shift-full-in 'w-empty- (si 'go 0)))
  (list 'shift-reg-op0
        (sis 'w-reg-in0 0 data-width)
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
        (sis 'w-reg-in1 0 data-width)
        (si 'v-buf data-width)
        (append (sis 'r-reg-out 1 (1- data-width))
                '(low)))
  (list 'shift-cnt-op1
        (sis 'w-cnt-in1 0 cnt-width)
        (si 'counter cnt-width)
        (sis 'r-cnt-out 0 cnt-width))

  '(shift-cntl (shift-act) b-or (in-act out-act))
  (list 'shift-reg-op
        (sis 'w-reg-in 0 data-width)
        (si 'tv-if (tree-number (make-tree data-width)))
        (cons 'r-cnt=0
              (append (sis 'w-reg-in0 0 data-width)
                      (sis 'w-reg-in1 0 data-width))))
  (list 'shift-cnt-op
        (sis 'w-cnt-in 0 cnt-width)
        (si 'tv-if (tree-number (make-tree cnt-width)))
        (cons 'r-cnt=0
              (append (sis 'w-cnt-in0 0 cnt-width)
                      (sis 'w-cnt-in1 0 cnt-width))))

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
  (list 'out '(bit-out) 'wire (sis 'r-reg-out 0 1)))

 :guard (and (posp data-width) (posp cnt-width)))

(make-event
 `(progn
    ,@(state-accessors-gen 'shift-register-piso
                           '(r-reg r-cnt w-reg w-cnt)
                           0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; SHIFT-REGISTER-PISO.

(defun shift-register-piso$netlist (data-width cnt-width)
  (declare (xargs :guard (and (posp data-width)
                              (natp cnt-width)
                              (<= 2 cnt-width))))
  (cons (shift-register-piso* data-width cnt-width)
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

;; Recognizer for SHIFT-REGISTER-PISO

(defund shift-register-piso& (netlist data-width cnt-width)
  (declare (xargs :guard (and (alistp netlist)
                              (posp data-width)
                              (natp cnt-width)
                              (<= 2 cnt-width))))
  (and (equal (assoc (si 'shift-register-piso data-width) netlist)
              (shift-register-piso* data-width cnt-width))
       (b* ((netlist (delete-to-eq (si 'shift-register-piso data-width)
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
 (defthmd check-shift-register-piso$netlist-64-7
   (and (net-syntax-okp (shift-register-piso$netlist 64 7))
        (net-arity-okp (shift-register-piso$netlist 64 7))
        (shift-register-piso& (shift-register-piso$netlist 64 7) 64 7))))

;; Constraints on the state of SHIFT-REGISTER-PISO

(defund shift-register-piso$st-format (st data-width cnt-width)
  (b* ((r-reg (get-field *shift-register-piso$r-reg* st))
       (r-cnt (get-field *shift-register-piso$r-cnt* st))
       (w-reg (get-field *shift-register-piso$w-reg* st))
       (w-cnt (get-field *shift-register-piso$w-cnt* st)))
    (and (posp data-width)
         (natp cnt-width)
         (<= 3 cnt-width)
         (link$st-format r-reg data-width)
         (link$st-format r-cnt cnt-width)
         (link$st-format w-reg data-width)
         (link$st-format w-cnt cnt-width))))

(defthm shift-register-piso$st-format=>contraints
  (implies (shift-register-piso$st-format st data-width cnt-width)
           (and (posp data-width)
                (natp cnt-width)
                (<= 3 cnt-width)))
  :hints (("Goal" :in-theory (enable shift-register-piso$st-format)))
  :rule-classes :forward-chaining)

(defund shift-register-piso$valid-st (st data-width cnt-width)
  (b* ((r-reg (get-field *shift-register-piso$r-reg* st))
       (r-cnt (get-field *shift-register-piso$r-cnt* st))
       (w-reg (get-field *shift-register-piso$w-reg* st))
       (w-cnt (get-field *shift-register-piso$w-cnt* st)))
    (and (shift-register-piso$st-format st data-width cnt-width)
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

(defthmd shift-register-piso$valid-st=>constraints
  (implies (shift-register-piso$valid-st st data-width cnt-width)
           (and (natp data-width)
                (<= 4 data-width)
                (natp cnt-width)
                (<= 3 cnt-width)))
  :hints (("Goal" :in-theory (enable shift-register-piso$valid-st)))
  :rule-classes :forward-chaining)

(defthmd shift-register-piso$valid-st=>st-format
  (implies (shift-register-piso$valid-st st data-width cnt-width)
           (shift-register-piso$st-format st data-width cnt-width))
  :hints (("Goal" :in-theory (enable shift-register-piso$valid-st))))

;; Extract the input and output signals for SHIFT-REGISTER-PISO

(progn
  ;; Extract the input data

  (defun shift-register-piso$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 2 inputs)))

  (defthm len-shift-register-piso$data-in
    (equal (len (shift-register-piso$data-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable shift-register-piso$data-in))

  ;; Extract the "in-act" signal

  (defund shift-register-piso$in-act (inputs st data-width)
    (b* ((full-in (nth 0 inputs))
         (go-signals (nthcdr (shift-register-piso$data-ins-len data-width)
                             inputs))
         (go-shift (nth 0 go-signals))

         (r-reg (get-field *shift-register-piso$r-reg* st))
         (r-reg.s (get-field *link$s* r-reg))
         (r-cnt (get-field *shift-register-piso$r-cnt* st))
         (r-cnt.s (get-field *link$s* r-cnt))
         (r-cnt.d (get-field *link$d* r-cnt))
         (w-reg (get-field *shift-register-piso$w-reg* st))
         (w-reg.s (get-field *link$s* w-reg))
         (w-cnt (get-field *shift-register-piso$w-cnt* st))
         (w-cnt.s (get-field *link$s* w-cnt))

         (r-cnt=0 (f$fast-zero (strip-cars r-cnt.d)))
         (shift-full-in (f-and4 (car r-reg.s) (car r-cnt.s)
                                r-cnt=0 full-in))
         (w-empty- (f-or (car w-reg.s) (car w-cnt.s))))
      (joint-act shift-full-in w-empty- go-shift)))

  (defthm shift-register-piso$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (shift-register-piso$in-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable f-and4
                                       shift-register-piso$in-act))))

  ;; Extract the "out-act" signal

  (defund shift-register-piso$out-act (inputs st data-width)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (shift-register-piso$data-ins-len data-width)
                             inputs))
         (go-shift (nth 0 go-signals))

         (r-reg (get-field *shift-register-piso$r-reg* st))
         (r-reg.s (get-field *link$s* r-reg))
         (r-cnt (get-field *shift-register-piso$r-cnt* st))
         (r-cnt.s (get-field *link$s* r-cnt))
         (r-cnt.d (get-field *link$d* r-cnt))
         (w-reg (get-field *shift-register-piso$w-reg* st))
         (w-reg.s (get-field *link$s* w-reg))
         (w-cnt (get-field *shift-register-piso$w-cnt* st))
         (w-cnt.s (get-field *link$s* w-cnt))

         (r-cnt=0~ (f-not (f$fast-zero (strip-cars r-cnt.d))))
         (r-full (f-and3 (car r-reg.s) (car r-cnt.s) r-cnt=0~))
         (shift-empty-out- (f-or3 (car w-reg.s) (car w-cnt.s) empty-out-)))
      (joint-act r-full shift-empty-out- go-shift)))

  (defthm shift-register-piso$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (shift-register-piso$out-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable f-or3
                                       shift-register-piso$out-act))))

  (defthm shift-register-piso$in-out-acts-mutually-exclusive
    (implies (and (shift-register-piso$valid-st st data-width cnt-width)
                  (shift-register-piso$in-act inputs st data-width))
             (not (shift-register-piso$out-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable f-and4
                                       shift-register-piso$valid-st
                                       shift-register-piso$in-act
                                       shift-register-piso$out-act))))

  ;; Extract the output data

  (defund shift-register-piso$bit-out (st)
    (b* ((r-reg (get-field *shift-register-piso$r-reg* st))
         (r-reg.d (get-field *link$d* r-reg)))
      (f-buf (car (strip-cars r-reg.d)))))

  (defthm booleanp-shift-register-piso$bit-out
    (implies (and (shift-register-piso$valid-st st data-width cnt-width)
                  (shift-register-piso$out-act inputs st data-width))
             (booleanp (shift-register-piso$bit-out st)))
    :hints (("Goal" :in-theory (enable f-and3
                                       f-buf
                                       shift-register-piso$valid-st
                                       shift-register-piso$out-act
                                       shift-register-piso$bit-out)))
    :rule-classes :type-prescription)

  (defun shift-register-piso$outputs (inputs st data-width)
    (list (shift-register-piso$in-act inputs st data-width)
          (shift-register-piso$out-act inputs st data-width)
          (shift-register-piso$bit-out st)))
  )

;; Prove that SHIFT-REGISTER-PISO is not a DE primitive.

(not-primp-lemma shift-register-piso)

;; The value lemma for SHIFT-REGISTER-PISO

(defthmd shift-register-piso$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (shift-register-piso& netlist data-width cnt-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *shift-register-piso$go-num*)
                  (shift-register-piso$st-format st data-width cnt-width))
             (equal (se (si 'shift-register-piso data-width) inputs st netlist)
                    (shift-register-piso$outputs inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'shift-register-piso data-width)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            shift-register-piso&
                            shift-register-piso*$destructure
                            link$value
                            joint-cntl$value
                            fast-zero$value
                            counter$value
                            v-buf$value
                            tv-if$value
                            shift-register-piso$data-in
                            shift-register-piso$st-format
                            shift-register-piso$in-act
                            shift-register-piso$out-act
                            shift-register-piso$bit-out)
                           ((shift-register-piso*)
                            car-cdr-elim
                            de-module-disabled-rules)))))

;; This function specifies the next state of SHIFT-REGISTER-PISO.

(defun shift-register-piso$step (inputs st data-width cnt-width)
  (b* ((data-in    (shift-register-piso$data-in inputs data-width))
       (go-signals (nthcdr (shift-register-piso$data-ins-len data-width)
                           inputs))
       (go-buf   (nth 1 go-signals))

       (r-reg (get-field *shift-register-piso$r-reg* st))
       (r-reg.s (get-field *link$s* r-reg))
       (r-reg.d (get-field *link$d* r-reg))
       (r-cnt (get-field *shift-register-piso$r-cnt* st))
       (r-cnt.s (get-field *link$s* r-cnt))
       (r-cnt.d (get-field *link$d* r-cnt))
       (w-reg (get-field *shift-register-piso$w-reg* st))
       (w-reg.s (get-field *link$s* w-reg))
       (w-reg.d (get-field *link$d* w-reg))
       (w-cnt (get-field *shift-register-piso$w-cnt* st))
       (w-cnt.s (get-field *link$s* w-cnt))
       (w-cnt.d (get-field *link$d* w-cnt))

       (r-cnt=0 (f$fast-zero (strip-cars r-cnt.d)))
       (in-act (shift-register-piso$in-act inputs st data-width))
       (out-act (shift-register-piso$out-act inputs st data-width))
       (shift-act (f-or in-act out-act))

       (buf-full-in (f-and (car w-reg.s) (car w-cnt.s)))
       (buf-empty-out- (f-or (car r-reg.s) (car r-cnt.s)))
       (buf-act (joint-act buf-full-in buf-empty-out- go-buf))

       (r-reg-inputs (list* buf-act shift-act (strip-cars w-reg.d)))
       (r-cnt-inputs (list* buf-act shift-act (strip-cars w-cnt.d)))
       (w-reg-inputs (list* shift-act buf-act
                            (fv-if r-cnt=0
                                   data-in
                                   (append (nthcdr 1 (v-threefix
                                                      (strip-cars r-reg.d)))
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
     ;; R-REG
     (link$step r-reg-inputs r-reg data-width)
     ;; R-CNT
     (link$step r-cnt-inputs r-cnt cnt-width)
     ;; W-REG
     (link$step w-reg-inputs w-reg data-width)
     ;; W-CNT
     (link$step w-cnt-inputs w-cnt cnt-width))))

(defthm len-of-shift-register-piso$step
  (equal (len (shift-register-piso$step inputs st data-width cnt-width))
         *shift-register-piso$st-len*))

;; The state lemma for SHIFT-REGISTER-PISO

(defthmd shift-register-piso$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies
     (and (shift-register-piso& netlist data-width cnt-width)
          (true-listp data-in)
          (equal (len data-in) data-width)
          (true-listp go-signals)
          (equal (len go-signals) *shift-register-piso$go-num*)
          (shift-register-piso$st-format st data-width cnt-width))
     (equal (de (si 'shift-register-piso data-width) inputs st netlist)
            (shift-register-piso$step inputs st data-width cnt-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'shift-register-piso data-width)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            shift-register-piso&
                            shift-register-piso*$destructure
                            link$value
                            link$state
                            joint-cntl$value
                            fast-zero$value
                            counter$value
                            v-buf$value
                            tv-if$value
                            shift-register-piso$data-in
                            shift-register-piso$in-act
                            shift-register-piso$out-act
                            shift-register-piso$st-format)
                           ((shift-register-piso*)
                            append-v-threefix
                            acl2::associativity-of-append
                            de-module-disabled-rules)))))

(in-theory (disable shift-register-piso$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund shift-register-piso$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (shift-register-piso$data-in inputs data-width))
       (go-signals (nthcdr (shift-register-piso$data-ins-len data-width) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *shift-register-piso$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(defthm booleanp-shift-register-piso$in-act
  (implies (and (shift-register-piso$input-format inputs data-width)
                (shift-register-piso$valid-st st data-width cnt-width))
           (booleanp (shift-register-piso$in-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (e/d (f-and4
                            shift-register-piso$input-format
                            shift-register-piso$valid-st
                            shift-register-piso$in-act)
                           ())))
  :rule-classes :type-prescription)

(defthm booleanp-shift-register-piso$out-act
  (implies (and (shift-register-piso$input-format inputs data-width)
                (shift-register-piso$valid-st st data-width cnt-width))
           (booleanp (shift-register-piso$out-act inputs st data-width)))
  :hints (("Goal"
           :in-theory (e/d (f-and3
                            shift-register-piso$input-format
                            shift-register-piso$valid-st
                            shift-register-piso$out-act)
                           ())))
  :rule-classes :type-prescription)

(simulate-lemma shift-register-piso :sizes (data-width cnt-width))

;; ======================================================================

;; 3. Single-Step-Update Property

;; Specify the functionality of SHIFT-REGISTER-PISO

(defun shift-register-piso$op (x)
  (rev x))

(defthm append-of-shift-register-piso$op-with-singleton
  (equal (append (shift-register-piso$op x) (list a))
         (shift-register-piso$op (cons a x))))

(in-theory (disable shift-register-piso$op))

;; The operation of SHIFT-REGISTER-PISO over a data sequence

(defun shift-register-piso$op-map (x)
  (if (atom x)
      nil
    (append (shift-register-piso$op (car x))
            (shift-register-piso$op-map (cdr x)))))

(defthm shift-register-piso$op-map-of-append
  (equal (shift-register-piso$op-map (append x y))
         (append (shift-register-piso$op-map x)
                 (shift-register-piso$op-map y))))

;; The extraction function for SHIFT-REGISTER-PISO

(defund shift-register-piso$extract (st)
  (b* ((r-reg (get-field *shift-register-piso$r-reg* st))
       (r-reg.s (get-field *link$s* r-reg))
       (r-reg.d (get-field *link$d* r-reg))
       (r-cnt (get-field *shift-register-piso$r-cnt* st))
       (r-cnt.d (get-field *link$d* r-cnt))
       (w-reg (get-field *shift-register-piso$w-reg* st))
       (w-reg.d (get-field *link$d* w-reg))
       (w-cnt (get-field *shift-register-piso$w-cnt* st))
       (w-cnt.d (get-field *link$d* w-cnt)))
    (if (fullp r-reg.s)
        (take (v-to-nat (strip-cars r-cnt.d))
              (strip-cars r-reg.d))
      (take (v-to-nat (strip-cars w-cnt.d))
            (strip-cars w-reg.d)))))

(local
 (defthm v-to-nat-of-v-zp
   (equal (v-zp x)
          (equal (v-to-nat x) 0))
   :hints (("Goal" :in-theory (enable v-zp v-nzp v-to-nat)))))

(defthm shift-register-piso$extract-not-empty
  (implies (and (shift-register-piso$out-act inputs st data-width)
                (shift-register-piso$valid-st st data-width cnt-width))
           (< 0 (len (shift-register-piso$extract st))))
  :hints (("Goal"
           :in-theory (e/d (f-and3
                            f-or3
                            shift-register-piso$valid-st
                            shift-register-piso$extract
                            shift-register-piso$out-act)
                           ())))
  :rule-classes :linear)

(defthmd len-of-shift-register-piso$extract-lemma
  (implies (and (shift-register-piso$in-act inputs st data-width)
                (shift-register-piso$valid-st st data-width cnt-width))
           (equal (len (shift-register-piso$extract st))
                  0))
  :hints (("Goal" :in-theory (e/d (f-and4
                                   shift-register-piso$valid-st
                                   shift-register-piso$in-act
                                   shift-register-piso$extract)
                                  ()))))

(defthm len-of-shift-register-piso$extract-contrapositive-lemma-1
  (implies (and (shift-register-piso$in-act inputs st data-width)
                (< 0 (len (shift-register-piso$extract st))))
                (not (shift-register-piso$valid-st st data-width cnt-width)))
  :hints (("Goal" :in-theory (e/d (f-and4
                                   shift-register-piso$valid-st
                                   shift-register-piso$in-act
                                   shift-register-piso$extract)
                                  ()))))

(defthm len-of-shift-register-piso$extract-contrapositive-lemma-2
  (implies (and (shift-register-piso$valid-st st data-width cnt-width)
                (< 0 (len (shift-register-piso$extract st))))
                (not (shift-register-piso$in-act inputs st data-width)))
  :hints (("Goal" :in-theory (e/d (f-and4
                                   shift-register-piso$valid-st
                                   shift-register-piso$in-act
                                   shift-register-piso$extract)
                                  ()))))

;; Specify and prove a state invariant

(progn
  (defund shift-register-piso$inv (st)
    (b* ((r-reg (get-field *shift-register-piso$r-reg* st))
         (r-reg.s (get-field *link$s* r-reg))
         (r-reg.d (get-field *link$d* r-reg))
         (r-cnt (get-field *shift-register-piso$r-cnt* st))
         (r-cnt.s (get-field *link$s* r-cnt))
         (r-cnt.d (get-field *link$d* r-cnt))
         (w-reg (get-field *shift-register-piso$w-reg* st))
         (w-reg.s (get-field *link$s* w-reg))
         (w-reg.d (get-field *link$d* w-reg))
         (w-cnt (get-field *shift-register-piso$w-cnt* st))
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

  (local
   (defthm shift-register-piso$input-format-lemma-1
     (implies (shift-register-piso$input-format inputs data-width)
              (booleanp (nth 0 inputs)))
     :hints (("Goal" :in-theory (enable shift-register-piso$input-format)))
     :rule-classes :type-prescription))

  (local
   (defthm shift-register-piso$input-format-lemma-2
     (implies (shift-register-piso$input-format inputs data-width)
              (booleanp (nth 1 inputs)))
     :hints (("Goal" :in-theory (enable shift-register-piso$input-format)))
     :rule-classes :type-prescription))

  (local
   (defthm shift-register-piso$input-format-lemma-3
     (implies (and (shift-register-piso$input-format inputs data-width)
                   (nth 0 inputs))
              (bvp (shift-register-piso$data-in inputs data-width)))
     :hints (("Goal" :in-theory (enable shift-register-piso$input-format)))))

  (defthm len-of-shift-register-piso$extract-upper-bound
    (implies (and (shift-register-piso$valid-st st data-width cnt-width)
                  (shift-register-piso$inv st))
             (<= (len (shift-register-piso$extract st))
                 data-width))
    :hints (("Goal" :in-theory (e/d (shift-register-piso$valid-st
                                     shift-register-piso$inv
                                     shift-register-piso$extract)
                                    ())))
    :rule-classes :linear)

  (local
   (defthm v-to-nat-of-repeat-lemma
     (equal (v-to-nat (append (repeat n nil) '(t)))
            (expt 2 (nfix n)))
     :hints (("Goal" :in-theory (enable v-to-nat repeat)))))

  (defthm shift-register-piso$inv-preserved
    (implies (and (shift-register-piso$input-format inputs data-width)
                  (shift-register-piso$valid-st st data-width cnt-width)
                  (shift-register-piso$inv st))
             (shift-register-piso$inv
              (shift-register-piso$step inputs st data-width cnt-width)))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              bvp
                              shift-register-piso$valid-st
                              shift-register-piso$inv
                              shift-register-piso$step
                              shift-register-piso$in-act
                              shift-register-piso$out-act)
                             ()))))
  )

;; The extracted next-state function for SHIFT-REGISTER-PISO.  Note that this
;; function avoids exploring the internal computation of SHIFT-REGISTER-PISO.

(defund shift-register-piso$extracted-step (inputs st data-width)
  (b* ((data (shift-register-piso$data-in inputs data-width))
       (extracted-st (shift-register-piso$extract st)))
    (cond
     ((equal (shift-register-piso$out-act inputs st data-width) t)
      (cdr extracted-st))
     ((equal (shift-register-piso$in-act inputs st data-width) t)
      data)
     (t extracted-st))))

;; The single-step-update property

(progn
  (local
   (defthm len-cdr
     (implies (< 0 (len x))
              (equal (len (cdr x))
                     (1- (len x))))))

  (defthm shift-register-piso$extracted-step-correct
    (b* ((next-st (shift-register-piso$step inputs st data-width cnt-width)))
      (implies (and (shift-register-piso$input-format inputs data-width)
                    (shift-register-piso$valid-st st data-width cnt-width)
                    (shift-register-piso$inv st))
               (equal (shift-register-piso$extract next-st)
                      (shift-register-piso$extracted-step inputs st data-width))))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              joint-act
                              bvp
                              pos-len=>cons
                              shift-register-piso$extracted-step
                              shift-register-piso$valid-st
                              shift-register-piso$inv
                              shift-register-piso$step
                              shift-register-piso$in-act
                              shift-register-piso$out-act
                              shift-register-piso$extract)
                             ()))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that shift-register-piso$valid-st is an invariant.

(defthm shift-register-piso$valid-st-preserved
  (implies (and (shift-register-piso$input-format inputs data-width)
                (shift-register-piso$valid-st st data-width cnt-width))
           (shift-register-piso$valid-st
            (shift-register-piso$step inputs st data-width cnt-width)
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
                            shift-register-piso$st-format
                            shift-register-piso$valid-st
                            shift-register-piso$step
                            shift-register-piso$in-act
                            shift-register-piso$out-act)
                           (if*
                            v-threefix)))))

(defthm shift-register-piso$extract-lemma
  (implies (and (shift-register-piso$out-act inputs st data-width)
                (shift-register-piso$valid-st st data-width cnt-width))
           (equal (shift-register-piso$bit-out st)
                  (car (shift-register-piso$extract st))))
  :hints (("Goal" :in-theory (e/d (f-and3
                                   booleanp-car-of-bv
                                   shift-register-piso$out-act
                                   shift-register-piso$valid-st
                                   shift-register-piso$bit-out
                                   shift-register-piso$extract)
                                  ()))))

(defthm booleanp-car-of-shift-register-piso$extract
  (implies (and (shift-register-piso$out-act inputs st data-width)
                (shift-register-piso$valid-st st data-width cnt-width))
           (booleanp (car (shift-register-piso$extract st))))
  :hints (("Goal"
           :use shift-register-piso$extract-lemma
           :in-theory (e/d ()
                           (shift-register-piso$extract-lemma))))
  :rule-classes :type-prescription)

;; Extract the accepted input sequence

(seq-gen shift-register-piso in in-act 0
         (shift-register-piso$data-in inputs data-width)
         :sizes (data-width cnt-width))

;; Extract the valid output sequence

(seq-gen shift-register-piso out out-act 1
         (shift-register-piso$bit-out st)
         :netlist-data (nth 2 outputs)
         :sizes (data-width cnt-width))

;; The multi-step input-output relationship

(encapsulate
  ()

  (local
   (defthm shift-register-piso$op-of-len-0
     (implies (equal (len x) 0)
              (not (shift-register-piso$op x)))
     :hints (("Goal" :in-theory (enable shift-register-piso$op)))))

  (local
   (defthm shift-register-piso$dataflow-correct-aux
     (implies (equal (append x y1)
                     (append (shift-register-piso$op-map seq) y2))
              (equal (append x y1 z)
                     (append (shift-register-piso$op-map seq)
                             y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (acl2::associativity-of-append))))))

  (defthmd shift-register-piso$dataflow-correct
    (b* ((extracted-st (shift-register-piso$extract st))
         (final-st (shift-register-piso$run
                    inputs-seq st data-width cnt-width n))
         (final-extracted-st (shift-register-piso$extract final-st)))
      (implies
       (and (shift-register-piso$input-format-n inputs-seq data-width n)
            (shift-register-piso$valid-st st data-width cnt-width)
            (shift-register-piso$inv st))
       (equal (append (shift-register-piso$op final-extracted-st)
                      (shift-register-piso$out-seq
                       inputs-seq st data-width cnt-width n))
              (append (shift-register-piso$op-map
                       (shift-register-piso$in-seq
                        inputs-seq st data-width cnt-width n))
                      (shift-register-piso$op extracted-st)))))
    :hints (("Goal"
             :in-theory (enable pos-len=>cons
                                len-of-shift-register-piso$extract-lemma
                                shift-register-piso$extracted-step))))

  (defthmd shift-register-piso$functionally-correct
    (b* ((extracted-st (shift-register-piso$extract st))
         (final-st (de-n (si 'shift-register-piso data-width)
                         inputs-seq st netlist n))
         (final-extracted-st (shift-register-piso$extract final-st)))
      (implies
       (and (shift-register-piso& netlist data-width cnt-width)
            (shift-register-piso$input-format-n inputs-seq data-width n)
            (shift-register-piso$valid-st st data-width cnt-width)
            (shift-register-piso$inv st))
       (equal (append (shift-register-piso$op final-extracted-st)
                      (shift-register-piso$netlist-out-seq
                       inputs-seq st netlist data-width n))
              (append (shift-register-piso$op-map
                       (shift-register-piso$netlist-in-seq
                        inputs-seq st netlist data-width n))
                      (shift-register-piso$op extracted-st)))))
    :hints (("Goal"
             :use shift-register-piso$dataflow-correct
             :in-theory (enable shift-register-piso$valid-st=>st-format
                                shift-register-piso$de-n))))
  )

