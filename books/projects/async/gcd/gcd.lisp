;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; February 2018

(in-package "ADE")

(include-book "gcd-cond")
(include-book "../merge")
(include-book "../store-n")
(include-book "../adders/add-sub")
(include-book "../comparators/v-less")

(local (include-book "gcd-alg"))
(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of GCD-OP
;;; 2. DE Module Generator of GCD
;;; 3. Specifying the Final State of GCD After An N-Step Execution
;;; 4. Single-Step-Update Property
;;; 5. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of GCD-OP
;;
;; GCD-OP performs the gcd operation in one iteration.

(defconst *gcd-op$go-num* 1)

(defun gcd-op$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun gcd-op$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (gcd-op$data-ins-len data-width)
     *gcd-op$go-num*))

(module-generator
 gcd-op* (data-width)
 (si 'gcd-op data-width)
 (list* 'full-in 'empty-out-
        (append (sis 'data-in 0 (* 2 data-width))
                (sis 'go 0 *gcd-op$go-num*)))
 (list* 'act 'act0 'act1
        (sis 'data-out 0 (* 2 data-width)))
 ()
 (list
  (list 'a<b?
        '(a<b)
        (si 'v-< data-width)
        (append (rev (sis 'data-in 0 data-width))
                (rev (sis 'data-in data-width data-width))))

  '(g0 (high) vdd ())
  (list 'a-b
        (sis 'a-b 0 (1+ data-width))
        (si 'ripple-add/sub data-width)
        (cons 'high
              (append (sis 'data-in 0 data-width)
                      (sis 'data-in data-width data-width))))
  (list 'out0
        (sis 'data-out0 0 (* 2 data-width))
        (si 'v-buf (* 2 data-width))
        (append (sis 'a-b 0 data-width)
                (sis 'data-in data-width data-width)))
  (list 'b-a
        (sis 'b-a 0 (1+ data-width))
        (si 'ripple-add/sub data-width)
        (cons 'high
              (append (sis 'data-in data-width data-width)
                      (sis 'data-in 0 data-width))))
  (list 'out1
        (sis 'data-out1 0 (* 2 data-width))
        (si 'v-buf (* 2 data-width))
        (append (sis 'data-in 0 data-width)
                (sis 'b-a 0 data-width)))

  (list 'me
        (list* 'act 'act0 'act1
               (sis 'data-out 0 (* 2 data-width)))
        (si 'merge (* 2 data-width))
        (list* 'full-in 'full-in 'empty-out- 'a<b
               (append (sis 'data-out0 0 (* 2 data-width))
                       (sis 'data-out1 0 (* 2 data-width))
                       (sis 'go 0 *merge$go-num*)))))
 :guard (natp data-width))

;; DE netlist generator. A generated netlist will contain an instance of GCD-OP.

(defun gcd-op$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (gcd-op* data-width)
        (union$ (merge$netlist (* 2 data-width))
                (v-buf$netlist (* 2 data-width))
                (v-<$netlist data-width)
                (ripple-add/sub$netlist data-width)
                :test 'equal)))

;; Sanity syntactic check

(defthmd gcd-op$netlist-64-okp
  (and (net-syntax-okp (gcd-op$netlist 64))
       (net-arity-okp (gcd-op$netlist 64))))

;; Recognizer for GCD-OP

(defund gcd-op& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (and (equal (assoc (si 'gcd-op data-width) netlist)
              (gcd-op* data-width))
       (b* ((netlist (delete-to-eq (si 'gcd-op data-width) netlist)))
         (and (merge& netlist (* 2 data-width))
              (v-buf& netlist (* 2 data-width))
              (v-<& netlist data-width)
              (ripple-add/sub& netlist data-width)))))

;; Sanity check

(defthm check-gcd-op$netlist-64
  (gcd-op& (gcd-op$netlist 64) 64))

;; Extracting the input data

(defun gcd-op$data-in (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (take (* 2 (mbe :logic (nfix data-width)
                  :exec  data-width))
        (nthcdr 2 inputs)))

(defthm len-gcd-op$data-in
  (equal (len (gcd-op$data-in inputs data-width))
         (* 2 (nfix data-width))))

(in-theory (disable gcd-op$data-in))

;; Extracting the "a<b" signal

(defund gcd-op$a<b (inputs data-width)
  (b* ((data-in (gcd-op$data-in inputs data-width)))
    (fv-< nil t
          (rev (take data-width data-in))
          (rev (nthcdr data-width data-in)))))

;; Extracting the 1st input data item for the merge

(defund gcd-op$data-out0 (inputs data-width)
  (b* ((data-in (gcd-op$data-in inputs data-width)))
    (v-threefix
     (append (take data-width
                   (fv-adder t
                             (take data-width data-in)
                             (fv-not (nthcdr data-width data-in))))
             (nthcdr data-width data-in)))))

(defthm len-gcd-op$data-out0
  (equal (len (gcd-op$data-out0 inputs data-width))
         (* 2 (nfix data-width)))
  :hints (("Goal" :in-theory (enable gcd-op$data-out0))))

(defthm bvp-gcd-op$data-out0
  (implies (bvp (gcd-op$data-in inputs data-width))
           (bvp (gcd-op$data-out0 inputs data-width)))
  :hints (("Goal" :in-theory (enable gcd-op$data-out0))))

;; Extracting the 2nd input data item for the merge

(defund gcd-op$data-out1 (inputs data-width)
  (b* ((data-in (gcd-op$data-in inputs data-width)))
    (v-threefix
     (append (take data-width data-in)
             (take data-width
                   (fv-adder t
                             (nthcdr data-width data-in)
                             (fv-not (take data-width data-in))))))))

(defthm len-gcd-op$data-out1
  (equal (len (gcd-op$data-out1 inputs data-width))
         (* 2 (nfix data-width)))
  :hints (("Goal" :in-theory (enable gcd-op$data-out1))))

(defthm bvp-gcd-op$data-out1
  (implies (bvp (gcd-op$data-in inputs data-width))
           (bvp (gcd-op$data-out1 inputs data-width)))
  :hints (("Goal" :in-theory (enable gcd-op$data-out1))))

;; Extracting the inputs for the merge joint

(defund gcd-op$me-inputs (inputs data-width)
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (go-signals (nthcdr (gcd-op$data-ins-len data-width) inputs))

       (a<b (gcd-op$a<b inputs data-width))
       (data-out0 (gcd-op$data-out0 inputs data-width))
       (data-out1 (gcd-op$data-out1 inputs data-width)))
    (list* full-in full-in empty-out- a<b
           (append data-out0 data-out1 go-signals))))

;; Extracting the "act0" signal

(defund gcd-op$act0 (inputs data-width)
  (merge$act0 (gcd-op$me-inputs inputs data-width)
              (* 2 data-width)))

;; Extracting the "act1" signal

(defund gcd-op$act1 (inputs data-width)
  (merge$act1 (gcd-op$me-inputs inputs data-width)
              (* 2 data-width)))

;; Extracting the "act" signal

(defund gcd-op$act (inputs data-width)
  (f-or (gcd-op$act0 inputs data-width)
        (gcd-op$act1 inputs data-width)))

;; Extracting the output data

(defund gcd-op$data-out (inputs data-width)
  (fv-if (gcd-op$a<b inputs data-width)
         (gcd-op$data-out1 inputs data-width)
         (gcd-op$data-out0 inputs data-width)))

(defthm len-gcd-op$data-out
  (equal (len (gcd-op$data-out inputs data-width))
         (* 2 (nfix data-width)))
  :hints (("Goal" :in-theory (enable gcd-op$data-out))))

(defthm bvp-gcd-op$data-out
  (implies (bvp (gcd-op$data-in inputs data-width))
           (bvp (gcd-op$data-out inputs data-width)))
  :hints (("Goal" :in-theory (enable gcd-op$a<b
                                     gcd-op$data-out))))

(not-primp-lemma gcd-op)

;; The value lemma for GCD-OP

(encapsulate
  ()

  (local
   (defthm list-of-singleton
     (implies (and (true-listp l)
                   (equal (len l) 1))
              (equal (list (car l))
                     l))))

  (defthmd gcd-op$value
    (b* ((inputs (list* full-in empty-out-
                        (append data-in go-signals))))
      (implies (and (posp data-width)
                    (gcd-op& netlist data-width)
                    (true-listp data-in)
                    (equal (len data-in) (* 2 data-width))
                    (true-listp go-signals)
                    (equal (len go-signals) *gcd-op$go-num*))
               (equal (se (si 'gcd-op data-width) inputs st netlist)
                      (list* (gcd-op$act inputs data-width)
                             (gcd-op$act0 inputs data-width)
                             (gcd-op$act1 inputs data-width)
                             (gcd-op$data-out inputs data-width)))))
    :hints (("Goal"
             :do-not-induct t
             :do-not '(preprocess)
             :expand (se (si 'gcd-op data-width)
                         (list* full-in empty-out-
                                (append data-in go-signals))
                         st
                         netlist)
             :in-theory (e/d (de-rules
                              get-field
                              len-1-true-listp=>true-listp
                              not-primp-gcd-op
                              gcd-op&
                              gcd-op*$destructure
                              gcd-op$data-in
                              gcd-op$me-inputs
                              gcd-op$a<b
                              gcd-op$act
                              gcd-op$act0
                              gcd-op$act1
                              gcd-op$data-out
                              gcd-op$data-out0
                              gcd-op$data-out1
                              merge$act
                              merge$value
                              v-buf$value
                              v-<$value
                              ripple-add/sub$value-2)
                             ((gcd-op*)
                              append-take-nthcdr
                              validp
                              fullp
                              emptyp
                              de-module-disabled-rules)))))
  )

;; ======================================================================

;; 2. DE Module Generator of GCD
;;
;; Constructing a DE module generator that computes the Greatest Common Divisor
;; (GCD) of two natural numbers. Proving the value and state lemmas for this
;; module generator. We follow the link-joint model in building this generator;
;; and a generated module contains a feedback loop in its data flows.

(defconst *gcd$go-num* 3)
(defconst *gcd$st-len* 8)

(defun gcd$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun gcd$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (gcd$data-ins-len data-width)
     *gcd$go-num*))

;; DE module generator of GCD. It reports the "in-act" signal at its input port,
;; and the "out-act" signal and output data at its output port.

(module-generator
 gcd* (data-width)
 (si 'gcd data-width)
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 (* 2 data-width))
                                     (sis 'go 0 *gcd$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-width))
 '(ls s l0 d0 l1 d1 l2 d2)
 (list
  ;; LINKS
  ;; S
  '(ls (s-status) link-cntl (branch-act merge-act))
  '(s (s-out s-out~) latch (branch-act done-))

  ;; L0
  '(l0 (l0-status) link-cntl (merge-act branch-act))
  (list 'd0
        (sis 'd0-out 0 (* 2 data-width))
        (si 'latch-n (* 2 data-width))
        (cons 'merge-act (sis 'd0-in 0 (* 2 data-width))))

  ;; L1
  '(l1 (l1-status) link-cntl (branch-act1 op-act))
  (list 'd1
        (sis 'd1-out 0 (* 2 data-width))
        (si 'latch-n (* 2 data-width))
        (cons 'branch-act1 (sis 'd1-in 0 (* 2 data-width))))

  ;; L2
  '(l2 (l2-status) link-cntl (op-act merge-act1))
  (list 'd2
        (sis 'd2-out 0 (* 2 data-width))
        (si 'latch-n (* 2 data-width))
        (cons 'op-act (sis 'd2-in 0 (* 2 data-width))))

  ;; JOINTS
  ;; Merge-in
  '(me-ready-in0 (me-full-in0) b-and (full-in s-status))
  '(me-ready-in1 (me-full-in1) b-and (l2-status s-status))
  (list 'me
        (list* 'merge-act 'in-act 'merge-act1
               (sis 'd0-in 0 (* 2 data-width)))
        (si 'merge (* 2 data-width))
        (list* 'me-full-in0 'me-full-in1 'l0-status 's-out
               (append (sis 'data-in 0 (* 2 data-width))
                       (sis 'd2-out 0 (* 2 data-width))
                       (sis 'go 0 *merge$go-num*))))

  ;; Branch-out
  '(br-ready-out0 (br-empty-out0-) b-or (empty-out- s-status))
  '(br-ready-out1 (br-empty-out1-) b-or (l1-status s-status))
  (list 'branch-out
        (list* 'branch-act 'out-act 'branch-act1 'done-
               (append (sis 'data-out 0 data-width)
                       (sis 'd1-in 0 (* 2 data-width))))
        (si 'gcd-cond data-width)
        (list* 'l0-status 'br-empty-out0- 'br-empty-out1-
               (append (sis 'd0-out 0 (* 2 data-width))
                       (sis 'go 1 *gcd-cond$go-num*))))

  ;; Op
  (list 'op
        (list* 'op-act 'op-act0 'op-act1
               (sis 'd2-in 0 (* 2 data-width)))
        (si 'gcd-op data-width)
        (list* 'l1-status 'l2-status
               (append (sis 'd1-out 0 (* 2 data-width))
                       (sis 'go 2 *gcd-op$go-num*)))))

 :guard (natp data-width))

;; DE netlist generator. A generated netlist will contain an instance of GCD.

(defun gcd$netlist (data-width)
  (declare (xargs :guard (and (natp data-width)
                              (<= 2 data-width))))
  (cons (gcd* data-width)
        (union$ (gcd-cond$netlist data-width)
                (gcd-op$netlist data-width)
                (latch-n$netlist (* 2 data-width))
                :test 'equal)))

;; Sanity syntactic check

(defthmd gcd$netlist-64-okp
  (and (net-syntax-okp (gcd$netlist 64))
       (net-arity-okp (gcd$netlist 64))))

;; Recognizer for GCD

(defund gcd& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width)
                              (<= 2 data-width))))
  (and (equal (assoc (si 'gcd data-width) netlist)
              (gcd* data-width))
       (b* ((netlist (delete-to-eq (si 'gcd data-width) netlist)))
         (and (gcd-cond& netlist data-width)
              (gcd-op& netlist data-width)
              (merge& netlist (* 2 data-width))
              (latch-n& netlist (* 2 data-width))))))

;; Sanity check

(defthm check-gcd$netlist-64
  (gcd& (gcd$netlist 64) 64))

(defconst *gcd$ls* 0)
(defconst *gcd$s*  1)
(defconst *gcd$l0* 2)
(defconst *gcd$d0* 3)
(defconst *gcd$l1* 4)
(defconst *gcd$d1* 5)
(defconst *gcd$l2* 6)
(defconst *gcd$d2* 7)

;; Constraints on the state of GCD

(defund gcd$valid-st (st data-width)
  (b* ((ls (get-field *gcd$ls* st))
       (s  (get-field *gcd$s* st))
       (l0 (get-field *gcd$l0* st))
       (d0 (get-field *gcd$d0* st))
       (l1 (get-field *gcd$l1* st))
       (d1 (get-field *gcd$d1* st))
       (l2 (get-field *gcd$l2* st))
       (d2 (get-field *gcd$d2* st)))
    (and (natp data-width)
         (<= 3 data-width)

         (validp ls)
         (or (emptyp ls)
             (booleanp (car s)))

         (validp l0)
         (len-1-true-listp d0)
         (equal (len d0) (* 2 data-width))
         (or (emptyp l0)
             (bvp (strip-cars d0)))

         (validp l1)
         (len-1-true-listp d1)
         (equal (len d1) (* 2 data-width))
         (or (emptyp l1)
             (bvp (strip-cars d1)))

         (validp l2)
         (len-1-true-listp d2)
         (equal (len d2) (* 2 data-width))
         (or (emptyp l2)
             (bvp (strip-cars d2))))))

(defthmd gcd$valid-st=>data-width-constraint
  (implies (gcd$valid-st st data-width)
           (and (natp data-width)
                (<= 3 data-width)))
  :hints (("Goal" :in-theory (enable gcd$valid-st)))
  :rule-classes :forward-chaining)

;; GCD simulator

(progn
  (defun gcd$map-to-links (st)
    (b* ((ls (get-field *gcd$ls* st))
         (s  (get-field *gcd$s* st))
         (l0 (get-field *gcd$l0* st))
         (d0 (get-field *gcd$d0* st))
         (l1 (get-field *gcd$l1* st))
         (d1 (get-field *gcd$d1* st))
         (l2 (get-field *gcd$l2* st))
         (d2 (get-field *gcd$d2* st)))
      (map-to-links (list (list 's ls (list s))
                          (list 'l0 l0 d0)
                          (list 'l1 l1 d1)
                          (list 'l2 l2 d2)))))

  (defun gcd$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (gcd$map-to-links (car x))
            (gcd$map-to-links-list (cdr x)))))

  (defund gcd$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (gcd$ins-len data-width))
         ((mv inputs-lst state)
          (signal-vals-gen num-signals n state nil))
         ;;(- (cw "~x0~%" inputs-lst))
         (full '(t))
         (empty '(nil))
         (invalid-data (make-list (* 2 data-width) :initial-element '(x)))
         (st (list full '(nil)
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data)))
      (mv (pretty-list
           (remove-dup-neighbors
            (gcd$map-to-links-list
             (de-sim-list (si 'gcd data-width)
                          inputs-lst
                          st
                          (gcd$netlist data-width))))
           0)
          state)))
  )

;; Extracting the input data

(defun gcd$data-in (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (take (* 2 (mbe :logic (nfix data-width)
                  :exec  data-width))
        (nthcdr 2 inputs)))

(defthm len-gcd$data-in
  (equal (len (gcd$data-in inputs data-width))
         (* 2 (nfix data-width))))

(in-theory (disable gcd$data-in))

;; Extracting the inputs for the merge-in joint

(defund gcd$me-inputs (inputs st data-width)
  (b* ((full-in (nth 0 inputs))
       (data-in (gcd$data-in inputs data-width))
       (go-signals (nthcdr (gcd$data-ins-len data-width) inputs))

       (me-go-signals (take *merge$go-num* go-signals))

       (ls (get-field *gcd$ls* st))
       (s  (get-field *gcd$s* st))
       (l0 (get-field *gcd$l0* st))
       (l2 (get-field *gcd$l2* st))
       (d2 (get-field *gcd$d2* st))

       (me-full-in0 (f-and full-in (car ls)))
       (me-full-in1 (f-and (car l2) (car ls))))

    (list* me-full-in0 me-full-in1 (car l0) (car s)
           (append data-in
                   (v-threefix (strip-cars d2))
                   me-go-signals))))

;; Extracting the inputs for the branch-out joint

(defund gcd$br-inputs (inputs st data-width)
  (b* ((empty-out- (nth 1 inputs))
       (go-signals (nthcdr (gcd$data-ins-len data-width) inputs))

       (br-go-signals (take *gcd-cond$go-num*
                            (nthcdr *merge$go-num* go-signals)))

       (ls (get-field *gcd$ls* st))
       (l0 (get-field *gcd$l0* st))
       (d0 (get-field *gcd$d0* st))
       (l1 (get-field *gcd$l1* st))

       (br-empty-out0- (f-or empty-out- (car ls)))
       (br-empty-out1- (f-or (car l1) (car ls))))

    (list* (car l0) br-empty-out0- br-empty-out1-
           (append (v-threefix (strip-cars d0))
                   br-go-signals))))

;; Extracting the inputs for the "op" joint

(defund gcd$op-inputs (inputs st data-width)
  (b* ((go-signals (nthcdr (gcd$data-ins-len data-width) inputs))

       (op-go-signals (take *gcd-op$go-num*
                            (nthcdr (+ *merge$go-num*
                                       *gcd-cond$go-num*)
                                    go-signals)))

       (l1 (get-field *gcd$l1* st))
       (d1 (get-field *gcd$d1* st))
       (l2 (get-field *gcd$l2* st)))

    (list* (car l1) (car l2)
           (append (v-threefix (strip-cars d1))
                   op-go-signals))))

;; Extracting the "in-act" signal

(defund gcd$in-act (inputs st data-width)
  (merge$act0 (gcd$me-inputs inputs st data-width)
              (* 2 data-width)))

;; Extracting the "out-act" signal

(defund gcd$out-act (inputs st data-width)
  (gcd-cond$act0 (gcd$br-inputs inputs st data-width)
                 data-width))

;; Extracting the output data

(defund gcd$data-out (inputs st data-width)
  (gcd-cond$data-out0 (gcd$br-inputs inputs st data-width)
                      data-width))

(defthm len-gcd$data-out
  (implies (gcd$valid-st st data-width)
           (equal (len (gcd$data-out inputs st data-width))
                  data-width))
  :hints (("Goal" :in-theory (enable gcd$valid-st
                                     gcd$data-out))))

(defthm bvp-gcd$data-out
  (implies (and (gcd$valid-st st data-width)
                (gcd$out-act inputs st data-width))
           (bvp (gcd$data-out inputs st data-width)))
  :hints (("Goal" :in-theory (enable gcd$valid-st
                                     gcd$out-act
                                     gcd$data-out
                                     gcd$br-inputs
                                     gcd-cond$br-inputs
                                     gcd-cond$act0
                                     gcd-cond$data-in
                                     branch$act0))))

(not-primp-lemma gcd)

(encapsulate
  ()

  (local
   (defthm validp=>f-buf-canceled
     (implies (validp x)
              (equal (f-buf (car x))
                     (car x)))))

  ;; The value lemma for GCD

  (defthmd gcd$value
    (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
      (implies (and (gcd& netlist data-width)
                    (true-listp data-in)
                    (equal (len data-in) (* 2 data-width))
                    (true-listp go-signals)
                    (equal (len go-signals) *gcd$go-num*)
                    (gcd$valid-st st data-width))
               (equal (se (si 'gcd data-width) inputs st netlist)
                      (list* (gcd$in-act inputs st data-width)
                             (gcd$out-act inputs st data-width)
                             (gcd$data-out inputs st data-width)))))
    :hints (("Goal"
             :do-not-induct t
             :do-not '(preprocess)
             :expand (se (si 'gcd data-width)
                         (list* full-in empty-out-
                                (append data-in go-signals))
                         st
                         netlist)
             :in-theory (e/d (de-rules
                              nthcdr-of-pos-const-idx
                              get-field
                              len-1-true-listp=>true-listp
                              not-primp-gcd
                              gcd&
                              gcd*$destructure
                              gcd$data-in
                              merge$act0
                              branch$value
                              merge$value
                              gcd-cond$value
                              gcd-op$value
                              latch-n$value
                              gcd$valid-st
                              gcd$in-act
                              gcd$out-act
                              gcd$data-out
                              gcd$br-inputs
                              gcd$me-inputs)
                             ((gcd*)
                              nfix
                              acl2::take-of-append
                              if*
                              b-not
                              cons-equal
                              validp
                              fullp
                              emptyp
                              de-module-disabled-rules)))))

  ;; This function specifies the next state of GCD.

  (defun gcd$state-fn (inputs st data-width)
    (b* ((data-in (gcd$data-in inputs data-width))

         (ls (get-field *gcd$ls* st))
         (s  (get-field *gcd$s* st))
         (l0 (get-field *gcd$l0* st))
         (d0 (get-field *gcd$d0* st))
         (l1 (get-field *gcd$l1* st))
         (d1 (get-field *gcd$d1* st))
         (l2 (get-field *gcd$l2* st))
         (d2 (get-field *gcd$d2* st))

         (me-inputs (gcd$me-inputs inputs st data-width))
         (br-inputs (gcd$br-inputs inputs st data-width))
         (op-inputs (gcd$op-inputs inputs st data-width))

         (d1-in (gcd-cond$data-out1 br-inputs data-width))
         (d2-in (gcd-op$data-out op-inputs data-width))

         (done- (gcd-cond$flag br-inputs data-width))
         (merge-act1 (merge$act1 me-inputs (* 2 data-width)))
         (merge-act (merge$act me-inputs (* 2 data-width)))
         (branch-act1 (gcd-cond$act1 br-inputs data-width))
         (branch-act (gcd-cond$act br-inputs data-width))
         (op-act (gcd-op$act op-inputs data-width)))
      (list
       ;; S
       (list (f-sr branch-act merge-act (car ls)))
       (list (f-if branch-act done- (car s)))

       ;; L0
       (list (f-sr merge-act branch-act (car l0)))
       (pairlis$ (fv-if merge-act
                        (fv-if (car s) (strip-cars d2) data-in)
                        (strip-cars d0))
                 nil)

       ;; L1
       (list (f-sr branch-act1 op-act (car l1)))
       (pairlis$ (fv-if branch-act1 d1-in (strip-cars d1))
                 nil)

       ;; L2
       (list (f-sr op-act merge-act1 (car l2)))
       (pairlis$ (fv-if op-act d2-in (strip-cars d2))
                 nil))))

  (defthm len-of-gcd$state-fn
    (equal (len (gcd$state-fn inputs st data-width))
           *gcd$st-len*))

  ;; The state lemma for GCD

  (defthmd gcd$state
    (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
      (implies (and (gcd& netlist data-width)
                    (true-listp data-in)
                    (equal (len data-in) (* 2 data-width))
                    (true-listp go-signals)
                    (equal (len go-signals) *gcd$go-num*)
                    (gcd$valid-st st data-width))
               (equal (de (si 'gcd data-width) inputs st netlist)
                      (gcd$state-fn inputs st data-width))))
    :hints (("Goal"
             :do-not-induct t
             :do-not '(preprocess)
             :expand (de (si 'gcd data-width)
                         (list* full-in empty-out-
                                (append data-in go-signals))
                         st
                         netlist)
             :in-theory (e/d (de-rules
                              nthcdr-of-pos-const-idx
                              get-field
                              len-1-true-listp=>true-listp
                              not-primp-gcd
                              gcd&
                              gcd*$destructure
                              merge$act
                              merge$act0
                              merge$act1
                              merge$value
                              gcd$valid-st
                              gcd$data-in
                              gcd$data-out
                              gcd$br-inputs
                              gcd$me-inputs
                              gcd$op-inputs
                              gcd-cond$value
                              gcd-op$value
                              latch-n$value latch-n$state)
                             ((gcd*)
                              nfix
                              if*
                              b-not
                              append-take-nthcdr
                              acl2::take-of-append
                              acl2::prefer-positive-addends-equal
                              acl2::simplify-sums-equal
                              acl2::simplify-products-gather-exponents-equal
                              acl2::|(equal (- x) (- y))|
                              append
                              cons-equal
                              true-listp
                              validp
                              fullp
                              emptyp
                              de-module-disabled-rules)))))

  (in-theory (disable gcd$state-fn))
  )

;; ======================================================================

;; 3. Specifying the Final State of GCD After An N-Step Execution

;; Conditions on the inputs

(defund gcd$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (gcd$data-in inputs data-width))
       (go-signals (nthcdr (gcd$data-ins-len data-width) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *gcd$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

;; Proving that gcd$valid-st is an invariant.

(progn
  (local
   (defthm booleanp-gcd$op-act
     (b* ((op-inputs (gcd$op-inputs inputs st data-width))
          (d1 (nth *gcd$d1* st)))
       (implies (or (equal (nth *gcd$l1* st) '(nil))
                    (and (equal (nth *gcd$l1* st) '(t))
                         (equal (nth *gcd$l2* st) '(nil))
                         (equal (len d1) (* 2 data-width))
                         (bvp (strip-cars d1))))
                (booleanp (gcd-op$act op-inputs data-width))))
     :hints (("Goal" :in-theory (enable get-field
                                        merge$act0
                                        merge$act1
                                        gcd-op$data-in
                                        gcd-op$me-inputs
                                        gcd-op$act
                                        gcd-op$act0
                                        gcd-op$act1
                                        gcd-op$a<b
                                        gcd$op-inputs)))
     :rule-classes :type-prescription))

  (local
   (defthm gcd$op-act-nil
     (b* ((op-inputs (gcd$op-inputs inputs st data-width)))
       (implies (or (equal (nth *gcd$l1* st) '(nil))
                    (equal (nth *gcd$l2* st) '(t)))
                (not (gcd-op$act op-inputs data-width))))
     :hints (("Goal" :in-theory (enable get-field
                                        merge$act0
                                        merge$act1
                                        gcd-op$me-inputs
                                        gcd-op$act
                                        gcd-op$act0
                                        gcd-op$act1
                                        gcd$op-inputs)))))

  (local
   (defthm bvp-gcd$op-data-out
     (b* ((op-inputs (gcd$op-inputs inputs st data-width))
          (d1 (nth *gcd$d1* st)))
       (implies (and (equal (len d1) (* 2 data-width))
                     (bvp (strip-cars d1)))
                (bvp (gcd-op$data-out op-inputs data-width))))
     :hints (("Goal" :in-theory (enable get-field
                                        gcd-op$data-in
                                        gcd$op-inputs)))))

  (defthm gcd$valid-st-preserved
    (implies (and (gcd$input-format inputs data-width)
                  (gcd$valid-st st data-width))
             (gcd$valid-st (gcd$state-fn inputs st data-width)
                           data-width))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              gcd$input-format
                              gcd$valid-st
                              gcd$state-fn
                              gcd$br-inputs
                              gcd$me-inputs
                              gcd-cond$data-in
                              gcd-cond$flag
                              gcd-cond$act
                              gcd-cond$act0
                              gcd-cond$act1
                              gcd-cond$br-inputs
                              branch$act0
                              branch$act1
                              merge$act
                              merge$act0
                              merge$act1
                              f-sr)
                             (if*
                              nthcdr
                              b-if
                              b-nor3
                              acl2::true-listp-append)))))
  )

(defthmd gcd$state-alt
  (implies (and (gcd& netlist data-width)
                (gcd$input-format inputs data-width)
                (gcd$valid-st st data-width))
           (equal (de (si 'gcd data-width) inputs st netlist)
                  (gcd$state-fn inputs st data-width)))
  :hints (("Goal"
           :in-theory (enable gcd$valid-st=>data-width-constraint
                              gcd$input-format)
           :use (:instance
                 gcd$state
                 (full-in    (nth 0 inputs))
                 (empty-out- (nth 1 inputs))
                 (data-in    (gcd$data-in inputs data-width))
                 (go-signals (nthcdr (gcd$data-ins-len data-width)
                                     inputs))))))

(state-fn-n-gen gcd data-width)
(input-format-n-gen gcd data-width)

(defthmd de-sim-n$gcd
  (implies (and (gcd& netlist data-width)
                (gcd$input-format-n inputs-lst data-width n)
                (gcd$valid-st st data-width))
           (equal (de-sim-n (si 'gcd data-width)
                            inputs-lst st netlist
                            n)
                  (gcd$state-fn-n inputs-lst st data-width n)))
  :hints (("Goal" :in-theory (enable gcd$state-alt))))

;; ======================================================================

;; 4. Single-Step-Update Property

;; Specifying the functionality of GCD, i.e., computing the greatest common
;; divisor of two natural numbers (see gcd$op). Proving the correctness of
;; gcd$op.

(encapsulate
  ()

  (local
   (defthm v-<-correct-instance
     (implies (and (natp data-width)
                   (equal (len x) (* 2 data-width))
                   (bvp x)
                   (v-< nil t
                        (rev (take data-width x))
                        (rev (nthcdr data-width x))))
              (< (v-to-nat (take data-width x))
                 (v-to-nat (nthcdr data-width x))))
     :hints (("Goal"
              :use (:instance v-<-correct-1
                              (a (take data-width x))
                              (b (nthcdr data-width x)))
              :in-theory (disable v-<-correct-1)))
     :rule-classes :linear))

  (local
   (defthm v-to-nat-of-v-zp
     (implies (bvp x)
              (equal (v-zp x)
                     (equal (v-to-nat x) 0)))
     :hints (("Goal" :in-theory (enable bvp v-zp v-nzp v-to-nat)))))

  (local
   (defthm v-to-nat-of-repeat-nil-is-zero
     (equal (v-to-nat (repeat n nil)) 0)
     :hints (("Goal" :in-theory (enable v-to-nat repeat)))))

  (local
   (defthmd v-to-nat-of-take
     (implies (<= 0 n)
              (equal (v-to-nat (take n l))
                     (- (v-to-nat l)
                        (* (expt 2 n) (v-to-nat (nthcdr n l))))))
     :hints (("Goal" :in-theory (enable bvp v-to-nat)))))

  (local
   (defun nthcdr-v-adder-sub-induct (n c a b)
     (if (zp n)
         (list c a b)
       (nthcdr-v-adder-sub-induct (1- n)
                                  (b-or3 (b-and (car a) (not (car b)))
                                         (b-and (car a) c)
                                         (b-and (not (car b)) c))
                                  (cdr a)
                                  (cdr b)))))

  (local
   (defthm nthcdr-v-adder-sub-1
     (implies (and (natp n)
                   (booleanp c)
                   (equal n (len a))
                   (equal (v-to-nat b) (v-to-nat a))
                   (bv2p a b))
              (equal (nthcdr n (v-adder c a (v-not b)))
                     (list c)))
     :hints (("Goal"
              :in-theory (enable bvp v-adder v-not)))))

  (local
   (defthm nthcdr-v-adder-sub-2
     (implies (and (natp n)
                   (booleanp c)
                   (equal n (len a))
                   (< (v-to-nat b) (v-to-nat a))
                   (bv2p a b))
              (equal (nthcdr n (v-adder c a (v-not b)))
                     (list t)))
     :hints (("Goal"
              :induct (nthcdr-v-adder-sub-induct n c a b)
              :in-theory (enable bvp v-adder v-to-nat v-not)))))

  (local
   (defthm v-to-nat-of-take-of-v-adder-sub
     (implies (and (natp n)
                   (equal n (len a))
                   (<= (v-to-nat b) (v-to-nat a))
                   (bv2p a b))
              (equal (v-to-nat (take n
                                     (v-adder t a (v-not b))))
                     (- (v-to-nat a)
                        (v-to-nat b))))
     :hints (("Goal"
              :in-theory (enable v-to-nat-of-take)
              :use (:instance nthcdr-v-adder-sub-2
                              (c t))))))

  (local
   (defun my-count (x)
     (nfix (+ (v-to-nat (take (/ (len x) 2) x))
              (v-to-nat (nthcdr (/ (len x) 2) x))))))

  (local
   (defund gcd$op (x)
     (declare
      (xargs :hints (("Goal"
                      :in-theory (e/d ()
                                      (v-not-take
                                       v-not-nthcdr))))
             :measure (my-count x)))
     (b* ((data-width (/ (len x) 2))
          (a (take data-width x))
          (b (nthcdr data-width x))
          (a-b (take data-width
                     (v-adder t a (v-not b))))
          (b-a (take data-width
                     (v-adder t b (v-not a))))
          (a<b (v-< nil t (rev a) (rev b))))
       (cond
        ((or (atom x)
             (zp data-width)
             (not (bvp x)))
         x)
        ((v-zp a) b)
        ((v-zp b) a)
        ((equal a b) a)
        (t (gcd$op
            (v-if a<b
                  (append a b-a)
                  (append a-b b))))))))

  (defund gcd$op (x)
    (declare (xargs :measure (:? x)))
    (b* ((data-width (/ (len x) 2))
         (a (take data-width x))
         (b (nthcdr data-width x))
         (a-b (take data-width
                    (v-adder t a (v-not b))))
         (b-a (take data-width
                    (v-adder t b (v-not a))))
         (a<b (v-< nil t (rev a) (rev b))))
      (cond
       ((or (atom x)
            (zp data-width)
            (not (bvp x)))
        x)
       ((v-zp a) b)
       ((v-zp b) a)
       ((equal a b) a)
       (t (gcd$op
           (v-if a<b
                 (append a b-a)
                 (append a-b b)))))))

  (local
   (defthm gcd$op-lemma-aux
     (implies (and (bv2p a b)
                   (not (v-< nil t (rev a) (rev b)))
                   (equal (v-to-nat a) 0))
              (equal a b))
     :hints (("Goal" :use (v-to-nat-equality
                           v-<-correct-2)))
     :rule-classes nil))

  (defthm gcd$op-lemma
    (b* ((a (take data-width x))
         (b (nthcdr data-width x))
         (a-b (take data-width
                    (v-adder t a (v-not b))))
         (b-a (take data-width
                    (v-adder t b (v-not a))))
         (a<b (v-< nil t (rev a) (rev b))))
      (implies (and (natp data-width)
                    (equal data-width (/ (len x) 2))
                    (bvp x))
               (equal (gcd$op (v-if a<b
                                    (append a b-a)
                                    (append a-b b)))
                      (gcd$op x))))
    :hints (("Goal"
             :induct (gcd$op x)
             :in-theory (e/d (gcd$op)
                             (v-to-nat-equality
                              v-not-take
                              v-not-nthcdr)))
            ("Subgoal *1/3"
             :use (:instance
                   v-to-nat-equality
                   (a (take data-width
                            (v-adder t (take data-width x)
                                     (v-not (nthcdr data-width x)))))
                   (b (take data-width x))))
            ("Subgoal *1/2"
             :use ((:instance
                    v-to-nat-equality
                    (a (take data-width
                             (v-adder t (nthcdr data-width x)
                                      (v-not (take data-width x)))))
                    (b (nthcdr data-width x)))
                   (:instance
                    gcd$op-lemma-aux
                    (a (take data-width x))
                    (b (nthcdr data-width x)))))))

  ;; Proving that gcd$op correctly computes the greatest common divisor

  (local
   (defthm v-to-nat-of-GCD$OP-is-GCD-ALG
     (implies (and (equal data-width (/ (len x) 2))
                   (bvp x))
              (equal (v-to-nat (gcd$op x))
                     (gcd-alg (v-to-nat (take data-width x))
                              (v-to-nat (nthcdr data-width x)))))
     :hints (("Goal" :in-theory (e/d (gcd$op)
                                     (v-not-take
                                      v-not-nthcdr))))))
  )

;; The operation of GCD over an accepted input sequence

(defun gcd$op-seq (in-seq)
  (if (atom in-seq)
      nil
    (cons (gcd$op (car in-seq))
          (gcd$op-seq (cdr in-seq)))))

(defthm len-of-gcd$op-seq
  (equal (len (gcd$op-seq x))
         (len x)))

(defthm gcd$op-seq-of-append
  (equal (gcd$op-seq (append x y))
         (append (gcd$op-seq x) (gcd$op-seq y))))

;; The extraction function for GCD that extracts the future output sequence
;; from the current state.

(defund gcd$extract-state (st)
  (b* ((l0 (get-field *gcd$l0* st))
       (d0 (get-field *gcd$d0* st))
       (l1 (get-field *gcd$l1* st))
       (d1 (get-field *gcd$d1* st))
       (l2 (get-field *gcd$l2* st))
       (d2 (get-field *gcd$d2* st)))
    (gcd$op-seq
     (extract-state (list l1 d1 l2 d2 l0 d0)))))

(defthm gcd$extract-state-not-empty
  (implies (and (gcd$out-act inputs st data-width)
                (gcd$valid-st st data-width))
           (< 0 (len (gcd$extract-state st))))
  :hints (("Goal"
           :in-theory (e/d (branch$act0
                            gcd-cond$br-inputs
                            gcd-cond$act0
                            gcd$valid-st
                            gcd$extract-state
                            gcd$br-inputs
                            gcd$out-act)
                           (nfix))))
  :rule-classes :linear)

;; Specifying and proving a state invariant

(progn
  (defund gcd$inv (st)
    (b* ((ls (get-field *gcd$ls* st))
         (s  (get-field *gcd$s* st)))
      (if (and (fullp ls) (not (car s)))
          (= (len (gcd$extract-state st))
             0)
        (= (len (gcd$extract-state st))
           1))))

  (defthm gcd$inv-preserved
    (implies (and (gcd$input-format inputs data-width)
                  (gcd$valid-st st data-width)
                  (gcd$inv st))
             (gcd$inv (gcd$state-fn inputs st data-width)))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              gcd$input-format
                              gcd$valid-st
                              gcd$inv
                              gcd$state-fn
                              gcd$extract-state
                              gcd$br-inputs
                              gcd$me-inputs
                              gcd-cond$data-in
                              gcd-cond$flag
                              gcd-cond$act
                              gcd-cond$act0
                              gcd-cond$act1
                              gcd-cond$br-inputs
                              branch$act0
                              branch$act1
                              merge$act
                              merge$act0
                              merge$act1
                              f-sr)
                             (if*
                              v-if-works
                              b-nor3
                              b-not
                              nfix
                              nthcdr)))))
  )

;; Extracting the accepted input sequence

(defun gcd$in-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (gcd$in-act inputs st data-width) t)
          (append (gcd$in-seq (cdr inputs-lst)
                               (gcd$state-fn inputs st data-width)
                               data-width
                               (1- n))
                  (list (gcd$data-in inputs data-width)))
        (gcd$in-seq (cdr inputs-lst)
                     (gcd$state-fn inputs st data-width)
                     data-width
                     (1- n))))))

;; Extracting the valid output sequence

(defun gcd$out-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (gcd$out-act inputs st data-width) t)
          (append (gcd$out-seq (cdr inputs-lst)
                               (gcd$state-fn inputs st data-width)
                               data-width
                               (1- n))
                  (list (gcd$data-out inputs st data-width)))
        (gcd$out-seq (cdr inputs-lst)
                     (gcd$state-fn inputs st data-width)
                     data-width
                     (1- n))))))

;; Input-output sequence simulator

(progn
  (defun v-to-nat-split-lst (seq data-width)
    (declare (xargs :guard (and (true-list-listp seq)
                                (natp data-width))))
    (if (atom seq)
        nil
      (cons (list (v-to-nat (take data-width (car seq)))
                  (v-to-nat (nthcdr data-width (car seq))))
            (v-to-nat-split-lst (cdr seq) data-width))))

  (defund gcd$in-out-seq-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (gcd$ins-len data-width))
         ((mv inputs-lst state)
          (signal-vals-gen num-signals n state nil))
         (full '(t))
         (empty '(nil))
         (invalid-data (make-list (* 2 data-width) :initial-element '(x)))
         (st (list full '(nil)
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-split-lst
                     (gcd$in-seq inputs-lst st data-width n)
                     data-width)))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (gcd$out-seq inputs-lst st data-width n)))))
       state)))
  )

;; The extracted next-state function for GCD

(defund gcd$step-spec (inputs st data-width)
  (b* ((data (gcd$op (gcd$data-in inputs data-width)))
       (extracted-st (gcd$extract-state st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (gcd$out-act inputs st data-width) t)
      (cond
       ((equal (gcd$in-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (gcd$in-act inputs st data-width) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(progn
  (local
   (defthm gcd-op$data-out-expand
     (b* ((op-inputs (gcd$op-inputs inputs st data-width))
          (d1 (nth *gcd$d1* st)))
       (implies
        (and (natp data-width)
             (equal (len d1) (* 2 data-width))
             (bvp (strip-cars d1)))
        (equal (gcd-op$data-out op-inputs data-width)
               (v-if (v-< nil t
                          (rev (take data-width (strip-cars d1)))
                          (rev (nthcdr data-width (strip-cars d1))))
                     (append
                      (take data-width (strip-cars d1))
                      (take data-width
                            (v-adder
                             t
                             (nthcdr data-width (strip-cars d1))
                             (v-not (take data-width (strip-cars d1))))))
                     (append
                      (take data-width
                            (v-adder
                             t
                             (take data-width (strip-cars d1))
                             (v-not (nthcdr data-width (strip-cars d1)))))
                      (nthcdr data-width (strip-cars d1)))))))
     :hints (("Goal"
              :in-theory (enable get-field
                                 gcd-op$data-in
                                 gcd-op$a<b
                                 gcd-op$data-out
                                 gcd-op$data-out0
                                 gcd-op$data-out1
                                 gcd$op-inputs)))))

  (defthm gcd$step-spec-correct
    (b* ((next-st (gcd$state-fn inputs st data-width)))
      (implies (and (gcd$input-format inputs data-width)
                    (gcd$valid-st st data-width)
                    (gcd$inv st))
               (equal (gcd$extract-state next-st)
                      (gcd$step-spec inputs st data-width))))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              gcd$step-spec
                              gcd$input-format
                              gcd$valid-st
                              gcd$inv
                              gcd$state-fn
                              gcd$in-act
                              gcd$out-act
                              gcd$data-out
                              gcd$br-inputs
                              gcd$me-inputs
                              gcd$extract-state
                              gcd-cond$data-in
                              gcd-cond$flag
                              gcd-cond$act
                              gcd-cond$act0
                              gcd-cond$act1
                              gcd-cond$data-out1
                              gcd-cond$br-inputs
                              branch$act0
                              branch$act1
                              merge$act
                              merge$act0
                              merge$act1
                              f-sr)
                             (if*
                              v-if-works
                              v-not-take
                              v-not-nthcdr
                              b-if
                              b-not
                              take-of-too-many
                              acl2::simplify-products-gather-exponents-<
                              acl2::prefer-positive-addends-<
                              acl2::prefer-positive-addends-equal
                              acl2::|(< (if a b c) x)|
                              nfix)))))
  )

;; ======================================================================

;; 5. Relationship Between the Input and Output Sequences

(defthm gcd$extract-state-lemma
  (implies (and (gcd$valid-st st data-width)
                (equal n (1- (len (gcd$extract-state st))))
                (gcd$out-act inputs st data-width))
           (equal (append
                   (take n (gcd$extract-state st))
                   (list (gcd$data-out inputs st data-width)))
                  (gcd$extract-state st)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (branch$act0
                            gcd-cond$data-in
                            gcd-cond$br-inputs
                            gcd-cond$act0
                            gcd-cond$flag
                            gcd-cond$data-out0
                            gcd$valid-st
                            gcd$extract-state
                            gcd$op
                            gcd$br-inputs
                            gcd$out-act
                            gcd$data-out)
                           (v-if-works)))))

(encapsulate
  ()

  (local
   (defthm gcd$dataflow-correct-aux
     (implies (equal (append x1 y1)
                     (append (gcd$op-seq in-seq) y2))
              (equal (append x1 y1 z)
                     (append (gcd$op-seq in-seq) y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (acl2::associativity-of-append))))))

  (defthmd gcd$dataflow-correct
    (b* ((extracted-st (gcd$extract-state st))
         (final-st (gcd$state-fn-n inputs-lst st data-width n))
         (final-extracted-st (gcd$extract-state final-st)))
      (implies (and (gcd$input-format-n inputs-lst data-width n)
                    (gcd$valid-st st data-width)
                    (gcd$inv st))
               (equal (append final-extracted-st
                              (gcd$out-seq inputs-lst st data-width n))
                      (append (gcd$op-seq
                               (gcd$in-seq inputs-lst st data-width n))
                              extracted-st))))
    :hints (("Goal"
             :in-theory (e/d (gcd$step-spec)
                             ()))))
  )

