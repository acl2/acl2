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
(include-book "../adders/subtractor")
(include-book "../comparators/v-less")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of GCD-BODY2
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of GCD-BODY2
;;
;; GCD-BODY2 performs the GCD operation in one iteration.  It is constructed
;; using the ripple-carry subtractor RIPPLE-SUB.

(defconst *gcd-body2$go-num* 3)

(defun gcd-body2$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (* 2 (mbe :logic (nfix data-size)
                 :exec  data-size))))

(defun gcd-body2$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (gcd-body2$data-ins-len data-size)
     *gcd-body2$go-num*))

(module-generator
 gcd-body2* (data-size)
 (si 'gcd-body2 data-size)
 (list* 'full-in 'empty-out-
        (append (sis 'data-in 0 (* 2 data-size))
                (sis 'go 0 *gcd-body2$go-num*)))
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
    ,@(state-accessors-gen 'gcd-body2 '(l0 l1 l2) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; GCD-BODY2.

(defund gcd-body2$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (gcd-body2* data-size)
        (union$ (link$netlist data-size)
                (link$netlist (* 2 data-size))
                *joint-cntl*
                (tv-if$netlist (make-tree data-size))
                (tv-if$netlist (make-tree (* 2 data-size)))
                (v-wire$netlist (* 2 data-size))
                (v-<$netlist data-size)
                (ripple-sub$netlist data-size)
                :test 'equal)))

;; Recognizer for GCD-BODY2

(defund gcd-body2& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'gcd-body2 data-size) netlist)))
    (and (equal (assoc (si 'gcd-body2 data-size) netlist)
                (gcd-body2* data-size))
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
 (defthmd check-gcd-body2$netlist-64
   (and (net-syntax-okp (gcd-body2$netlist 64))
        (net-arity-okp (gcd-body2$netlist 64))
        (gcd-body2& (gcd-body2$netlist 64) 64))))

;; Constraints on the state of GCD-BODY2

(defund gcd-body2$st-format (st data-size)
  (b* ((l0 (nth *gcd-body2$l0* st))
       (l1 (nth *gcd-body2$l1* st))
       (l2 (nth *gcd-body2$l2* st)))
    (and (< 0 data-size)
         (link$st-format l0 (* 2 data-size))
         (link$st-format l1 data-size)
         (link$st-format l2 data-size))))

(defthm gcd-body2$st-format=>constraint
  (implies (gcd-body2$st-format st data-size)
           (posp data-size))
  :hints (("Goal" :in-theory (enable gcd-body2$st-format)))
  :rule-classes :forward-chaining)

(defund gcd-body2$valid-st (st data-size)
  (b* ((l0 (nth *gcd-body2$l0* st))
       (l1 (nth *gcd-body2$l1* st))
       (l2 (nth *gcd-body2$l2* st)))
    (and (< 0 data-size)
         (link$valid-st l0 (* 2 data-size))
         (link$valid-st l1 data-size)
         (link$valid-st l2 data-size))))

(defthmd gcd-body2$valid-st=>constraint
  (implies (gcd-body2$valid-st st data-size)
           (posp data-size))
  :hints (("Goal" :in-theory (enable gcd-body2$valid-st)))
  :rule-classes :forward-chaining)

(defthmd gcd-body2$valid-st=>st-format
  (implies (gcd-body2$valid-st st data-size)
           (gcd-body2$st-format st data-size))
  :hints (("Goal" :in-theory (e/d (gcd-body2$st-format
                                   gcd-body2$valid-st)
                                  ()))))

;; Extract the input and output signals for GCD-BODY2

(progn
  ;; Extract the input data

  (defun gcd-body2$data-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (* 2 (mbe :logic (nfix data-size)
                    :exec  data-size))
          (nthcdr 2 inputs)))

  (defthm len-gcd-body2$data-in
    (equal (len (gcd-body2$data-in inputs data-size))
           (* 2 (nfix data-size))))

  (in-theory (disable gcd-body2$data-in))

  ;; Extract the "a<b" signal

  (defund gcd-body2$a<b (inputs data-size)
    (b* ((data-in (gcd-body2$data-in inputs data-size)))
      (fv-< nil t
            (rev (take data-size data-in))
            (rev (nthcdr data-size data-in)))))

  ;; Extract the "in-act" signal

  (defund gcd-body2$in-act (inputs st data-size)
    (b* ((full-in (nth 0 inputs))
         (go-signals (nthcdr (gcd-body2$data-ins-len data-size) inputs))
         (go-in (nth 0 go-signals))

         (l0 (nth *gcd-body2$l0* st))
         (l0.s (nth *link$s* l0))
         (l1 (nth *gcd-body2$l1* st))
         (l1.s (nth *link$s* l1))

         (ready-in- (f-or (car l0.s) (car l1.s))))
      (joint-act full-in ready-in- go-in)))

  (defthm gcd-body2$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (gcd-body2$in-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable gcd-body2$in-act))))

  ;; Extract the "out-act" signal

  (defund gcd-body2$out-act (inputs st data-size)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (gcd-body2$data-ins-len data-size) inputs))
         (go-out (nth 1 go-signals))

         (l1 (nth *gcd-body2$l1* st))
         (l1.s (nth *link$s* l1))
         (l2 (nth *gcd-body2$l2* st))
         (l2.s (nth *link$s* l2))

         (ready-out (f-and (car l1.s) (car l2.s))))
      (joint-act ready-out empty-out- go-out)))

  (defthm gcd-body2$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (gcd-body2$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable gcd-body2$out-act))))

  (defthm gcd-body2$in-out-acts-mutually-exclusive
    (implies (and (gcd-body2$valid-st st data-size)
                  (gcd-body2$in-act inputs st data-size))
             (not (gcd-body2$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable gcd-body2$valid-st
                                       gcd-body2$in-act
                                       gcd-body2$out-act))))

  ;; Extract the output data

  (defund gcd-body2$data-out (st)
    (b* ((l1 (nth *gcd-body2$l1* st))
         (l1.d (nth *link$d* l1))
         (l2 (nth *gcd-body2$l2* st))
         (l2.d (nth *link$d* l2)))
      (append (v-threefix (strip-cars l2.d))
              (v-threefix (strip-cars l1.d)))))

  (defthm len-gcd-body2$data-out-1
    (implies (gcd-body2$st-format st data-size)
             (equal (len (gcd-body2$data-out st))
                    (* 2 data-size)))
    :hints (("Goal" :in-theory (enable gcd-body2$st-format
                                       gcd-body2$data-out))))

  (defthm len-gcd-body2$data-out-2
    (implies (gcd-body2$valid-st st data-size)
             (equal (len (gcd-body2$data-out st))
                    (* 2 data-size)))
    :hints (("Goal" :in-theory (enable gcd-body2$valid-st
                                       gcd-body2$data-out))))

  (defthm bvp-gcd-body2$data-out
    (implies (and (gcd-body2$valid-st st data-size)
                  (gcd-body2$out-act inputs st data-size))
             (bvp (gcd-body2$data-out st)))
    :hints (("Goal" :in-theory (enable gcd-body2$valid-st
                                       gcd-body2$out-act
                                       gcd-body2$data-out))))

  (defun gcd-body2$outputs (inputs st data-size)
    (list* (gcd-body2$in-act inputs st data-size)
           (gcd-body2$out-act inputs st data-size)
           (gcd-body2$data-out st)))
  )

;; The value lemma for GCD-BODY2

(defthm gcd-body2$value
  (b* ((inputs (list* full-in empty-out-
                      (append data-in go-signals))))
    (implies (and (gcd-body2& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-size))
                  (true-listp go-signals)
                  (equal (len go-signals) *gcd-body2$go-num*)
                  (gcd-body2$st-format st data-size))
             (equal (se (si 'gcd-body2 data-size) inputs st netlist)
                    (gcd-body2$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'gcd-body2 data-size)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            gcd-body2&
                            gcd-body2*$destructure
                            gcd-body2$st-format
                            gcd-body2$in-act
                            gcd-body2$out-act
                            gcd-body2$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of GCD-BODY2.

(defun gcd-body2$step (inputs st data-size)
  (b* ((data-in (gcd-body2$data-in inputs data-size))
       (go-signals (nthcdr (gcd-body2$data-ins-len data-size) inputs))

       (go-sub (nth 2 go-signals))

       (l0 (nth *gcd-body2$l0* st))
       (l0.s (nth *link$s* l0))
       (l0.d (nth *link$d* l0))
       (l1 (nth *gcd-body2$l1* st))
       (l2 (nth *gcd-body2$l2* st))
       (l2.s (nth *link$s* l2))

       (in-act (gcd-body2$in-act inputs st data-size))
       (out-act (gcd-body2$out-act inputs st data-size))
       (sub-act (joint-act (car l0.s) (car l2.s) go-sub))

       (a<b (gcd-body2$a<b inputs data-size))
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

;; The state lemma for GCD-BODY2

(defthm gcd-body2$state
  (b* ((inputs (list* full-in empty-out-
                      (append data-in go-signals))))
    (implies (and (gcd-body2& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-size))
                  (true-listp go-signals)
                  (equal (len go-signals) *gcd-body2$go-num*)
                  (gcd-body2$st-format st data-size))
             (equal (de (si 'gcd-body2 data-size) inputs st netlist)
                    (gcd-body2$step inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'gcd-body2 data-size)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            fv-adder-output
                            gcd-body2&
                            gcd-body2*$destructure
                            gcd-body2$st-format
                            gcd-body2$data-in
                            gcd-body2$a<b
                            gcd-body2$in-act
                            gcd-body2$out-act)
                           (associativity-of-append
                            append-take-nthcdr
                            append-v-threefix
                            de-module-disabled-rules)))))

(in-theory (disable gcd-body2$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund gcd-body2$input-format (inputs data-size)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-size))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (gcd-body2$data-in inputs data-size))
       (go-signals (nthcdr (gcd-body2$data-ins-len data-size) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in)
         (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *gcd-body2$go-num*)
     (equal inputs
            (list* full-in empty-out-
                   (append data-in go-signals))))))

(defthm booleanp-gcd-body2$in-act
  (implies (and (gcd-body2$input-format inputs data-size)
                (gcd-body2$valid-st st data-size))
           (booleanp (gcd-body2$in-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (e/d (gcd-body2$input-format
                            gcd-body2$valid-st
                            gcd-body2$in-act)
                           ())))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-gcd-body2$out-act
  (implies (and (gcd-body2$input-format inputs data-size)
                (gcd-body2$valid-st st data-size))
           (booleanp (gcd-body2$out-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (e/d (gcd-body2$input-format
                            gcd-body2$valid-st
                            gcd-body2$out-act)
                           ())))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma gcd-body2)

;; ======================================================================

;; 3. Single-Step-Update Property

;; Specify the functionality of GCD-BODY2

(defund gcd-body2$op (x)
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

;; The operation of GCD-BODY2 over a data sequence

(defun gcd-body2$op-map (x)
  (if (atom x)
      nil
    (cons (gcd-body2$op (car x))
          (gcd-body2$op-map (cdr x)))))

(defthm gcd-body2$op-map-of-append
  (equal (gcd-body2$op-map (append x y))
         (append (gcd-body2$op-map x)
                 (gcd-body2$op-map y))))

;; The extraction function for GCD-BODY2 that extracts the future output
;; sequence from the current state.

(defund gcd-body2$extract (st data-size)
  (b* ((l0 (nth *gcd-body2$l0* st))
       (l0.s (nth *link$s* l0))
       (l0.d (nth *link$d* l0))
       (l1 (nth *gcd-body2$l1* st))
       (l1.s (nth *link$s* l1))
       (l1.d (nth *link$d* l1))
       (l2 (nth *gcd-body2$l2* st))
       (l2.d (nth *link$d* l2)))
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

(defthm gcd-body2$extract-not-empty
  (implies (and (gcd-body2$out-act inputs st data-size)
                (gcd-body2$valid-st st data-size))
           (< 0 (len (gcd-body2$extract st data-size))))
  :hints (("Goal"
           :in-theory (e/d (gcd-body2$valid-st
                            gcd-body2$extract
                            gcd-body2$out-act)
                           ())))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund gcd-body2$inv (st)
    (b* ((l0 (nth *gcd-body2$l0* st))
         (l1 (nth *gcd-body2$l1* st))
         (l2 (nth *gcd-body2$l2* st))

         (len1 (len (extract-valid-data (list l0 l2))))
         (len2 (len (extract-valid-data (list l1)))))
      (equal len1 len2)))

  (defthm gcd-body2$inv-preserved
    (implies (and (gcd-body2$input-format inputs data-size)
                  (gcd-body2$valid-st st data-size)
                  (gcd-body2$inv st))
             (gcd-body2$inv
              (gcd-body2$step inputs st data-size)))
    :hints (("Goal"
             :in-theory (e/d (f-sr
                              gcd-body2$valid-st
                              gcd-body2$inv
                              gcd-body2$step
                              gcd-body2$in-act
                              gcd-body2$out-act)
                             ()))))
  )

;; The extracted next-state function for GCD-BODY2.  Note that this
;; function avoids exploring the internal computation of GCD-BODY2.

(defund gcd-body2$extracted-step (inputs st data-size)
  (b* ((data (gcd-body2$op (gcd-body2$data-in inputs data-size)))
       (extracted-st (gcd-body2$extract st data-size))
       (n (1- (len extracted-st))))
    (cond
     ((equal (gcd-body2$out-act inputs st data-size) t)
      (take n extracted-st))
     ((equal (gcd-body2$in-act inputs st data-size) t)
      (cons data extracted-st))
     (t extracted-st))))

(local
 (defthm gcd-body2$input-format-lemma-1
   (implies (gcd-body2$input-format inputs data-size)
            (booleanp (nth 0 inputs)))
   :hints (("Goal" :in-theory (enable gcd-body2$input-format)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm gcd-body2$input-format-lemma-2
   (implies (gcd-body2$input-format inputs data-size)
            (booleanp (nth 1 inputs)))
   :hints (("Goal" :in-theory (enable gcd-body2$input-format)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm gcd-body2$input-format-lemma-3
   (implies (and (gcd-body2$input-format inputs data-size)
                 (nth 0 inputs))
            (bvp (gcd-body2$data-in inputs data-size)))
   :hints (("Goal" :in-theory (enable gcd-body2$input-format)))))

;; The single-step-update property

(defthm gcd-body2$extracted-step-correct
  (b* ((next-st (gcd-body2$step inputs st data-size)))
    (implies (and (gcd-body2$input-format inputs data-size)
                  (gcd-body2$valid-st st data-size)
                  (gcd-body2$inv st))
             (equal (gcd-body2$extract next-st data-size)
                    (gcd-body2$extracted-step inputs st data-size))))
  :hints (("Goal"
           :in-theory (e/d (joint-act
                            pos-len=>cons
                            fv-if-rewrite
                            gcd-body2$extracted-step
                            gcd-body2$valid-st
                            gcd-body2$inv
                            gcd-body2$step
                            gcd-body2$a<b
                            gcd-body2$in-act
                            gcd-body2$out-act
                            gcd-body2$extract
                            gcd-body2$op)
                           ()))))

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that gcd-body2$valid-st is an invariant.

(defthm gcd-body2$valid-st-preserved
  (implies (and (gcd-body2$input-format inputs data-size)
                (gcd-body2$valid-st st data-size))
           (gcd-body2$valid-st
            (gcd-body2$step inputs st data-size)
            data-size))
  :hints (("Goal"
           :in-theory (e/d (f-sr
                            joint-act
                            gcd-body2$valid-st
                            gcd-body2$step
                            gcd-body2$a<b
                            gcd-body2$in-act
                            gcd-body2$out-act)
                           (if*)))))

(defthm gcd-body2$extract-lemma
  (implies (and (gcd-body2$valid-st st data-size)
                (gcd-body2$inv st)
                (gcd-body2$out-act inputs st data-size))
           (equal (list (gcd-body2$data-out st))
                  (nthcdr (1- (len (gcd-body2$extract st data-size)))
                          (gcd-body2$extract st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (gcd-body2$valid-st
                            gcd-body2$inv
                            gcd-body2$extract
                            gcd-body2$out-act
                            gcd-body2$data-out)
                           ()))))

;; Extract the accepted input sequence

(seq-gen gcd-body2 in in-act 0
         (gcd-body2$data-in inputs data-size))

;; Extract the valid output sequence

(seq-gen gcd-body2 out out-act 1
         (gcd-body2$data-out st)
         :netlist-data (nthcdr 2 outputs))

;; The multi-step input-output relationship

(encapsulate
  ()

  (local
   (defthm gcd-body2$dataflow-correct-aux
     (implies (equal (append x y1)
                     (append (gcd-body2$op-map seq) y2))
              (equal (append x y1 z)
                     (append (gcd-body2$op-map seq)
                             y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (associativity-of-append))))))

  (defthmd gcd-body2$dataflow-correct
    (b* ((extracted-st (gcd-body2$extract st data-size))
         (final-st (gcd-body2$run
                    inputs-seq st data-size n))
         (final-extracted-st (gcd-body2$extract final-st data-size)))
      (implies
       (and (gcd-body2$input-format-n inputs-seq data-size n)
            (gcd-body2$valid-st st data-size)
            (gcd-body2$inv st))
       (equal (append final-extracted-st
                      (gcd-body2$out-seq
                       inputs-seq st data-size n))
              (append (gcd-body2$op-map
                       (gcd-body2$in-seq
                        inputs-seq st data-size n))
                      extracted-st))))
    :hints (("Goal"
             :in-theory (enable gcd-body2$extracted-step))))

  (defthmd gcd-body2$functionally-correct
    (b* ((extracted-st (gcd-body2$extract st data-size))
         (final-st (de-n (si 'gcd-body2 data-size)
                         inputs-seq st netlist n))
         (final-extracted-st (gcd-body2$extract final-st data-size)))
      (implies
       (and (gcd-body2& netlist data-size)
            (gcd-body2$input-format-n inputs-seq data-size n)
            (gcd-body2$valid-st st data-size)
            (gcd-body2$inv st))
       (equal (append final-extracted-st
                      (gcd-body2$out-seq-netlist
                       inputs-seq st netlist data-size n))
              (append (gcd-body2$op-map
                       (gcd-body2$in-seq-netlist
                        inputs-seq st netlist data-size n))
                      extracted-st))))
    :hints (("Goal"
             :use gcd-body2$dataflow-correct
             :in-theory (enable gcd-body2$valid-st=>st-format
                                gcd-body2$de-n))))
  )



