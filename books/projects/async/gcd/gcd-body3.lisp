;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "../vector-module")
(include-book "../comparators/v-less")
(include-book "../serial-adder/serial-sub")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of GCD-BODY3
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of GCD-BODY3
;;
;; GCD-BODY3 performs the GCD operation in one iteration.  It is constructed
;; using the self-timed serial subtractor SERIAL-SUB.

(defconst *gcd-body3$prim-go-num* 2)
(defconst *gcd-body3$go-num* (+ *gcd-body3$prim-go-num*
                                *serial-sub$go-num*))

(defun gcd-body3$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (* 2 (mbe :logic (nfix data-size)
                 :exec  data-size))))

(defun gcd-body3$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (gcd-body3$data-ins-len data-size)
     *gcd-body3$go-num*))

(module-generator
 gcd-body3* (data-size)
 (si 'gcd-body3 data-size)
 (list* 'full-in 'empty-out-
        (append (sis 'data-in 0 (* 2 data-size))
                (sis 'go 0 *gcd-body3$go-num*)))
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
    ,@(state-accessors-gen 'gcd-body3 '(l0 l1 l2 sub) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; GCD-BODY3.

(defund gcd-body3$netlist (data-size cnt-size)
  (declare (xargs :guard (and (posp data-size)
                              (natp cnt-size)
                              (<= 3 cnt-size))))
  (cons (gcd-body3* data-size)
        (union$ (link$netlist (* 2 data-size))
                (tv-if$netlist (make-tree (* 2 data-size)))
                (v-wire$netlist (* 2 data-size))
                (v-<$netlist data-size)
                (serial-sub$netlist data-size cnt-size)
                :test 'equal)))

;; Recognizer for GCD-BODY3

(defund gcd-body3& (netlist data-size cnt-size)
  (declare (xargs :guard (and (alistp netlist)
                              (posp data-size)
                              (natp cnt-size)
                              (<= 3 cnt-size))))
  (b* ((subnetlist (delete-to-eq (si 'gcd-body3 data-size) netlist)))
    (and (equal (assoc (si 'gcd-body3 data-size) netlist)
                (gcd-body3* data-size))
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
 (defthmd check-gcd-body3$netlist-64-7
   (and (net-syntax-okp (gcd-body3$netlist 64 7))
        (net-arity-okp (gcd-body3$netlist 64 7))
        (gcd-body3& (gcd-body3$netlist 64 7) 64 7))))

;; Constraints on the state of GCD-BODY3

(defund gcd-body3$st-format (st data-size cnt-size)
  (b* ((l0 (nth *gcd-body3$l0* st))
       (l1 (nth *gcd-body3$l1* st))
       (l2 (nth *gcd-body3$l2* st))
       (sub (nth *gcd-body3$sub* st)))
    (and (link$st-format l0 (* 2 data-size))
         (link$st-format l1 data-size)
         (link$st-format l2 data-size)
         (serial-sub$st-format sub data-size cnt-size))))

(defthm gcd-body3$st-format=>constraint
  (implies (gcd-body3$st-format st data-size cnt-size)
           (and (posp data-size)
                (natp cnt-size)
                (<= 4 cnt-size)))
  :hints (("Goal" :in-theory (enable gcd-body3$st-format)))
  :rule-classes :forward-chaining)

(defund gcd-body3$valid-st (st data-size cnt-size)
  (b* ((l0 (nth *gcd-body3$l0* st))
       (l1 (nth *gcd-body3$l1* st))
       (l2 (nth *gcd-body3$l2* st))
       (sub (nth *gcd-body3$sub* st)))
    (and (link$valid-st l0 (* 2 data-size))
         (link$valid-st l1 data-size)
         (link$valid-st l2 data-size)
         (serial-sub$valid-st sub data-size cnt-size))))

(defthmd gcd-body3$valid-st=>constraint
  (implies (gcd-body3$valid-st st data-size cnt-size)
           (and (posp data-size)
                (natp cnt-size)
                (<= 4 cnt-size)))
  :hints (("Goal" :in-theory (enable serial-sub$valid-st=>constraint
                                     gcd-body3$valid-st)))
  :rule-classes :forward-chaining)

(defthmd gcd-body3$valid-st=>st-format
  (implies (gcd-body3$valid-st st data-size cnt-size)
           (gcd-body3$st-format st data-size cnt-size))
  :hints (("Goal" :in-theory (e/d (serial-sub$valid-st=>st-format
                                   gcd-body3$st-format
                                   gcd-body3$valid-st)
                                  ()))))

;; Extract the input and output signals for GCD-BODY3

(progn
  ;; Extract the input data

  (defun gcd-body3$data-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (* 2 (mbe :logic (nfix data-size)
                    :exec  data-size))
          (nthcdr 2 inputs)))

  (defthm len-gcd-body3$data-in
    (equal (len (gcd-body3$data-in inputs data-size))
           (* 2 (nfix data-size))))

  (in-theory (disable gcd-body3$data-in))

  ;; Extract the "a<b" signal

  (defund gcd-body3$a<b (inputs data-size)
    (b* ((data-in (gcd-body3$data-in inputs data-size)))
      (fv-< nil t
            (rev (take data-size data-in))
            (rev (nthcdr data-size data-in)))))

  ;; Extract the inputs for the SUB joint

  (defund gcd-body3$sub-inputs (inputs st data-size)
    (b* ((go-signals (nthcdr (gcd-body3$data-ins-len data-size) inputs))
         (sub-go-signals (take *serial-sub$go-num*
                               (nthcdr *gcd-body3$prim-go-num*
                                       go-signals)))

         (l0 (nth *gcd-body3$l0* st))
         (l0.s (nth *link$s* l0))
         (l0.d (nth *link$d* l0))
         (l2 (nth *gcd-body3$l2* st))
         (l2.s (nth *link$s* l2)))
      (list* (f-buf (car l0.s)) (f-buf (car l2.s))
             (append (v-threefix (take data-size (strip-cars l0.d)))
                     (v-threefix (nthcdr data-size (strip-cars l0.d)))
                     sub-go-signals))))

  ;; Extract the "in-act" signal

  (defund gcd-body3$in-act (inputs st data-size)
    (b* ((full-in (nth 0 inputs))
         (go-signals (nthcdr (gcd-body3$data-ins-len data-size) inputs))
         (go-in (nth 0 go-signals))

         (l0 (nth *gcd-body3$l0* st))
         (l0.s (nth *link$s* l0))
         (l1 (nth *gcd-body3$l1* st))
         (l1.s (nth *link$s* l1))

         (ready-in- (f-or (car l0.s) (car l1.s))))
      (joint-act full-in ready-in- go-in)))

  (defthm gcd-body3$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (gcd-body3$in-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable gcd-body3$in-act))))

  ;; Extract the "out-act" signal

  (defund gcd-body3$out-act (inputs st data-size)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (gcd-body3$data-ins-len data-size) inputs))
         (go-out (nth 1 go-signals))

         (l1 (nth *gcd-body3$l1* st))
         (l1.s (nth *link$s* l1))
         (l2 (nth *gcd-body3$l2* st))
         (l2.s (nth *link$s* l2))

         (ready-out (f-and (car l1.s) (car l2.s))))
      (joint-act ready-out empty-out- go-out)))

  (defthm gcd-body3$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (gcd-body3$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable gcd-body3$out-act))))

  (defthm gcd-body3$in-out-acts-mutually-exclusive
    (implies (and (gcd-body3$valid-st st data-size cnt-size)
                  (gcd-body3$in-act inputs st data-size))
             (not (gcd-body3$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable gcd-body3$valid-st
                                       gcd-body3$in-act
                                       gcd-body3$out-act))))

  ;; Extract the output data

  (defund gcd-body3$data-out (st)
    (b* ((l1 (nth *gcd-body3$l1* st))
         (l1.d (nth *link$d* l1))
         (l2 (nth *gcd-body3$l2* st))
         (l2.d (nth *link$d* l2)))
      (append (v-threefix (strip-cars l2.d))
              (v-threefix (strip-cars l1.d)))))

  (defthm len-gcd-body3$data-out-1
    (implies (gcd-body3$st-format st data-size cnt-size)
             (equal (len (gcd-body3$data-out st))
                    (* 2 data-size)))
    :hints (("Goal" :in-theory (enable gcd-body3$st-format
                                       gcd-body3$data-out))))

  (defthm len-gcd-body3$data-out-2
    (implies (gcd-body3$valid-st st data-size cnt-size)
             (equal (len (gcd-body3$data-out st))
                    (* 2 data-size)))
    :hints (("Goal" :in-theory (enable gcd-body3$valid-st
                                       gcd-body3$data-out))))

  (defthm bvp-gcd-body3$data-out
    (implies (and (gcd-body3$valid-st st data-size cnt-size)
                  (gcd-body3$out-act inputs st data-size))
             (bvp (gcd-body3$data-out st)))
    :hints (("Goal" :in-theory (enable gcd-body3$valid-st
                                       gcd-body3$out-act
                                       gcd-body3$data-out))))

  (defun gcd-body3$outputs (inputs st data-size)
    (list* (gcd-body3$in-act inputs st data-size)
           (gcd-body3$out-act inputs st data-size)
           (gcd-body3$data-out st)))
  )

;; The value lemma for GCD-BODY3

(defthm gcd-body3$value
  (b* ((inputs (list* full-in empty-out-
                      (append data-in go-signals))))
    (implies (and (gcd-body3& netlist data-size cnt-size)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-size))
                  (true-listp go-signals)
                  (equal (len go-signals) *gcd-body3$go-num*)
                  (gcd-body3$st-format st data-size cnt-size))
             (equal (se (si 'gcd-body3 data-size) inputs st netlist)
                    (gcd-body3$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'gcd-body3 data-size)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            gcd-body3&
                            gcd-body3*$destructure
                            gcd-body3$st-format
                            gcd-body3$in-act
                            gcd-body3$out-act
                            gcd-body3$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of GCD-BODY3.

(defun gcd-body3$step (inputs st data-size cnt-size)
  (b* ((data-in (gcd-body3$data-in inputs data-size))

       (l0 (nth *gcd-body3$l0* st))
       (l1 (nth *gcd-body3$l1* st))
       (l2 (nth *gcd-body3$l2* st))
       (sub (nth *gcd-body3$sub* st))

       (in-act (gcd-body3$in-act inputs st data-size))
       (out-act (gcd-body3$out-act inputs st data-size))
       (sub-inputs (gcd-body3$sub-inputs inputs st data-size))
       (sub-in-act (serial-sub$in-act sub-inputs sub data-size))
       (sub-out-act (serial-sub$out-act sub-inputs sub data-size))

       (a<b (gcd-body3$a<b inputs data-size))
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

;; The state lemma for GCD-BODY3

(defthm gcd-body3$state
  (b* ((inputs (list* full-in empty-out-
                      (append data-in go-signals))))
    (implies (and (gcd-body3& netlist data-size cnt-size)
                  (true-listp data-in)
                  (equal (len data-in) (* 2 data-size))
                  (true-listp go-signals)
                  (equal (len go-signals) *gcd-body3$go-num*)
                  (gcd-body3$st-format st data-size cnt-size))
             (equal (de (si 'gcd-body3 data-size) inputs st netlist)
                    (gcd-body3$step inputs st data-size cnt-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'gcd-body3 data-size)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            gcd-body3&
                            gcd-body3*$destructure
                            gcd-body3$st-format
                            gcd-body3$data-in
                            gcd-body3$a<b
                            gcd-body3$sub-inputs
                            gcd-body3$in-act
                            gcd-body3$out-act)
                           (associativity-of-append
                            append-take-nthcdr
                            de-module-disabled-rules)))))

(in-theory (disable gcd-body3$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund gcd-body3$input-format (inputs data-size)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-size))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (gcd-body3$data-in inputs data-size))
       (go-signals (nthcdr (gcd-body3$data-ins-len data-size) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in)
         (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *gcd-body3$go-num*)
     (equal inputs
            (list* full-in empty-out-
                   (append data-in go-signals))))))

(local
 (defthm gcd-body3$input-format=>sub$input-format
   (implies (and (gcd-body3$input-format inputs data-size)
                 (gcd-body3$valid-st st data-size cnt-size))
            (serial-sub$input-format
             (gcd-body3$sub-inputs inputs st data-size)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (serial-sub$input-format
                             serial-sub$data0-in
                             serial-sub$data1-in
                             gcd-body3$input-format
                             gcd-body3$valid-st
                             gcd-body3$sub-inputs)
                            ())))))

(defthm booleanp-gcd-body3$in-act
  (implies (and (gcd-body3$input-format inputs data-size)
                (gcd-body3$valid-st st data-size cnt-size))
           (booleanp (gcd-body3$in-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (e/d (gcd-body3$input-format
                            gcd-body3$valid-st
                            gcd-body3$in-act)
                           ())))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-gcd-body3$out-act
  (implies (and (gcd-body3$input-format inputs data-size)
                (gcd-body3$valid-st st data-size cnt-size))
           (booleanp (gcd-body3$out-act inputs st data-size)))
  :hints (("Goal"
           :in-theory (e/d (gcd-body3$input-format
                            gcd-body3$valid-st
                            gcd-body3$out-act)
                           ())))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma gcd-body3 :sizes (data-size cnt-size))

;; ======================================================================

;; 3. Single-Step-Update Property

;; Specify the functionality of GCD-BODY3

(defund gcd-body3$op (x)
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

;; The operation of GCD-BODY3 over a data sequence

(defun gcd-body3$op-map (x)
  (if (atom x)
      nil
    (cons (gcd-body3$op (car x))
          (gcd-body3$op-map (cdr x)))))

(defthm gcd-body3$op-map-of-append
  (equal (gcd-body3$op-map (append x y))
         (append (gcd-body3$op-map x)
                 (gcd-body3$op-map y))))

;; The extraction function for GCD-BODY3 that extracts the future output
;; sequence from the current state.

(defund gcd-body3$extract (st data-size)
  (b* ((l0 (nth *gcd-body3$l0* st))
       (l0.s (nth *link$s* l0))
       (l0.d (nth *link$d* l0))
       (l1 (nth *gcd-body3$l1* st))
       (l1.s (nth *link$s* l1))
       (l1.d (nth *link$d* l1))
       (l2 (nth *gcd-body3$l2* st))
       (l2.s (nth *link$s* l2))
       (l2.d (nth *link$d* l2))
       (sub (nth *gcd-body3$sub* st)))
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

(defthm gcd-body3$extract-not-empty
  (implies (and (gcd-body3$out-act inputs st data-size)
                (gcd-body3$valid-st st data-size cnt-size))
           (< 0 (len (gcd-body3$extract st data-size))))
  :hints (("Goal"
           :in-theory (e/d (gcd-body3$valid-st
                            gcd-body3$extract
                            gcd-body3$out-act)
                           ())))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund gcd-body3$inv (st data-size)
    (b* ((l0 (nth *gcd-body3$l0* st))
         (l1 (nth *gcd-body3$l1* st))
         (l2 (nth *gcd-body3$l2* st))
         (sub (nth *gcd-body3$sub* st))

         (len1 (len (append
                     (extract-valid-data (list l0 l2))
                     (serial-sub$extract sub data-size))))
         (len2 (len (extract-valid-data (list l1)))))
      (and (equal len1 len2)
           (serial-sub$inv sub data-size))))

  (local
   (defthm gcd-body3$sub-in-act-inactive
     (b* ((l0 (nth *gcd-body3$l0* st))
          (l0.s (nth *link$s* l0))
          (sub (nth *gcd-body3$sub* st))
          (sub-inputs (gcd-body3$sub-inputs inputs st data-size)))
       (implies (emptyp l0.s)
                (not (serial-sub$in-act sub-inputs
                                        sub
                                        data-size))))
     :hints (("Goal" :in-theory (enable gcd-body3$sub-inputs)))))

  (defthm gcd-body3$inv-preserved
    (implies (and (gcd-body3$input-format inputs data-size)
                  (gcd-body3$valid-st st data-size cnt-size)
                  (gcd-body3$inv st data-size))
             (gcd-body3$inv
              (gcd-body3$step inputs st data-size cnt-size)
              data-size))
    :hints (("Goal"
             :use gcd-body3$input-format=>sub$input-format
             :in-theory (e/d (f-sr
                              serial-sub$extracted-step
                              gcd-body3$valid-st
                              gcd-body3$inv
                              gcd-body3$step
                              gcd-body3$in-act
                              gcd-body3$out-act)
                             (gcd-body3$input-format=>sub$input-format)))))
  )

;; The extracted next-state function for GCD-BODY3.  Note that this
;; function avoids exploring the internal computation of GCD-BODY3.

(defund gcd-body3$extracted-step (inputs st data-size)
  (b* ((data (gcd-body3$op (gcd-body3$data-in inputs data-size)))
       (extracted-st (gcd-body3$extract st data-size))
       (n (1- (len extracted-st))))
    (cond
     ((equal (gcd-body3$out-act inputs st data-size) t)
      (take n extracted-st))
     ((equal (gcd-body3$in-act inputs st data-size) t)
      (cons data extracted-st))
     (t extracted-st))))

(local
 (defthm gcd-body3$input-format-lemma-1
   (implies (gcd-body3$input-format inputs data-size)
            (booleanp (nth 0 inputs)))
   :hints (("Goal" :in-theory (enable gcd-body3$input-format)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm gcd-body3$input-format-lemma-2
   (implies (gcd-body3$input-format inputs data-size)
            (booleanp (nth 1 inputs)))
   :hints (("Goal" :in-theory (enable gcd-body3$input-format)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm gcd-body3$input-format-lemma-3
   (implies (and (gcd-body3$input-format inputs data-size)
                 (nth 0 inputs))
            (bvp (gcd-body3$data-in inputs data-size)))
   :hints (("Goal" :in-theory (enable gcd-body3$input-format)))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm gcd-body3$extracted-step-correct-aux-1
     (b* ((sub-inputs (gcd-body3$sub-inputs inputs st data-size))
          (l0 (nth *gcd-body3$l0* st))
          (l0.d (nth *link$d* l0)))
       (equal (serial-sub$data0-in sub-inputs data-size)
              (v-threefix (take data-size (strip-cars l0.d)))))
     :hints (("Goal" :in-theory (enable serial-sub$data0-in
                                        gcd-body3$sub-inputs)))))

  (local
   (defthm gcd-body3$extracted-step-correct-aux-2
     (b* ((sub-inputs (gcd-body3$sub-inputs inputs st data-size))
          (l0 (nth *gcd-body3$l0* st))
          (l0.d (nth *link$d* l0)))
       (implies (and (equal (len l0.d) (* 2 data-size))
                     (integerp data-size))
                (equal (serial-sub$data1-in sub-inputs data-size)
                       (v-threefix (nthcdr data-size (strip-cars l0.d))))))
     :hints (("Goal" :in-theory (enable serial-sub$data1-in
                                        gcd-body3$sub-inputs)))))

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
              :in-theory (e/d (serial-sub$valid-st
                               serial-sub$inv
                               serial-sub$extract
                               serial-sub$out-act
                               serial-sub$data-out)
                              (acl2::normalize-terms-such-as-a/a+b-+-b/a+b
                               acl2::prefer-positive-addends-<
                               acl2::simplify-products-gather-exponents-<
                               acl2::len-when-prefixp
                               acl2::take-when-prefixp
                               take
                               not
                               default-car
                               default-cdr
                               true-listp
                               bv-is-true-list))))))

  (defthm gcd-body3$extracted-step-correct
    (b* ((next-st (gcd-body3$step inputs st data-size cnt-size)))
      (implies (and (gcd-body3$input-format inputs data-size)
                    (gcd-body3$valid-st st data-size cnt-size)
                    (gcd-body3$inv st data-size))
               (equal (gcd-body3$extract next-st data-size)
                      (gcd-body3$extracted-step inputs st data-size))))
    :hints (("Goal"
             :use gcd-body3$input-format=>sub$input-format
             :in-theory (e/d (joint-act
                              pos-len=>cons
                              fv-if-rewrite
                              serial-sub$valid-st=>constraint
                              serial-sub$extracted-step
                              gcd-body3$extracted-step
                              gcd-body3$valid-st
                              gcd-body3$inv
                              gcd-body3$step
                              gcd-body3$a<b
                              gcd-body3$in-act
                              gcd-body3$out-act
                              gcd-body3$extract
                              gcd-body3$op)
                             (gcd-body3$input-format=>sub$input-format)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that gcd-body3$valid-st is an invariant.

(encapsulate
  ()

  (local
   (defthm gcd-body3$sub-out-act-inactive
     (b* ((l2 (nth *gcd-body3$l2* st))
          (l2.s (nth *link$s* l2))
          (sub (nth *gcd-body3$sub* st))
          (sub-inputs (gcd-body3$sub-inputs inputs st data-size)))
       (implies (fullp l2.s)
                (not (serial-sub$out-act sub-inputs
                                         sub
                                         data-size))))
     :hints (("Goal" :in-theory (enable gcd-body3$sub-inputs)))))

  (defthm gcd-body3$valid-st-preserved
    (implies (and (gcd-body3$input-format inputs data-size)
                  (gcd-body3$valid-st st data-size cnt-size))
             (gcd-body3$valid-st
              (gcd-body3$step inputs st data-size cnt-size)
              data-size
              cnt-size))
    :hints (("Goal"
             :use gcd-body3$input-format=>sub$input-format
             :in-theory (e/d (f-sr
                              joint-act
                              serial-sub$valid-st=>constraint
                              gcd-body3$valid-st
                              gcd-body3$step
                              gcd-body3$a<b
                              gcd-body3$in-act
                              gcd-body3$out-act)
                             (gcd-body3$input-format=>sub$input-format
                              if*)))))
  )

(defthm gcd-body3$extract-lemma
  (implies (and (gcd-body3$valid-st st data-size cnt-size)
                (gcd-body3$inv st data-size)
                (gcd-body3$out-act inputs st data-size))
           (equal (list (gcd-body3$data-out st))
                  (nthcdr (1- (len (gcd-body3$extract st data-size)))
                          (gcd-body3$extract st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (len-0-is-atom
                            gcd-body3$valid-st
                            gcd-body3$inv
                            gcd-body3$extract
                            gcd-body3$out-act
                            gcd-body3$data-out)
                           ()))))

;; Extract the accepted input sequence

(seq-gen gcd-body3 in in-act 0
         (gcd-body3$data-in inputs data-size)
         :sizes (data-size cnt-size))

;; Extract the valid output sequence

(seq-gen gcd-body3 out out-act 1
         (gcd-body3$data-out st)
         :netlist-data (nthcdr 2 outputs)
         :sizes (data-size cnt-size))

;; The multi-step input-output relationship

(encapsulate
  ()

  (local
   (defthm gcd-body3$dataflow-correct-aux
     (implies (equal (append x y1)
                     (append (gcd-body3$op-map seq) y2))
              (equal (append x y1 z)
                     (append (gcd-body3$op-map seq)
                             y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (associativity-of-append))))))

  (defthmd gcd-body3$dataflow-correct
    (b* ((extracted-st (gcd-body3$extract st data-size))
         (final-st (gcd-body3$run
                    inputs-seq st data-size cnt-size n))
         (final-extracted-st (gcd-body3$extract final-st data-size)))
      (implies
       (and (gcd-body3$input-format-n inputs-seq data-size n)
            (gcd-body3$valid-st st data-size cnt-size)
            (gcd-body3$inv st data-size))
       (equal (append final-extracted-st
                      (gcd-body3$out-seq
                       inputs-seq st data-size cnt-size n))
              (append (gcd-body3$op-map
                       (gcd-body3$in-seq
                        inputs-seq st data-size cnt-size n))
                      extracted-st))))
    :hints (("Goal"
             :in-theory (enable gcd-body3$extracted-step))))

  (defthmd gcd-body3$functionally-correct
    (b* ((extracted-st (gcd-body3$extract st data-size))
         (final-st (de-n (si 'gcd-body3 data-size)
                         inputs-seq st netlist n))
         (final-extracted-st (gcd-body3$extract final-st data-size)))
      (implies
       (and (gcd-body3& netlist data-size cnt-size)
            (gcd-body3$input-format-n inputs-seq data-size n)
            (gcd-body3$valid-st st data-size cnt-size)
            (gcd-body3$inv st data-size))
       (equal (append final-extracted-st
                      (gcd-body3$out-seq-netlist
                       inputs-seq st netlist data-size n))
              (append (gcd-body3$op-map
                       (gcd-body3$in-seq-netlist
                        inputs-seq st netlist data-size n))
                      extracted-st))))
    :hints (("Goal"
             :use gcd-body3$dataflow-correct
             :in-theory (enable gcd-body3$valid-st=>st-format
                                gcd-body3$de-n))))
  )
