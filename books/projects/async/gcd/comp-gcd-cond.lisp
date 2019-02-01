;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; December 2018

(in-package "ADE")

(include-book "gcd-cond")
(include-book "../fifo/queue2")
(include-book "../fifo/queue3")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of COMP-GCD-COND
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of COMP-GCD-COND
;;
;; Construct a DE module generator for COMP-GCD-COND using the link-joint
;; model.  Prove the value and state lemmas for this module generator.

(defconst *comp-gcd-cond$prim-go-num* 1)
(defconst *comp-gcd-cond$go-num* (+ *comp-gcd-cond$prim-go-num*
                                    *queue2$go-num*
                                    *queue3$go-num*
                                    *gcd-cond$go-num*))
(defconst *comp-gcd-cond$st-len* 6)

(defun comp-gcd-cond$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 3 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun comp-gcd-cond$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (comp-gcd-cond$data-ins-len data-width)
     *comp-gcd-cond$go-num*))

;; DE module generator of COMP-GCD-COND

(module-generator
 comp-gcd-cond* (data-width)
 (si 'comp-gcd-cond data-width)
 (list* 'full-in 'empty-out0- 'empty-out1-
        (append (sis 'data-in 0 (* 2 data-width))
                (sis 'go 0 *comp-gcd-cond$go-num*)))
 (list* 'in-act 'out-act 'out-act0 'out-act1 'flag
        (append (sis 'data0-out 0 data-width)
                (sis 'data1-out 0 (* 2 data-width))))
 '(a0 b0 a1 b1 q2 q3)
 (list
  ;; LINKS
  ;; A0
  (list 'a0
        (list* 'a0-status (sis 'a0-out 0 data-width))
        (si 'link data-width)
        (list* 'in-act 'q2-in-act (sis 'a0-in 0 data-width)))

  ;; B0
  (list 'b0
        (list* 'b0-status (sis 'b0-out 0 data-width))
        (si 'link data-width)
        (list* 'in-act 'q3-in-act (sis 'b0-in 0 data-width)))

  ;; A1
  (list 'a1
        (list* 'a1-status (sis 'a1-out 0 data-width))
        (si 'link data-width)
        (list* 'q2-out-act 'out-act (sis 'q2-data-out 0 data-width)))

  ;; B1
  (list 'b1
        (list* 'b1-status (sis 'b1-out 0 data-width))
        (si 'link data-width)
        (list* 'q3-out-act 'out-act (sis 'q3-data-out 0 data-width)))

  ;; STATUS
  '(in-status (ready-in-) b-or (a0-status b0-status))
  '(out-status (ready-out) b-and (a1-status b1-status))

  ;; JOINTS
  ;; 2-link queue Q2
  (list 'q2
        (list* 'q2-in-act 'q2-out-act
               (sis 'q2-data-out 0 data-width))
        (si 'queue2 data-width)
        (list* 'a0-status 'a1-status
               (append (sis 'a0-out 0 data-width)
                       (sis 'go
                            (+ *comp-gcd-cond$prim-go-num*
                               *gcd-cond$go-num*)
                            *queue2$go-num*))))

  ;; 3-link queue Q3
  (list 'q3
        (list* 'q3-in-act 'q3-out-act
               (sis 'q3-data-out 0 data-width))
        (si 'queue3 data-width)
        (list* 'b0-status 'b1-status
               (append (sis 'b0-out 0 data-width)
                       (sis 'go
                            (+ *comp-gcd-cond$prim-go-num*
                               *gcd-cond$go-num*
                               *queue2$go-num*)
                            *queue3$go-num*))))

  ;; In
  (list 'in-cntl
        '(in-act)
        'joint-cntl
        (list 'full-in 'ready-in- (si 'go 0)))
  (list 'in-op0
        (sis 'a0-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'data-in 0 data-width))
  (list 'in-op1
        (sis 'b0-in 0 data-width)
        (si 'v-buf data-width)
        (sis 'data-in data-width data-width))

  ;; Out
  (list 'branch-out
        (list* 'out-act 'out-act0 'out-act1 'flag
               (append (sis 'data0-out 0 data-width)
                       (sis 'data1-out 0 (* 2 data-width))))
        (si 'gcd-cond data-width)
        (list* 'ready-out 'empty-out0- 'empty-out1-
               (append (append (sis 'a1-out 0 data-width)
                               (sis 'b1-out 0 data-width))
                       (sis 'go
                            *comp-gcd-cond$prim-go-num*
                            *gcd-cond$go-num*)))))

 (declare (xargs :guard (natp data-width))))

(make-event
 `(progn
    ,@(state-accessors-gen 'comp-gcd-cond '(a0 b0 a1 b1 q2 q3) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; COMP-GCD-COND.

(defund comp-gcd-cond$netlist (data-width)
  (declare (xargs :guard (and (natp data-width)
                              (<= 2 data-width))))
  (cons (comp-gcd-cond* data-width)
        (union$ (queue2$netlist data-width)
                (queue3$netlist data-width)
                (gcd-cond$netlist data-width)
                :test 'equal)))

;; Recognizer for COMP-GCD-COND

(defund comp-gcd-cond& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (and (natp data-width)
                                   (<= 2 data-width)))))
  (b* ((subnetlist (delete-to-eq (si 'comp-gcd-cond data-width) netlist)))
    (and (equal (assoc (si 'comp-gcd-cond data-width) netlist)
                (comp-gcd-cond* data-width))
         (link& subnetlist data-width)
         (joint-cntl& subnetlist)
         (v-buf& subnetlist data-width)
         (gcd-cond& subnetlist data-width)
         (queue2& subnetlist data-width)
         (queue3& subnetlist data-width))))

;; Sanity check

(local
 (defthmd check-comp-gcd-cond$netlist-64
   (and (net-syntax-okp (comp-gcd-cond$netlist 64))
        (net-arity-okp (comp-gcd-cond$netlist 64))
        (comp-gcd-cond& (comp-gcd-cond$netlist 64) 64))))

;; Constraints on the state of COMP-GCD-COND

(defund comp-gcd-cond$st-format (st data-width)
  (b* ((a0 (get-field *comp-gcd-cond$a0* st))
       (b0 (get-field *comp-gcd-cond$b0* st))
       (a1 (get-field *comp-gcd-cond$a1* st))
       (b1 (get-field *comp-gcd-cond$b1* st))
       (q2 (get-field *comp-gcd-cond$q2* st))
       (q3 (get-field *comp-gcd-cond$q3* st)))
    (and (natp data-width)
         (<= 3 data-width)

         (link$st-format a0 data-width)
         (link$st-format b0 data-width)
         (link$st-format a1 data-width)
         (link$st-format b1 data-width)

         (queue2$st-format q2 data-width)
         (queue3$st-format q3 data-width))))

(defthm comp-gcd-cond$st-format=>constraint
  (implies (comp-gcd-cond$st-format st data-width)
           (and (natp data-width)
                (<= 3 data-width)))
  :hints (("Goal" :in-theory (enable comp-gcd-cond$st-format)))
  :rule-classes :forward-chaining)

(defund comp-gcd-cond$valid-st (st data-width)
  (b* ((a0 (get-field *comp-gcd-cond$a0* st))
       (b0 (get-field *comp-gcd-cond$b0* st))
       (a1 (get-field *comp-gcd-cond$a1* st))
       (b1 (get-field *comp-gcd-cond$b1* st))
       (q2 (get-field *comp-gcd-cond$q2* st))
       (q3 (get-field *comp-gcd-cond$q3* st)))
    (and (comp-gcd-cond$st-format st data-width)

         (link$valid-st a0 data-width)
         (link$valid-st b0 data-width)
         (link$valid-st a1 data-width)
         (link$valid-st b1 data-width)

         (queue2$valid-st q2 data-width)
         (queue3$valid-st q3 data-width))))

(defthmd comp-gcd-cond$valid-st=>constraint
  (implies (comp-gcd-cond$valid-st st data-width)
           (and (natp data-width)
                (<= 3 data-width)))
  :hints (("Goal"
           :in-theory (enable comp-gcd-cond$valid-st)))
  :rule-classes :forward-chaining)

(defthmd comp-gcd-cond$valid-st=>st-format
  (implies (comp-gcd-cond$valid-st st data-width)
           (comp-gcd-cond$st-format st data-width))
  :hints (("Goal" :in-theory (e/d (comp-gcd-cond$valid-st)
                                  ()))))

;; Extract the input and output signals for COMP-GCD-COND

(progn
  ;; Extract the input data

  (defun comp-gcd-cond$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (* 2 (mbe :logic (nfix data-width)
                    :exec  data-width))
          (nthcdr 3 inputs)))

  (defthm len-comp-gcd-cond$data-in
    (equal (len (comp-gcd-cond$data-in inputs data-width))
           (* 2 (nfix data-width))))

  (in-theory (disable comp-gcd-cond$data-in))

  ;; Extract the inputs for the Q2 joint

  (defund comp-gcd-cond$q2-inputs (inputs st data-width)
    (b* ((go-signals (nthcdr (comp-gcd-cond$data-ins-len data-width) inputs))

         (q2-go-signals (take *queue2$go-num*
                              (nthcdr (+ *comp-gcd-cond$prim-go-num*
                                         *gcd-cond$go-num*)
                                      go-signals)))

         (a0 (get-field *comp-gcd-cond$a0* st))
         (a0.s (get-field *link$s* a0))
         (a0.d (get-field *link$d* a0))
         (a1 (get-field *comp-gcd-cond$a1* st))
         (a1.s (get-field *link$s* a1)))

      (list* (f-buf (car a0.s)) (f-buf (car a1.s))
             (append (v-threefix (strip-cars a0.d))
                     q2-go-signals))))

  ;; Extract the inputs for the Q3 joint

  (defund comp-gcd-cond$q3-inputs (inputs st data-width)
    (b* ((go-signals (nthcdr (comp-gcd-cond$data-ins-len data-width) inputs))

         (q3-go-signals (take *queue3$go-num*
                              (nthcdr (+ *comp-gcd-cond$prim-go-num*
                                         *gcd-cond$go-num*
                                         *queue2$go-num*)
                                      go-signals)))

         (b0 (get-field *comp-gcd-cond$b0* st))
         (b0.s (get-field *link$s* b0))
         (b0.d (get-field *link$d* b0))
         (b1 (get-field *comp-gcd-cond$b1* st))
         (b1.s (get-field *link$s* b1)))

      (list* (f-buf (car b0.s)) (f-buf (car b1.s))
             (append (v-threefix (strip-cars b0.d))
                     q3-go-signals))))

  ;; Extract the inputs for the branch-out joint

  (defund comp-gcd-cond$br-inputs (inputs st data-width)
    (b* ((empty-out0- (nth 1 inputs))
         (empty-out1- (nth 2 inputs))
         (go-signals (nthcdr (comp-gcd-cond$data-ins-len data-width)
                             inputs))

         (br-go-signals (take *gcd-cond$go-num*
                              (nthcdr *comp-gcd-cond$prim-go-num*
                                      go-signals)))

         (a1 (get-field *comp-gcd-cond$a1* st))
         (a1.s (get-field *link$s* a1))
         (a1.d (get-field *link$d* a1))
         (b1 (get-field *comp-gcd-cond$b1* st))
         (b1.s (get-field *link$s* b1))
         (b1.d (get-field *link$d* b1))

         (br-full-in (f-and (car a1.s) (car b1.s))))

      (list* br-full-in empty-out0- empty-out1-
             (append (append (v-threefix (strip-cars a1.d))
                             (v-threefix (strip-cars b1.d)))
                     br-go-signals))))

  ;; Extract the "in-act" signal

  (defund comp-gcd-cond$in-act (inputs st data-width)
    (b* ((full-in (nth 0 inputs))
         (go-signals (nthcdr (comp-gcd-cond$data-ins-len data-width) inputs))
         (go-in (nth 0 go-signals))
         (a0 (get-field *comp-gcd-cond$a0* st))
         (a0.s (get-field *link$s* a0))
         (b0 (get-field *comp-gcd-cond$b0* st))
         (b0.s (get-field *link$s* b0)))
      (joint-act full-in
                 (f-or (car a0.s) (car b0.s))
                 go-in)))

  (defthm comp-gcd-cond$in-act-inactive-lemma
    (implies (not (nth 0 inputs))
             (not (comp-gcd-cond$in-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable comp-gcd-cond$in-act))))

  ;; Extract the "out-act0" signal

  (defund comp-gcd-cond$out-act0 (inputs st data-width)
    (gcd-cond$act0 (comp-gcd-cond$br-inputs inputs st data-width)
                   data-width))

  (defthm comp-gcd-cond$out-act0-inactive-lemma
    (implies (equal (nth 1 inputs) t)
             (not (comp-gcd-cond$out-act0 inputs st data-width)))
    :hints (("Goal" :in-theory (enable comp-gcd-cond$br-inputs
                                       comp-gcd-cond$out-act0))))

  ;; Extract the "out-act1" signal

  (defund comp-gcd-cond$out-act1 (inputs st data-width)
    (gcd-cond$act1 (comp-gcd-cond$br-inputs inputs st data-width)
                   data-width))

  (defthm comp-gcd-cond$out-act1-inactive-lemma
    (implies (equal (nth 2 inputs) t)
             (not (comp-gcd-cond$out-act1 inputs st data-width)))
    :hints (("Goal" :in-theory (enable comp-gcd-cond$br-inputs
                                       comp-gcd-cond$out-act1))))

  (defthm comp-gcd-cond$out-act-mutually-exclusive
    (implies (and (comp-gcd-cond$valid-st st data-width)
                  (comp-gcd-cond$out-act0 inputs st data-width))
             (not (comp-gcd-cond$out-act1 inputs st data-width)))
    :hints (("Goal" :in-theory (e/d (branch$act0
                                     branch$act1
                                     gcd-cond$data-in
                                     gcd-cond$br-inputs
                                     gcd-cond$flag
                                     gcd-cond$act0
                                     gcd-cond$act1
                                     comp-gcd-cond$valid-st
                                     comp-gcd-cond$br-inputs
                                     comp-gcd-cond$out-act0
                                     comp-gcd-cond$out-act1)
                                    (b-nor3)))))

  ;; Extract the "out-act" signal

  (defund comp-gcd-cond$out-act (inputs st data-width)
    (f-or (comp-gcd-cond$out-act0 inputs st data-width)
          (comp-gcd-cond$out-act1 inputs st data-width)))

  (defthm comp-gcd-cond$out-act-inactive-lemma
    (implies (and (equal (nth 1 inputs) t)
                  (equal (nth 2 inputs) t))
             (not (comp-gcd-cond$out-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable comp-gcd-cond$out-act))))

  ;; Extract the "flag" signal

  (defund comp-gcd-cond$flag (inputs st data-width)
    (gcd-cond$flag (comp-gcd-cond$br-inputs inputs st data-width)
                   data-width))

  ;; Extract the 1st output data item

  (defund comp-gcd-cond$data0-out (inputs st data-width)
    (gcd-cond$data0-out (comp-gcd-cond$br-inputs inputs st data-width)
                        data-width))

  (defthm len-comp-gcd-cond$data0-out-1
    (implies (comp-gcd-cond$st-format st data-width)
             (equal (len (comp-gcd-cond$data0-out inputs st data-width))
                    data-width))
    :hints (("Goal" :in-theory (enable comp-gcd-cond$st-format
                                       comp-gcd-cond$data0-out))))

  (defthm len-comp-gcd-cond$data0-out-2
    (implies (comp-gcd-cond$valid-st st data-width)
             (equal (len (comp-gcd-cond$data0-out inputs st data-width))
                    data-width))
    :hints (("Goal" :in-theory (enable comp-gcd-cond$valid-st))))

  (defthm bvp-comp-gcd-cond$data0-out
    (implies (and (comp-gcd-cond$valid-st st data-width)
                  (comp-gcd-cond$out-act0 inputs st data-width))
             (bvp (comp-gcd-cond$data0-out inputs st data-width)))
    :hints (("Goal" :in-theory (enable gcd-cond$act0
                                       gcd-cond$br-inputs
                                       gcd-cond$data-in
                                       branch$act0
                                       comp-gcd-cond$br-inputs
                                       comp-gcd-cond$valid-st
                                       comp-gcd-cond$st-format
                                       comp-gcd-cond$out-act0
                                       comp-gcd-cond$data0-out))))

  ;; Extract the 2nd output data item

  (defund comp-gcd-cond$data1-out (inputs st data-width)
    (gcd-cond$data1-out (comp-gcd-cond$br-inputs inputs st data-width)
                        data-width))

  (defthm len-comp-gcd-cond$data1-out-1
    (implies (comp-gcd-cond$st-format st data-width)
             (equal (len (comp-gcd-cond$data1-out inputs st data-width))
                    (* 2 data-width)))
    :hints (("Goal" :in-theory (enable comp-gcd-cond$st-format
                                       comp-gcd-cond$data1-out))))

  (defthm len-comp-gcd-cond$data1-out-2
    (implies (comp-gcd-cond$valid-st st data-width)
             (equal (len (comp-gcd-cond$data1-out inputs st data-width))
                    (* 2 data-width)))
    :hints (("Goal" :in-theory (enable comp-gcd-cond$valid-st))))

  (defthm bvp-comp-gcd-cond$data1-out
    (implies (and (comp-gcd-cond$valid-st st data-width)
                  (comp-gcd-cond$out-act1 inputs st data-width))
             (bvp (comp-gcd-cond$data1-out inputs st data-width)))
    :hints (("Goal" :in-theory (enable gcd-cond$act1
                                       gcd-cond$br-inputs
                                       gcd-cond$data-in
                                       branch$act1
                                       comp-gcd-cond$br-inputs
                                       comp-gcd-cond$valid-st
                                       comp-gcd-cond$st-format
                                       comp-gcd-cond$out-act1
                                       comp-gcd-cond$data1-out))))

  ;; Extract the output data

  (defund comp-gcd-cond$data-outs (inputs st data-width)
    (cons (comp-gcd-cond$flag inputs st data-width)
          (append (comp-gcd-cond$data0-out inputs st data-width)
                  (comp-gcd-cond$data1-out inputs st data-width))))

  (defun comp-gcd-cond$outputs (inputs st data-width)
    (list* (comp-gcd-cond$in-act inputs st data-width)
           (comp-gcd-cond$out-act inputs st data-width)
           (comp-gcd-cond$out-act0 inputs st data-width)
           (comp-gcd-cond$out-act1 inputs st data-width)
           (comp-gcd-cond$flag inputs st data-width)
           (append (comp-gcd-cond$data0-out inputs st data-width)
                   (comp-gcd-cond$data1-out inputs st data-width))))
  )

(encapsulate
  ()

  (local
   (defthm gcd-cond$value-alt
     (b* ((inputs (list* full-in empty-out0- empty-out1-
                         (append a b go-signals))))
       (implies
        (and (natp data-width)
             (<= 3 data-width)
             (gcd-cond& netlist data-width)
             (true-listp a)
             (equal (len a) data-width)
             (true-listp b)
             (equal (len b) data-width)
             (true-listp go-signals)
             (equal (len go-signals)
                    *gcd-cond$go-num*))
        (equal (se (si 'gcd-cond data-width) inputs st netlist)
               (list* (gcd-cond$act inputs data-width)
                      (gcd-cond$act0 inputs data-width)
                      (gcd-cond$act1 inputs data-width)
                      (gcd-cond$flag inputs data-width)
                      (append (gcd-cond$data0-out inputs data-width)
                              (gcd-cond$data1-out inputs data-width))))))
     :hints (("Goal"
              :use (:instance gcd-cond$value
                              (data-in (append a b)))))))

  ;; The value lemma for COMP-GCD-COND

  (defthm comp-gcd-cond$value
    (b* ((inputs (list* full-in empty-out0- empty-out1-
                        (append data-in go-signals))))
      (implies
       (and (comp-gcd-cond& netlist data-width)
            (equal (len data-in) (* 2 data-width))
            (true-listp go-signals)
            (equal (len go-signals) *comp-gcd-cond$go-num*)
            (comp-gcd-cond$st-format st data-width))
       (equal (se (si 'comp-gcd-cond data-width) inputs st netlist)
              (comp-gcd-cond$outputs inputs st data-width))))
    :hints (("Goal"
             :do-not-induct t
             :expand (:free (inputs data-width)
                            (se (si 'comp-gcd-cond data-width)
                                inputs st netlist))
             :in-theory (e/d (de-rules
                              comp-gcd-cond&
                              comp-gcd-cond*$destructure
                              gcd-cond$act
                              comp-gcd-cond$st-format
                              comp-gcd-cond$br-inputs
                              comp-gcd-cond$in-act
                              comp-gcd-cond$out-act
                              comp-gcd-cond$out-act0
                              comp-gcd-cond$out-act1
                              comp-gcd-cond$flag
                              comp-gcd-cond$data0-out
                              comp-gcd-cond$data1-out)
                             (nfix
                              append
                              append-v-threefix
                              de-module-disabled-rules)))))

  ;; This function specifies the next state of COMP-GCD-COND.

  (defun comp-gcd-cond$step (inputs st data-width)
    (b* ((data-in (comp-gcd-cond$data-in inputs data-width))
         (a (take data-width data-in))
         (b (nthcdr data-width data-in))

         (a0 (get-field *comp-gcd-cond$a0* st))
         (b0 (get-field *comp-gcd-cond$b0* st))
         (a1 (get-field *comp-gcd-cond$a1* st))
         (b1 (get-field *comp-gcd-cond$b1* st))
         (q2 (get-field *comp-gcd-cond$q2* st))
         (q3 (get-field *comp-gcd-cond$q3* st))

         (q2-inputs (comp-gcd-cond$q2-inputs inputs st data-width))
         (q2-in-act (queue2$in-act q2-inputs q2 data-width))
         (q2-out-act (queue2$out-act q2-inputs q2 data-width))
         (q2-data-out (queue2$data-out q2))

         (q3-inputs (comp-gcd-cond$q3-inputs inputs st data-width))
         (q3-in-act (queue3$in-act q3-inputs q3 data-width))
         (q3-out-act (queue3$out-act q3-inputs q3 data-width))
         (q3-data-out (queue3$data-out q3))

         (in-act (comp-gcd-cond$in-act inputs st data-width))
         (out-act (comp-gcd-cond$out-act inputs st data-width))

         (a0-inputs (list* in-act q2-in-act a))
         (b0-inputs (list* in-act q3-in-act b))
         (a1-inputs (list* q2-out-act out-act q2-data-out))
         (b1-inputs (list* q3-out-act out-act q3-data-out)))

      (list
       ;; A0
       (link$step a0-inputs a0 data-width)
       ;; B0
       (link$step b0-inputs b0 data-width)
       ;; A1
       (link$step a1-inputs a1 data-width)
       ;; B1
       (link$step b1-inputs b1 data-width)

       ;; Joint Q2
       (queue2$step q2-inputs q2 data-width)
       ;; Joint Q3
       (queue3$step q3-inputs q3 data-width))))

  (defthm len-of-comp-gcd-cond$step
    (equal (len (comp-gcd-cond$step inputs st data-width))
           *comp-gcd-cond$st-len*))

  ;; The state lemma for COMP-GCD-COND

  (defthm comp-gcd-cond$state
    (b* ((inputs (list* full-in empty-out0- empty-out1-
                        (append data-in go-signals))))
      (implies (and (comp-gcd-cond& netlist data-width)
                    (true-listp data-in)
                    (equal (len data-in) (* 2 data-width))
                    (true-listp go-signals)
                    (equal (len go-signals) *comp-gcd-cond$go-num*)
                    (comp-gcd-cond$st-format st data-width))
               (equal (de (si 'comp-gcd-cond data-width) inputs st netlist)
                      (comp-gcd-cond$step inputs st data-width))))
    :hints (("Goal"
             :do-not-induct t
             :expand (:free (inputs data-width)
                            (de (si 'comp-gcd-cond data-width)
                                inputs st netlist))
             :in-theory (e/d (de-rules
                              comp-gcd-cond&
                              comp-gcd-cond*$destructure
                              comp-gcd-cond$st-format
                              comp-gcd-cond$br-inputs
                              comp-gcd-cond$data-in
                              comp-gcd-cond$in-act
                              comp-gcd-cond$out-act
                              comp-gcd-cond$out-act0
                              comp-gcd-cond$out-act1
                              comp-gcd-cond$q2-inputs
                              comp-gcd-cond$q3-inputs
                              gcd-cond$act)
                             (nfix
                              append
                              append-v-threefix
                              de-module-disabled-rules)))))

  (in-theory (disable comp-gcd-cond$step))
  )

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund comp-gcd-cond$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in     (nth 0 inputs))
       (empty-out0- (nth 1 inputs))
       (empty-out1- (nth 2 inputs))
       (data-in (comp-gcd-cond$data-in inputs data-width))
       (go-signals (nthcdr (comp-gcd-cond$data-ins-len data-width)
                           inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out0-)
     (booleanp empty-out1-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *comp-gcd-cond$go-num*)
     (equal inputs
            (list* full-in empty-out0- empty-out1-
                   (append data-in go-signals))))))

(local
 (defthm comp-gcd-cond$input-format=>q2$input-format
   (implies (and (comp-gcd-cond$input-format inputs data-width)
                 (comp-gcd-cond$valid-st st data-width))
            (queue2$input-format
             (comp-gcd-cond$q2-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (queue2$input-format
                             queue2$data-in
                             comp-gcd-cond$input-format
                             comp-gcd-cond$valid-st
                             comp-gcd-cond$q2-inputs)
                            ())))))

(local
 (defthm comp-gcd-cond$input-format=>q3$input-format
   (implies (and (comp-gcd-cond$input-format inputs data-width)
                 (comp-gcd-cond$valid-st st data-width))
            (queue3$input-format
             (comp-gcd-cond$q3-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (queue3$input-format
                             queue3$data-in
                             comp-gcd-cond$input-format
                             comp-gcd-cond$valid-st
                             comp-gcd-cond$q3-inputs)
                            ())))))

(defthm booleanp-comp-gcd-cond$in-act
  (implies (and (comp-gcd-cond$input-format inputs data-width)
                (comp-gcd-cond$valid-st st data-width))
           (booleanp (comp-gcd-cond$in-act inputs st data-width)))
  :hints (("Goal" :in-theory (enable comp-gcd-cond$input-format
                                     comp-gcd-cond$valid-st
                                     comp-gcd-cond$in-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-gcd-cond$out-act0
  (implies (and (comp-gcd-cond$input-format inputs data-width)
                (comp-gcd-cond$valid-st st data-width))
           (booleanp (comp-gcd-cond$out-act0 inputs st data-width)))
  :hints (("Goal" :in-theory (enable branch$act0
                                     gcd-cond$br-inputs
                                     gcd-cond$data-in
                                     gcd-cond$flag
                                     gcd-cond$act0
                                     comp-gcd-cond$input-format
                                     comp-gcd-cond$valid-st
                                     comp-gcd-cond$out-act0
                                     comp-gcd-cond$br-inputs)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-gcd-cond$out-act1
  (implies (and (comp-gcd-cond$input-format inputs data-width)
                (comp-gcd-cond$valid-st st data-width))
           (booleanp (comp-gcd-cond$out-act1 inputs st data-width)))
  :hints (("Goal" :in-theory (enable branch$act1
                                     gcd-cond$br-inputs
                                     gcd-cond$data-in
                                     gcd-cond$flag
                                     gcd-cond$act1
                                     comp-gcd-cond$input-format
                                     comp-gcd-cond$valid-st
                                     comp-gcd-cond$out-act1
                                     comp-gcd-cond$br-inputs)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-comp-gcd-cond$out-act
  (implies (and (comp-gcd-cond$input-format inputs data-width)
                (comp-gcd-cond$valid-st st data-width))
           (booleanp (comp-gcd-cond$out-act inputs st data-width)))
  :hints (("Goal" :in-theory (enable comp-gcd-cond$out-act)))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma comp-gcd-cond)

;; ======================================================================

;; 3. Single-Step-Update Property

;; Specify the functionality of COMP-GCD-COND

(defund comp-gcd-cond$op (x)
  (append (car x) (cdr x)))

;; The operation of COMP-GCD-COND over a data sequence

(defun comp-gcd-cond$op-map (x)
  (if (atom x)
      nil
    (cons (comp-gcd-cond$op (car x))
          (comp-gcd-cond$op-map (cdr x)))))

(defthm len-of-comp-gcd-cond$op-map
  (equal (len (comp-gcd-cond$op-map x))
         (len x)))

(defthm comp-gcd-cond$op-map-of-append
  (equal (comp-gcd-cond$op-map (append x y))
         (append (comp-gcd-cond$op-map x)
                 (comp-gcd-cond$op-map y))))

;; The extraction function for COMP-GCD-COND that extracts the future output
;; sequence from the current state.

(defund comp-gcd-cond$extract (st)
  (b* ((a0 (get-field *comp-gcd-cond$a0* st))
       (b0 (get-field *comp-gcd-cond$b0* st))
       (a1 (get-field *comp-gcd-cond$a1* st))
       (b1 (get-field *comp-gcd-cond$b1* st))
       (q2 (get-field *comp-gcd-cond$q2* st))
       (q3 (get-field *comp-gcd-cond$q3* st))

       (a-seq (append (extract-valid-data (list a0))
                      (queue2$extract q2)
                      (extract-valid-data (list a1))))
       (b-seq (append (extract-valid-data (list b0))
                      (queue3$extract q3)
                      (extract-valid-data (list b1)))))
    (comp-gcd-cond$op-map (pairlis$ a-seq b-seq))))

(defthm comp-gcd-cond$extract-not-empty-1
  (implies (and (comp-gcd-cond$out-act0 inputs st data-width)
                (comp-gcd-cond$valid-st st data-width))
           (< 0 (len (comp-gcd-cond$extract st))))
  :hints (("Goal"
           :in-theory (e/d (branch$act0
                            gcd-cond$br-inputs
                            gcd-cond$act0
                            comp-gcd-cond$br-inputs
                            comp-gcd-cond$out-act0
                            comp-gcd-cond$valid-st
                            comp-gcd-cond$extract)
                           ())))
  :rule-classes :linear)

(defthm comp-gcd-cond$extract-not-empty-2
  (implies (and (comp-gcd-cond$out-act1 inputs st data-width)
                (comp-gcd-cond$valid-st st data-width))
           (< 0 (len (comp-gcd-cond$extract st))))
  :hints (("Goal"
           :in-theory (e/d (branch$act1
                            gcd-cond$br-inputs
                            gcd-cond$act1
                            comp-gcd-cond$br-inputs
                            comp-gcd-cond$out-act1
                            comp-gcd-cond$valid-st
                            comp-gcd-cond$extract)
                           ())))
  :rule-classes :linear)

;; Specify and prove a state invariant

(progn
  (defund comp-gcd-cond$inv (st)
    (b* ((a0 (get-field *comp-gcd-cond$a0* st))
         (b0 (get-field *comp-gcd-cond$b0* st))
         (a1 (get-field *comp-gcd-cond$a1* st))
         (b1 (get-field *comp-gcd-cond$b1* st))
         (q2 (get-field *comp-gcd-cond$q2* st))
         (q3 (get-field *comp-gcd-cond$q3* st))

         (a-seq (append (extract-valid-data (list a0))
                        (queue2$extract q2)
                        (extract-valid-data (list a1))))
         (b-seq (append (extract-valid-data (list b0))
                        (queue3$extract q3)
                        (extract-valid-data (list b1)))))
      (equal (len a-seq) (len b-seq))))

  (local
   (defthm comp-gcd-cond$q2-in-act-inactive
     (implies (equal (nth *link$s*
                          (nth *comp-gcd-cond$a0* st))
                     '(nil))
              (not (queue2$in-act (comp-gcd-cond$q2-inputs
                                   inputs st data-width)
                                  (nth *comp-gcd-cond$q2* st)
                                  data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 comp-gcd-cond$q2-inputs)))))

  (local
   (defthm comp-gcd-cond$q3-in-act-inactive
     (implies (equal (nth *link$s*
                          (nth *comp-gcd-cond$b0* st))
                     '(nil))
              (not (queue3$in-act (comp-gcd-cond$q3-inputs
                                   inputs st data-width)
                                  (nth *comp-gcd-cond$q3* st)
                                  data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 comp-gcd-cond$q3-inputs)))))

  (local
   (defthm comp-gcd-cond$q2-out-act-inactive
     (implies (equal (nth *link$s*
                          (nth *comp-gcd-cond$a1* st))
                     '(t))
              (not (queue2$out-act (comp-gcd-cond$q2-inputs
                                    inputs st data-width)
                                   (nth *comp-gcd-cond$q2* st)
                                   data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 comp-gcd-cond$q2-inputs)))))

  (local
   (defthm comp-gcd-cond$q3-out-act-inactive
     (implies (equal (nth *link$s*
                          (nth *comp-gcd-cond$b1* st))
                     '(t))
              (not (queue3$out-act (comp-gcd-cond$q3-inputs
                                    inputs st data-width)
                                   (nth *comp-gcd-cond$q3* st)
                                   data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 comp-gcd-cond$q3-inputs)))))

  (defthm comp-gcd-cond$inv-preserved
    (implies (and (comp-gcd-cond$input-format inputs data-width)
                  (comp-gcd-cond$valid-st st data-width)
                  (comp-gcd-cond$inv st))
             (comp-gcd-cond$inv
              (comp-gcd-cond$step inputs st data-width)))
    :hints (("Goal"
             :use (comp-gcd-cond$input-format=>q2$input-format
                   comp-gcd-cond$input-format=>q3$input-format)
             :in-theory (e/d (get-field
                              f-sr
                              queue2$extracted-step
                              queue3$extracted-step
                              branch$act0
                              branch$act1
                              gcd-cond$act0
                              gcd-cond$act1
                              gcd-cond$flag
                              gcd-cond$data-in
                              gcd-cond$br-inputs
                              comp-gcd-cond$valid-st
                              comp-gcd-cond$inv
                              comp-gcd-cond$step
                              comp-gcd-cond$br-inputs
                              comp-gcd-cond$in-act
                              comp-gcd-cond$out-act
                              comp-gcd-cond$out-act0
                              comp-gcd-cond$out-act1)
                             (comp-gcd-cond$input-format=>q2$input-format
                              comp-gcd-cond$input-format=>q3$input-format
                              b-nor3
                              b-not)))))
  )

;; The extracted next-state function for COMP-GCD-COND.  Note that this
;; function avoids exploring the internal computation of COMP-GCD-COND.

(defund comp-gcd-cond$extracted-step (inputs st data-width)
  (b* ((a (take data-width (comp-gcd-cond$data-in inputs data-width)))
       (b (nthcdr data-width (comp-gcd-cond$data-in inputs data-width)))
       (data (comp-gcd-cond$op (cons a b)))
       (extracted-st (comp-gcd-cond$extract st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-gcd-cond$out-act inputs st data-width) t)
      (cond
       ((equal (comp-gcd-cond$in-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (comp-gcd-cond$in-act inputs st data-width) t)
          (cons data extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(local
 (defthm comp-gcd-cond$input-format-lemma-1
   (implies (comp-gcd-cond$input-format inputs data-width)
            (booleanp (nth 0 inputs)))
   :hints (("Goal" :in-theory (enable comp-gcd-cond$input-format)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm comp-gcd-cond$input-format-lemma-2
   (implies (comp-gcd-cond$input-format inputs data-width)
            (booleanp (nth 1 inputs)))
   :hints (("Goal" :in-theory (enable comp-gcd-cond$input-format)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm comp-gcd-cond$input-format-lemma-3
   (implies (comp-gcd-cond$input-format inputs data-width)
            (booleanp (nth 2 inputs)))
   :hints (("Goal" :in-theory (enable comp-gcd-cond$input-format)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm comp-gcd-cond$input-format-lemma-4
   (implies (and (comp-gcd-cond$input-format inputs data-width)
                 (nth 0 inputs))
            (bvp (comp-gcd-cond$data-in inputs data-width)))
   :hints (("Goal" :in-theory (enable comp-gcd-cond$input-format)))))

(encapsulate
  ()

  (local
   (defthm comp-gcd-cond$q2-data-in-rewrite
     (b* ((a0 (get-field *comp-gcd-cond$a0* st))
          (a0.d (get-field *link$d* a0)))
       (implies (and (bvp (strip-cars a0.d))
                     (equal (len a0.d) data-width))
                (equal (queue2$data-in
                        (comp-gcd-cond$q2-inputs inputs st data-width)
                        data-width)
                       (strip-cars a0.d))))
     :hints (("Goal"
              :in-theory (enable queue2$data-in
                                 comp-gcd-cond$q2-inputs)))))

  (local
   (defthm comp-gcd-cond$q3-data-in-rewrite
     (b* ((b0 (get-field *comp-gcd-cond$b0* st))
          (b0.d (get-field *link$d* b0)))
       (implies (and (bvp (strip-cars b0.d))
                     (equal (len b0.d) data-width))
                (equal (queue3$data-in
                        (comp-gcd-cond$q3-inputs inputs st data-width)
                        data-width)
                       (strip-cars b0.d))))
     :hints (("Goal"
              :in-theory (enable queue3$data-in
                                 comp-gcd-cond$q3-inputs)))))

  (local
   (defthm comp-gcd-cond$extracted-step-correct-aux
     (and (equal (cons e (append (queue2$extract st)
                                 x))
                 (append (cons e (queue2$extract st))
                         x))
          (equal (cons e (append (queue3$extract st)
                                 x))
                 (append (cons e (queue3$extract st))
                         x)))))

  (defthm comp-gcd-cond$extracted-step-correct
    (b* ((next-st (comp-gcd-cond$step inputs st data-width)))
      (implies (and (comp-gcd-cond$input-format inputs data-width)
                    (comp-gcd-cond$valid-st st data-width)
                    (comp-gcd-cond$inv st))
               (equal (comp-gcd-cond$extract next-st)
                      (comp-gcd-cond$extracted-step inputs st data-width))))
    :hints (("Goal"
             :use (comp-gcd-cond$input-format=>q2$input-format
                   comp-gcd-cond$input-format=>q3$input-format)
             :in-theory (e/d (get-field
                              f-sr
                              joint-act
                              queue2$extracted-step
                              queue3$extracted-step
                              branch$act0
                              branch$act1
                              gcd-cond$act0
                              gcd-cond$act1
                              gcd-cond$flag
                              gcd-cond$data-in
                              gcd-cond$br-inputs
                              comp-gcd-cond$extracted-step
                              comp-gcd-cond$valid-st
                              comp-gcd-cond$inv
                              comp-gcd-cond$step
                              comp-gcd-cond$br-inputs
                              comp-gcd-cond$in-act
                              comp-gcd-cond$out-act
                              comp-gcd-cond$out-act0
                              comp-gcd-cond$out-act1
                              comp-gcd-cond$extract)
                             (comp-gcd-cond$input-format=>q2$input-format
                              comp-gcd-cond$input-format=>q3$input-format
                              comp-gcd-cond$out-act-mutually-exclusive
                              b-nor3
                              b-not
                              b-or
                              strip-cars
                              acl2::append-of-cons)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that comp-gcd-cond$valid-st is an invariant.

(defthm comp-gcd-cond$valid-st-preserved
  (implies (and (comp-gcd-cond$input-format inputs data-width)
                (comp-gcd-cond$valid-st st data-width))
           (comp-gcd-cond$valid-st (comp-gcd-cond$step inputs st data-width)
                                   data-width))
  :hints (("Goal"
           :use (comp-gcd-cond$input-format=>q2$input-format
                 comp-gcd-cond$input-format=>q3$input-format)
           :in-theory (e/d (get-field
                            f-sr
                            joint-act
                            branch$act0
                            branch$act1
                            gcd-cond$act0
                            gcd-cond$act1
                            gcd-cond$flag
                            gcd-cond$data-in
                            gcd-cond$br-inputs
                            comp-gcd-cond$valid-st
                            comp-gcd-cond$st-format
                            comp-gcd-cond$step
                            comp-gcd-cond$br-inputs
                            comp-gcd-cond$in-act
                            comp-gcd-cond$out-act
                            comp-gcd-cond$out-act0
                            comp-gcd-cond$out-act1)
                           (comp-gcd-cond$input-format=>q2$input-format
                            comp-gcd-cond$input-format=>q3$input-format
                            b-not
                            b-or
                            b-nor3
                            take-of-too-many)))))

(encapsulate
  ()

  (local
   (defthm comp-gcd-cond$data-outs-rewrite
     (b* ((a1 (get-field *comp-gcd-cond$a1* st))
          (a1.d (get-field *link$d* a1))
          (b1 (get-field *comp-gcd-cond$b1* st))
          (b1.d (get-field *link$d* b1)))
       (implies (and (comp-gcd-cond$valid-st st data-width)
                     (comp-gcd-cond$out-act inputs st data-width))
                (equal (comp-gcd-cond$data1-out inputs st data-width)
                       (comp-gcd-cond$op (cons (strip-cars a1.d)
                                               (strip-cars b1.d))))))
     :hints (("Goal" :in-theory (e/d (branch$act0
                                      branch$act1
                                      gcd-cond$data-in
                                      gcd-cond$br-inputs
                                      gcd-cond$act0
                                      gcd-cond$act1
                                      gcd-cond$data1-out
                                      comp-gcd-cond$valid-st
                                      comp-gcd-cond$out-act
                                      comp-gcd-cond$out-act0
                                      comp-gcd-cond$out-act1
                                      comp-gcd-cond$br-inputs
                                      comp-gcd-cond$data1-out
                                      comp-gcd-cond$op)
                                     ())))))

  (defthm comp-gcd-cond$extract-lemma
    (implies
     (and (comp-gcd-cond$valid-st st data-width)
          (comp-gcd-cond$inv st)
          (comp-gcd-cond$out-act inputs st data-width))
     (equal (list (comp-gcd-cond$data1-out inputs st data-width))
            (nthcdr (1- (len (comp-gcd-cond$extract st)))
                    (comp-gcd-cond$extract st))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (left-associativity-of-append
                              branch$act0
                              branch$act1
                              gcd-cond$br-inputs
                              gcd-cond$act0
                              gcd-cond$act1
                              comp-gcd-cond$valid-st
                              comp-gcd-cond$inv
                              comp-gcd-cond$extract
                              comp-gcd-cond$br-inputs
                              comp-gcd-cond$out-act
                              comp-gcd-cond$out-act0
                              comp-gcd-cond$out-act1)
                             (acl2::append-of-cons
                              associativity-of-append
                              append)))))
  )

;; Extract the accepted input sequence

(seq-gen comp-gcd-cond in in-act 0
         (cons (take data-width
                     (comp-gcd-cond$data-in inputs data-width))
               (nthcdr data-width
                       (comp-gcd-cond$data-in inputs data-width))))

;; Extract the valid output sequence

(seq-gen comp-gcd-cond out out-act 1
         (comp-gcd-cond$data1-out inputs st data-width)
         :netlist-data (nthcdr (+ 5 data-width) outputs))

;; The multi-step input-output relationship

(in-out-stream-lemma comp-gcd-cond :op comp-gcd-cond$op :inv t)

