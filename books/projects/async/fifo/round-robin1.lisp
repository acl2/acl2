;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; February 2018

(in-package "ADE")

(include-book "alt-branch")
(include-book "alt-merge")
(include-book "queue2")
(include-book "queue3")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of RR1
;;; 2. Specifying the Final State of RR1 After An N-Step Execution
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of RR1
;;
;; Constructing a DE module generator for a round-robin circuit, RR1, using the
;; link-joint model. Proving the value and state lemmas for this module
;; generator.

(defconst *round-robin1$go-num* (+ *queue2$go-num*
                                   *queue3$go-num*
                                   *alt-branch$go-num*
                                   *alt-merge$go-num*))
(defconst *round-robin1$st-len* 12)

(defun round-robin1$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun round-robin1$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (round-robin1$data-ins-len data-width)
     *round-robin1$go-num*))

;; DE module generator of RR1. It reports the "in-act" signal at its input
;; port, and the "out-act" signal and output data at its output port. The
;; alt-branch joint in RR1 accepts input data and places them alternately into
;; two queues. The alt-merge joint takes data alternately from two queues and
;; delivers them as outputs.

(module-generator
 round-robin1* (data-width)
 (si 'round-robin1 data-width)
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 data-width)
                                    (sis 'go 0 *round-robin1$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-width))
 '(la0 a0 lb0 b0 la1 a1 lb1 b1 q2 q3 br me)
 (list
  ;; LINKS
  ;; A0
  '(la0 (a0-status) link-cntl (br-act0 q2-in-act))
  (list 'a0
        (sis 'a0-out 0 data-width)
        (si 'latch-n data-width)
        (list* 'br-act0 (sis 'data 0 data-width)))

  ;; B0
  '(lb0 (b0-status) link-cntl (br-act1 q3-in-act))
  (list 'b0
        (sis 'b0-out 0 data-width)
        (si 'latch-n data-width)
        (list* 'br-act1 (sis 'data 0 data-width)))

  ;; A1
  '(la1 (a1-status) link-cntl (q2-out-act me-act0))
  (list 'a1
        (sis 'a1-out 0 data-width)
        (si 'latch-n data-width)
        (list* 'q2-out-act (sis 'q2-data-out 0 data-width)))

  ;; B1
  '(lb1 (b1-status) link-cntl (q3-out-act me-act1))
  (list 'b1
        (sis 'b1-out 0 data-width)
        (si 'latch-n data-width)
        (list* 'q3-out-act (sis 'q3-data-out 0 data-width)))

  ;; JOINTS
  ;; 2-link queue Q2
  (list 'q2
        (list* 'q2-in-act 'q2-out-act
               (sis 'q2-data-out 0 data-width))
        (si 'queue2 data-width)
        (list* 'a0-status 'a1-status
               (append (sis 'a0-out 0 data-width)
                       (sis 'go 0 *queue2$go-num*))))

  ;; 3-link queue Q3
  (list 'q3
        (list* 'q3-in-act 'q3-out-act
               (sis 'q3-data-out 0 data-width))
        (si 'queue3 data-width)
        (list* 'b0-status 'b1-status
               (append (sis 'b0-out 0 data-width)
                       (sis 'go
                            *queue2$go-num*
                            *queue3$go-num*))))

  ;; Alt-Branch
  (list 'br
        (list* 'in-act 'br-act0 'br-act1
               (sis 'data 0 data-width))
        (si 'alt-branch data-width)
        (list* 'full-in 'a0-status 'b0-status
               (append (sis 'data-in 0 data-width)
                       (sis 'go
                            (+ *queue2$go-num*
                               *queue3$go-num*)
                            *alt-branch$go-num*))))

  ;; Alt-Merge
  (list 'me
        (list* 'out-act 'me-act0 'me-act1
               (sis 'data-out 0 data-width))
        (si 'alt-merge data-width)
        (list* 'a1-status 'b1-status 'empty-out-
               (append (sis 'a1-out 0 data-width)
                       (sis 'b1-out 0 data-width)
                       (sis 'go
                            (+ *queue2$go-num*
                               *queue3$go-num*
                               *alt-branch$go-num*)
                            *alt-merge$go-num*)))))

 :guard (natp data-width))

;; DE netlist generator. A generated netlist will contain an instance of RR1.

(defun round-robin1$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (round-robin1* data-width)
        (union$ (queue2$netlist data-width)
                (queue3$netlist data-width)
                (alt-branch$netlist data-width)
                (alt-merge$netlist data-width)
                :test 'equal)))

;; Sanity syntactic check

(defthmd round-robin1$netlist-64-okp
  (and (net-syntax-okp (round-robin1$netlist 64))
       (net-arity-okp (round-robin1$netlist 64))))

;; Recognizer for RR1

(defund round-robin1& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (and (equal (assoc (si 'round-robin1 data-width) netlist)
              (round-robin1* data-width))
       (b* ((netlist (delete-to-eq (si 'round-robin1 data-width) netlist)))
         (and (queue2& netlist data-width)
              (queue3& netlist data-width)
              (alt-branch& netlist data-width)
              (alt-merge& netlist data-width)
              (latch-n& netlist data-width)))))

;; Sanity check

(defthm check-round-robin1$netlist-64
  (round-robin1& (round-robin1$netlist 64) 64))

(defconst *round-robin1$la0* 0)
(defconst *round-robin1$a0*  1)
(defconst *round-robin1$lb0* 2)
(defconst *round-robin1$b0*  3)
(defconst *round-robin1$la1* 4)
(defconst *round-robin1$a1*  5)
(defconst *round-robin1$lb1* 6)
(defconst *round-robin1$b1*  7)
(defconst *round-robin1$q2*  8)
(defconst *round-robin1$q3*  9)
(defconst *round-robin1$br* 10)
(defconst *round-robin1$me* 11)

;; Constraints on the state of RR1

(defund round-robin1$st-format (st data-width)
  (b* ((a0  (get-field *round-robin1$a0* st))
       (b0  (get-field *round-robin1$b0* st))
       (a1  (get-field *round-robin1$a1* st))
       (b1  (get-field *round-robin1$b1* st))
       (q2  (get-field *round-robin1$q2* st))
       (q3  (get-field *round-robin1$q3* st)))
    (and (len-1-true-listp a0)
         (equal (len a0) data-width)

         (len-1-true-listp b0)
         (equal (len b0) data-width)

         (len-1-true-listp a1)
         (equal (len a1) data-width)

         (len-1-true-listp b1)
         (equal (len b1) data-width)

         (queue2$st-format q2 data-width)
         (queue3$st-format q3 data-width))))

(defthmd round-robin1$st-format=>natp-data-width
  (implies (round-robin1$st-format st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable round-robin1$st-format)))
  :rule-classes :forward-chaining)

(defund round-robin1$valid-st (st data-width)
  (b* ((la0 (get-field *round-robin1$la0* st))
       (a0  (get-field *round-robin1$a0* st))
       (lb0 (get-field *round-robin1$lb0* st))
       (b0  (get-field *round-robin1$b0* st))
       (la1 (get-field *round-robin1$la1* st))
       (a1  (get-field *round-robin1$a1* st))
       (lb1 (get-field *round-robin1$lb1* st))
       (b1  (get-field *round-robin1$b1* st))
       (q2  (get-field *round-robin1$q2* st))
       (q3  (get-field *round-robin1$q3* st))
       (br  (get-field *round-robin1$br* st))
       (me  (get-field *round-robin1$me* st)))
    (and (round-robin1$st-format st data-width)

         (validp la0)
         (or (emptyp la0)
             (bvp (strip-cars a0)))

         (validp lb0)
         (or (emptyp lb0)
             (bvp (strip-cars b0)))

         (validp la1)
         (or (emptyp la1)
             (bvp (strip-cars a1)))

         (validp lb1)
         (or (emptyp lb1)
             (bvp (strip-cars b1)))

         (queue2$valid-st q2 data-width)
         (queue3$valid-st q3 data-width)

         (alt-branch$valid-st br)
         (alt-merge$valid-st me))))

(defthmd round-robin1$valid-st=>natp-data-width
  (implies (round-robin1$valid-st st data-width)
           (natp data-width))
  :hints (("Goal" :in-theory (enable round-robin1$st-format=>natp-data-width
                                     round-robin1$valid-st)))
  :rule-classes :forward-chaining)

;; RR1 simulator

(progn
  (defun round-robin1$map-to-links (st)
    (b* ((la0 (get-field *round-robin1$la0* st))
         (a0  (get-field *round-robin1$a0* st))
         (lb0 (get-field *round-robin1$lb0* st))
         (b0  (get-field *round-robin1$b0* st))
         (la1 (get-field *round-robin1$la1* st))
         (a1  (get-field *round-robin1$a1* st))
         (lb1 (get-field *round-robin1$lb1* st))
         (b1  (get-field *round-robin1$b1* st))
         (q2  (get-field *round-robin1$q2* st))
         (q3  (get-field *round-robin1$q3* st))
         (br  (get-field *round-robin1$br* st))
         (me  (get-field *round-robin1$me* st)))
      (append (list (cons 'alt-branch (alt-branch$map-to-links br)))
              (map-to-links (list (list 'a0 la0 a0)
                                  (list 'b0 lb0 b0)))
              (cons (cons 'Q2 (queue2$map-to-links q2))
                    (cons (cons 'Q3 (queue3$map-to-links q3))
                          (map-to-links (list (list 'a1 la1 a1)
                                              (list 'b1 lb1 b1)))))
              (list (cons 'alt-merge (alt-merge$map-to-links me))))))

  (defun round-robin1$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (round-robin1$map-to-links (car x))
            (round-robin1$map-to-links-list (cdr x)))))

  (defund round-robin1$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (round-robin1$ins-len data-width))
         ((mv inputs-lst state)
          (signal-vals-gen num-signals n state nil))
         ;;(- (cw "~x0~%" inputs-lst))
         (full '(t))
         (empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (la0 empty)
         (a0 invalid-data)
         (lb0 empty)
         (b0 invalid-data)
         (la1 empty)
         (a1 invalid-data)
         (lb1 empty)
         (b1 invalid-data)
         (q2 (list empty invalid-data
                   empty invalid-data))
         (q3 (list empty invalid-data
                   empty invalid-data
                   empty invalid-data))
         (br (list full '(nil)
                   empty '(x)))
         (me (list full '(nil)
                   empty '(x)))
         (st (list la0 a0 lb0 b0 la1 a1 lb1 b1 q2 q3 br me)))
      (mv (pretty-list
           (remove-dup-neighbors
            (round-robin1$map-to-links-list
             (de-sim-list (si 'round-robin1 data-width)
                          inputs-lst
                          st
                          (round-robin1$netlist data-width))))
           0)
          state)))
  )

;; Extracting the input data

(defun round-robin1$data-in (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (take (mbe :logic (nfix data-width)
             :exec  data-width)
        (nthcdr 2 inputs)))

(defthm len-round-robin1$data-in
  (equal (len (round-robin1$data-in inputs data-width))
         (nfix data-width)))

(in-theory (disable round-robin1$data-in))

;; Extracting the inputs for the Q2 joint

(defund round-robin1$q2-inputs (inputs st data-width)
  (b* ((go-signals (nthcdr (round-robin1$data-ins-len data-width) inputs))

       (q2-go-signals (take *queue2$go-num* go-signals))

       (la0 (get-field *round-robin1$la0* st))
       (a0  (get-field *round-robin1$a0* st))
       (la1 (get-field *round-robin1$la1* st)))

    (list* (f-buf (car la0)) (f-buf (car la1))
           (append (v-threefix (strip-cars a0))
                   q2-go-signals))))

;; Extracting the inputs for the Q3 joint

(defund round-robin1$q3-inputs (inputs st data-width)
  (b* ((go-signals (nthcdr (round-robin1$data-ins-len data-width) inputs))

       (q3-go-signals (take *queue3$go-num*
                            (nthcdr *queue2$go-num*
                                    go-signals)))

       (lb0 (get-field *round-robin1$lb0* st))
       (b0  (get-field *round-robin1$b0* st))
       (lb1 (get-field *round-robin1$lb1* st)))

    (list* (f-buf (car lb0)) (f-buf (car lb1))
           (append (v-threefix (strip-cars b0))
                   q3-go-signals))))

;; Extracting the inputs for the alt-branch joint

(defund round-robin1$br-inputs (inputs st data-width)
  (b* ((full-in    (nth 0 inputs))
       (data-in    (round-robin1$data-in inputs data-width))
       (go-signals (nthcdr (round-robin1$data-ins-len data-width) inputs))

       (br-go-signals (take *alt-branch$go-num*
                            (nthcdr (+ *queue2$go-num*
                                       *queue3$go-num*)
                                    go-signals)))

       (la0 (get-field *round-robin1$la0* st))
       (lb0 (get-field *round-robin1$lb0* st)))

    (list* full-in (f-buf (car la0)) (f-buf (car lb0))
           (append data-in br-go-signals))))

;; Extracting the inputs for the alt-merge joint

(defund round-robin1$me-inputs (inputs st data-width)
  (b* ((empty-out-  (nth 1 inputs))
       (go-signals (nthcdr (round-robin1$data-ins-len data-width) inputs))

       (me-go-signals (nthcdr (+ *queue2$go-num*
                                 *queue3$go-num*
                                 *alt-branch$go-num*)
                              go-signals))

       (la1 (get-field *round-robin1$la1* st))
       (a1  (get-field *round-robin1$a1* st))
       (lb1 (get-field *round-robin1$lb1* st))
       (b1  (get-field *round-robin1$b1* st)))

    (list* (f-buf (car la1)) (f-buf (car lb1)) empty-out-
           (append (v-threefix (strip-cars a1))
                   (v-threefix (strip-cars b1))
                   me-go-signals))))

;; Extracting the "in-act" signal

(defund round-robin1$in-act (inputs st data-width)
  (b* ((br-inputs (round-robin1$br-inputs inputs st data-width))
       (br (get-field *round-robin1$br* st)))
    (alt-branch$act br-inputs br data-width)))

;; Extracting the "out-act" signal

(defund round-robin1$out-act (inputs st data-width)
  (b* ((me-inputs (round-robin1$me-inputs inputs st data-width))
       (me (get-field *round-robin1$me* st)))
    (alt-merge$act me-inputs me data-width)))

;; Extracting the output data

(defund round-robin1$data-out (st)
  (b* ((a1 (get-field *round-robin1$a1* st))
       (b1 (get-field *round-robin1$b1* st))
       (me (get-field *round-robin1$me* st))

       (me-select (get-field *alt-merge$select* me)))
    (fv-if (car me-select)
           (strip-cars b1)
           (strip-cars a1))))

(defthm len-round-robin1$data-out-1
  (implies (round-robin1$st-format st data-width)
           (equal (len (round-robin1$data-out st))
                  data-width))
  :hints (("Goal" :in-theory (enable round-robin1$st-format
                                     round-robin1$data-out))))

(defthm len-round-robin1$data-out-2
  (implies (round-robin1$valid-st st data-width)
           (equal (len (round-robin1$data-out st))
                  data-width))
  :hints (("Goal" :in-theory (enable round-robin1$valid-st))))

(defthm bvp-round-robin1$data-out
  (implies (and (round-robin1$valid-st st data-width)
                (round-robin1$out-act inputs st data-width))
           (bvp (round-robin1$data-out st)))
  :hints (("Goal" :in-theory (enable f-and3
                                     f-and
                                     joint-act
                                     round-robin1$valid-st
                                     round-robin1$st-format
                                     round-robin1$out-act
                                     round-robin1$data-out
                                     round-robin1$me-inputs
                                     alt-merge$valid-st
                                     alt-merge$act
                                     alt-merge$act0
                                     alt-merge$act1))))

(not-primp-lemma round-robin1)

;; The value lemma for RR1

(defthmd round-robin1$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (posp data-width)
                  (round-robin1& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *round-robin1$go-num*)
                  (round-robin1$st-format st data-width))
             (equal (se (si 'round-robin1 data-width) inputs st netlist)
                    (list* (round-robin1$in-act inputs st data-width)
                           (round-robin1$out-act inputs st data-width)
                           (round-robin1$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :expand (se (si 'round-robin1 data-width)
                       (list* full-in empty-out-
                              (append data-in go-signals))
                       st
                       netlist)
           :in-theory (e/d (de-rules
                            get-field
                            len-1-true-listp=>true-listp
                            not-primp-round-robin1
                            round-robin1&
                            round-robin1*$destructure
                            round-robin1$data-in
                            queue2$value
                            queue3$value
                            alt-branch$value
                            alt-merge$value
                            latch-n$value
                            round-robin1$st-format
                            round-robin1$in-act
                            round-robin1$out-act
                            round-robin1$data-out
                            round-robin1$br-inputs
                            round-robin1$me-inputs)
                           ((round-robin1*)
                            validp
                            fullp
                            emptyp
                            de-module-disabled-rules)))))

;; This function specifies the next state of RR1.

(defun round-robin1$state-fn (inputs st data-width)
  (b* ((data-in (round-robin1$data-in inputs data-width))

       (la0 (get-field *round-robin1$la0* st))
       (a0  (get-field *round-robin1$a0* st))
       (lb0 (get-field *round-robin1$lb0* st))
       (b0  (get-field *round-robin1$b0* st))
       (la1 (get-field *round-robin1$la1* st))
       (a1  (get-field *round-robin1$a1* st))
       (lb1 (get-field *round-robin1$lb1* st))
       (b1  (get-field *round-robin1$b1* st))
       (q2  (get-field *round-robin1$q2* st))
       (q3  (get-field *round-robin1$q3* st))
       (br  (get-field *round-robin1$br* st))
       (me  (get-field *round-robin1$me* st))

       (q2-inputs (round-robin1$q2-inputs inputs st data-width))
       (q2-in-act (queue2$in-act q2-inputs q2 data-width))
       (q2-out-act (queue2$out-act q2-inputs q2 data-width))
       (q2-data-out (queue2$data-out q2))

       (q3-inputs (round-robin1$q3-inputs inputs st data-width))
       (q3-in-act (queue3$in-act q3-inputs q3 data-width))
       (q3-out-act (queue3$out-act q3-inputs q3 data-width))
       (q3-data-out (queue3$data-out q3))

       (br-inputs (round-robin1$br-inputs inputs st data-width))
       (br-act0 (alt-branch$act0 br-inputs br data-width))
       (br-act1 (alt-branch$act1 br-inputs br data-width))

       (me-inputs (round-robin1$me-inputs inputs st data-width))
       (me-act0 (alt-merge$act0 me-inputs me data-width))
       (me-act1 (alt-merge$act1 me-inputs me data-width)))

    (list
     ;; A0
     (list (f-sr br-act0 q2-in-act (car la0)))
     (pairlis$ (fv-if br-act0 data-in (strip-cars a0))
               nil)

     ;; B0
     (list (f-sr br-act1 q3-in-act (car lb0)))
     (pairlis$ (fv-if br-act1 data-in (strip-cars b0))
               nil)

     ;; A1
     (list (f-sr q2-out-act me-act0 (car la1)))
     (pairlis$ (fv-if q2-out-act q2-data-out (strip-cars a1))
               nil)

     ;; B1
     (list (f-sr q3-out-act me-act1 (car lb1)))
     (pairlis$ (fv-if q3-out-act q3-data-out (strip-cars b1))
               nil)

     ;; Joint Q2
     (queue2$state-fn q2-inputs q2 data-width)
     ;; Joint Q3
     (queue3$state-fn q3-inputs q3 data-width)
     ;; Joint alt-branch
     (alt-branch$state-fn br-inputs br data-width)
     ;; Joint alt-merge
     (alt-merge$state-fn me-inputs me data-width))))

(defthm len-of-round-robin1$state-fn
  (equal (len (round-robin1$state-fn inputs st data-width))
         *round-robin1$st-len*))

;; The state lemma for RR1

(defthmd round-robin1$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (posp data-width)
                  (round-robin1& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *round-robin1$go-num*)
                  (round-robin1$st-format st data-width))
             (equal (de (si 'round-robin1 data-width) inputs st netlist)
                    (round-robin1$state-fn inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :expand (de (si 'round-robin1 data-width)
                       (list* full-in empty-out-
                              (append data-in go-signals))
                       st
                       netlist)
           :in-theory (e/d (de-rules
                            get-field
                            len-1-true-listp=>true-listp
                            not-primp-round-robin1
                            round-robin1&
                            round-robin1*$destructure
                            round-robin1$st-format
                            round-robin1$data-in
                            round-robin1$q2-inputs
                            round-robin1$q3-inputs
                            round-robin1$br-inputs
                            round-robin1$me-inputs
                            queue2$value queue2$state
                            queue3$value queue3$state
                            alt-branch$value alt-branch$state
                            alt-merge$value alt-merge$state
                            latch-n$value latch-n$state)
                           ((round-robin1*)
                            validp
                            fullp
                            emptyp
                            de-module-disabled-rules)))))

(in-theory (disable round-robin1$state-fn))

;; ======================================================================

;; 2. Specifying the Final State of RR1 After An N-Step Execution

;; Conditions on the inputs

(defund round-robin1$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (round-robin1$data-in inputs data-width))
       (go-signals (nthcdr (round-robin1$data-ins-len data-width) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *round-robin1$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(defthmd len-of-round-robin1$inputs
  (implies (round-robin1$input-format inputs data-width)
           (equal (len inputs) (round-robin1$ins-len data-width)))
  :hints (("Goal" :in-theory (enable round-robin1$input-format))))

(local
 (defthm round-robin1$input-format=>q2$input-format
   (implies (and (round-robin1$input-format inputs data-width)
                 (round-robin1$valid-st st data-width))
            (queue2$input-format
             (round-robin1$q2-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (round-robin1$input-format
                             queue2$input-format
                             queue2$data-in
                             round-robin1$valid-st
                             round-robin1$st-format
                             round-robin1$q2-inputs)
                            (nthcdr
                             len
                             take-of-too-many))))))

(local
 (defthm round-robin1$input-format=>q3$input-format
   (implies (and (round-robin1$input-format inputs data-width)
                 (round-robin1$valid-st st data-width))
            (queue3$input-format
             (round-robin1$q3-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (round-robin1$input-format
                             queue3$input-format
                             queue3$data-in
                             round-robin1$valid-st
                             round-robin1$st-format
                             round-robin1$q3-inputs)
                            (nthcdr
                             len
                             take-of-too-many))))))

(local
 (defthm round-robin1$input-format=>br$input-format
   (implies (and (round-robin1$input-format inputs data-width)
                 (round-robin1$valid-st st data-width))
            (alt-branch$input-format
             (round-robin1$br-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (round-robin1$input-format
                             alt-branch$input-format
                             alt-branch$data-in
                             round-robin1$valid-st
                             round-robin1$st-format
                             round-robin1$br-inputs)
                            (nthcdr
                             take-of-too-many))))))

(local
 (defthm round-robin1$input-format=>me$input-format
   (implies (and (round-robin1$input-format inputs data-width)
                 (round-robin1$valid-st st data-width))
            (alt-merge$input-format
             (round-robin1$me-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :use len-of-round-robin1$inputs
            :in-theory (e/d (round-robin1$input-format
                             alt-merge$input-format
                             alt-merge$data-in0
                             alt-merge$data-in1
                             round-robin1$valid-st
                             round-robin1$st-format
                             round-robin1$me-inputs)
                            (nthcdr
                             take-of-too-many))))))

;; Proving that round-robin1$st-format is an invariant.

(defthm round-robin1$st-format-preserved
  (implies (round-robin1$st-format st data-width)
           (round-robin1$st-format
            (round-robin1$state-fn inputs st data-width)
            data-width))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            round-robin1$st-format
                            round-robin1$state-fn)
                           ()))))

(defthmd round-robin1$state-alt
  (implies (and (posp data-width)
                (round-robin1& netlist data-width)
                (round-robin1$input-format inputs data-width)
                (round-robin1$st-format st data-width))
           (equal (de (si 'round-robin1 data-width) inputs st netlist)
                  (round-robin1$state-fn inputs st data-width)))
  :hints (("Goal"
           :in-theory (enable round-robin1$input-format)
           :use (:instance
                 round-robin1$state
                 (full-in    (nth 0 inputs))
                 (empty-out- (nth 1 inputs))
                 (data-in    (round-robin1$data-in inputs data-width))
                 (go-signals (nthcdr (round-robin1$data-ins-len data-width)
                                     inputs))))))

(state-fn-n-gen round-robin1 data-width)
(input-format-n-gen round-robin1 data-width)

(defthmd de-sim-n$round-robin1
  (implies (and (posp data-width)
                (round-robin1& netlist data-width)
                (round-robin1$input-format-n inputs-lst data-width n)
                (round-robin1$st-format st data-width))
           (equal (de-sim-n (si 'round-robin1 data-width)
                            inputs-lst st netlist
                            n)
                  (round-robin1$state-fn-n inputs-lst st data-width n)))
  :hints (("Goal" :in-theory (enable round-robin1$state-alt))))

;; ======================================================================

;; 3. Single-Step-Update Property

(defun interleave (l1 l2)
  (declare (xargs :guard t))
  (cond ((atom l1) l2)
        ((atom l2) l1)
        (t (append (list (car l1) (car l2))
                   (interleave (cdr l1) (cdr l2))))))

(defthm consp-interleave
  (implies (or (consp l1) (consp l2)
               (< 0 (len l1)) (< 0 (len l2)))
           (consp (interleave l1 l2)))
  :rule-classes :type-prescription)

(defthm true-listp-interleave
  (implies (and (true-listp l1)
                (true-listp l2))
           (true-listp (interleave l1 l2)))
  :rule-classes :type-prescription)

(defthm len-interleave
  (equal (len (interleave l1 l2))
         (+ (len l1) (len l2))))

(defthm len-of-cdr-interleave
  (implies (or (< 0 (len l1)) (< 0 (len l2)))
           (equal (len (cdr (interleave l1 l2)))
                  (+ -1 (len l1) (len l2)))))

(defthm interleave-append-1
  (implies (and (or (equal (len x1) (len x2))
                    (equal (len x1) (1+ (len x2))))
                (consp y))
           (equal (interleave (append x1 y) x2)
                  (append (interleave x1 x2) y))))

(defthm interleave-append-2
  (implies (and (<= (len x1) (1+ (len x2)))
                (consp y))
           (equal (interleave x1 (append x2 y))
                  (append (interleave x1 x2) y))))

(defthm interleave-append-append
  (implies (equal (len x1) (len x2))
           (equal (interleave (append x1 y1) (append x2 y2))
                  (append (interleave x1 x2) (interleave y1 y2)))))

;; The extraction function for RR1 that extracts the future output sequence
;; from the current state.

(defund round-robin1$extract-state (st)
  (b* ((la0 (get-field *round-robin1$la0* st))
       (a0  (get-field *round-robin1$a0* st))
       (lb0 (get-field *round-robin1$lb0* st))
       (b0  (get-field *round-robin1$b0* st))
       (la1 (get-field *round-robin1$la1* st))
       (a1  (get-field *round-robin1$a1* st))
       (lb1 (get-field *round-robin1$lb1* st))
       (b1  (get-field *round-robin1$b1* st))
       (q2  (get-field *round-robin1$q2* st))
       (q3  (get-field *round-robin1$q3* st))
       (me  (get-field *round-robin1$me* st))

       (a-seq (append (extract-state (list la0 a0))
                      (queue2$extract-state q2)
                      (extract-state (list la1 a1))))
       (b-seq (append (extract-state (list lb0 b0))
                      (queue3$extract-state q3)
                      (extract-state (list lb1 b1))))

       (me-lselect    (get-field *alt-merge$lselect* me))
       (me-select     (get-field *alt-merge$select* me))
       (me-select-buf (get-field *alt-merge$select-buf* me))
       (valid-me-select (if (fullp me-lselect)
                            (car me-select)
                          (car me-select-buf))))

    (cond ((< (len a-seq) (len b-seq))
           (interleave b-seq a-seq))
          ((< (len b-seq) (len a-seq))
           (interleave a-seq b-seq))
          (valid-me-select (interleave a-seq b-seq))
          (t (interleave b-seq a-seq)))))

(defthm round-robin1$extract-state-not-empty
  (implies (and (round-robin1$out-act inputs st data-width)
                (round-robin1$valid-st st data-width))
           (< 0 (len (round-robin1$extract-state st))))
  :hints (("Goal"
           :in-theory (e/d (f-and3
                            alt-merge$act
                            alt-merge$act0
                            alt-merge$act1
                            round-robin1$me-inputs
                            round-robin1$valid-st
                            round-robin1$extract-state
                            round-robin1$out-act)
                           (nfix))))
  :rule-classes :linear)

;; Specifying and proving a state invariant

(progn
  (defund round-robin1$inv (st)
    (b* ((la0 (get-field *round-robin1$la0* st))
         (a0  (get-field *round-robin1$a0* st))
         (lb0 (get-field *round-robin1$lb0* st))
         (b0  (get-field *round-robin1$b0* st))
         (la1 (get-field *round-robin1$la1* st))
         (a1  (get-field *round-robin1$a1* st))
         (lb1 (get-field *round-robin1$lb1* st))
         (b1  (get-field *round-robin1$b1* st))
         (q2  (get-field *round-robin1$q2* st))
         (q3  (get-field *round-robin1$q3* st))
         (br  (get-field *round-robin1$br* st))
         (me  (get-field *round-robin1$me* st))

         (a-seq (append (extract-state (list la0 a0))
                        (queue2$extract-state q2)
                        (extract-state (list la1 a1))))
         (b-seq (append (extract-state (list lb0 b0))
                        (queue3$extract-state q3)
                        (extract-state (list lb1 b1))))

         (br-lselect    (get-field *alt-branch$lselect* br))
         (br-select     (get-field *alt-branch$select* br))
         (br-select-buf (get-field *alt-branch$select-buf* br))
         (valid-br-select (if (fullp br-lselect)
                              (car br-select)
                            (car br-select-buf)))

         (me-lselect    (get-field *alt-merge$lselect* me))
         (me-select     (get-field *alt-merge$select* me))
         (me-select-buf (get-field *alt-merge$select-buf* me))
         (valid-me-select (if (fullp me-lselect)
                              (car me-select)
                            (car me-select-buf))))

      (and (alt-branch$inv br)
           (alt-merge$inv me)
           (or (and (equal (len a-seq) (len b-seq))
                    (equal valid-br-select valid-me-select))
               (and (equal (len a-seq) (1+ (len b-seq)))
                    valid-br-select
                    (not valid-me-select))
               (and (equal (1+ (len a-seq)) (len b-seq))
                    (not valid-br-select)
                    valid-me-select)))))

  (local
   (defthm booleanp-round-robin1$q2-in-act
     (implies (and (or (equal (nth *round-robin1$la0* st) '(t))
                       (equal (nth *round-robin1$la0* st) '(nil)))
                   (queue2$valid-st (nth *round-robin1$q2* st)
                                    data-width))
              (booleanp
               (queue2$in-act (round-robin1$q2-inputs inputs st data-width)
                              (nth *round-robin1$q2* st)
                              data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 round-robin1$q2-inputs
                                 queue2$valid-st
                                 queue2$in-act)))
     :rule-classes :type-prescription))

  (local
   (defthm booleanp-round-robin1$q3-in-act
     (implies (and (or (equal (nth *round-robin1$lb0* st) '(t))
                       (equal (nth *round-robin1$lb0* st) '(nil)))
                   (queue3$valid-st (nth *round-robin1$q3* st)
                                    data-width))
              (booleanp
               (queue3$in-act (round-robin1$q3-inputs inputs st data-width)
                              (nth *round-robin1$q3* st)
                              data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 round-robin1$q3-inputs
                                 queue3$valid-st
                                 queue3$in-act)))
     :rule-classes :type-prescription))

  (local
   (defthm round-robin1$q2-in-act-nil
     (implies (equal (nth *round-robin1$la0* st) '(nil))
              (not (queue2$in-act
                    (round-robin1$q2-inputs inputs st data-width)
                    (nth *round-robin1$q2* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 round-robin1$q2-inputs
                                 queue2$in-act)))))

  (local
   (defthm round-robin1$q3-in-act-nil
     (implies (equal (nth *round-robin1$lb0* st) '(nil))
              (not (queue3$in-act
                    (round-robin1$q3-inputs inputs st data-width)
                    (nth *round-robin1$q3* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 round-robin1$q3-inputs
                                 queue3$in-act)))))

  (local
   (defthm booleanp-round-robin1$q2-out-act
     (implies (and (or (equal (nth *round-robin1$la1* st) '(t))
                       (equal (nth *round-robin1$la1* st) '(nil)))
                   (queue2$valid-st (nth *round-robin1$q2* st)
                                    data-width))
              (booleanp
               (queue2$out-act (round-robin1$q2-inputs inputs st data-width)
                               (nth *round-robin1$q2* st)
                               data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 round-robin1$q2-inputs
                                 queue2$valid-st
                                 queue2$out-act)))
     :rule-classes :type-prescription))

  (local
   (defthm booleanp-round-robin1$q3-out-act
     (implies (and (or (equal (nth *round-robin1$lb1* st) '(t))
                       (equal (nth *round-robin1$lb1* st) '(nil)))
                   (queue3$valid-st (nth *round-robin1$q3* st)
                                    data-width))
              (booleanp
               (queue3$out-act (round-robin1$q3-inputs inputs st data-width)
                               (nth *round-robin1$q3* st)
                               data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 round-robin1$q3-inputs
                                 queue3$valid-st
                                 queue3$out-act)))
     :rule-classes :type-prescription))

  (local
   (defthm round-robin1$q2-out-act-nil
     (implies (equal (nth *round-robin1$la1* st) '(t))
              (not (queue2$out-act
                    (round-robin1$q2-inputs inputs st data-width)
                    (nth *round-robin1$q2* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 round-robin1$q2-inputs
                                 queue2$out-act)))))

  (local
   (defthm round-robin1$q3-out-act-nil
     (implies (equal (nth *round-robin1$lb1* st) '(t))
              (not (queue3$out-act
                    (round-robin1$q3-inputs inputs st data-width)
                    (nth *round-robin1$q3* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 round-robin1$q3-inputs
                                 queue3$out-act)))))

  (local
   (defthm booleanp-round-robin1$br-act0
     (implies (and (booleanp (nth 0 inputs))
                   (or (equal (nth *round-robin1$la0* st) '(t))
                       (equal (nth *round-robin1$la0* st) '(nil)))
                   (or (equal (nth *round-robin1$lb0* st) '(t))
                       (equal (nth *round-robin1$lb0* st) '(nil)))
                   (alt-branch$valid-st (nth *round-robin1$br* st)))
              (booleanp
               (alt-branch$act0 (round-robin1$br-inputs inputs st data-width)
                                (nth *round-robin1$br* st)
                                data-width)))
     :hints (("Goal" :in-theory (enable get-field
                                        round-robin1$br-inputs
                                        alt-branch$valid-st
                                        alt-branch$act0
                                        alt-branch$act)))
     :rule-classes :type-prescription))

  (local
   (defthm booleanp-round-robin1$br-act1
     (implies (and (booleanp (nth 0 inputs))
                   (or (equal (nth *round-robin1$la0* st) '(t))
                       (equal (nth *round-robin1$la0* st) '(nil)))
                   (or (equal (nth *round-robin1$lb0* st) '(t))
                       (equal (nth *round-robin1$lb0* st) '(nil)))
                   (alt-branch$valid-st (nth *round-robin1$br* st)))
              (booleanp
               (alt-branch$act1 (round-robin1$br-inputs inputs st data-width)
                                (nth *round-robin1$br* st)
                                data-width)))
     :hints (("Goal" :in-theory (enable get-field
                                        round-robin1$br-inputs
                                        alt-branch$valid-st
                                        alt-branch$act1
                                        alt-branch$act)))
     :rule-classes :type-prescription))

  (local
   (defthm round-robin1$br-act0-nil
     (implies (and (equal (nth *round-robin1$la0* st) '(t))
                   (alt-branch$valid-st (nth *round-robin1$br* st)))
              (not (alt-branch$act0
                    (round-robin1$br-inputs inputs st data-width)
                    (nth *round-robin1$br* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 f-if
                                 round-robin1$br-inputs
                                 alt-branch$valid-st
                                 alt-branch$act0
                                 alt-branch$act)))))

  (local
   (defthm round-robin1$br-act1-nil
     (implies (and (equal (nth *round-robin1$lb0* st) '(t))
                   (alt-branch$valid-st (nth *round-robin1$br* st)))
              (not (alt-branch$act1
                    (round-robin1$br-inputs inputs st data-width)
                    (nth *round-robin1$br* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 f-if
                                 round-robin1$br-inputs
                                 alt-branch$valid-st
                                 alt-branch$act1
                                 alt-branch$act)))))

  (local
   (defthm booleanp-round-robin1$me-act0
     (implies (and (booleanp (nth 1 inputs))
                   (or (equal (nth *round-robin1$la1* st) '(t))
                       (equal (nth *round-robin1$la1* st) '(nil)))
                   (or (equal (nth *round-robin1$lb1* st) '(t))
                       (equal (nth *round-robin1$lb1* st) '(nil)))
                   (alt-merge$valid-st (nth *round-robin1$me* st)))
              (booleanp
               (alt-merge$act0 (round-robin1$me-inputs inputs st data-width)
                               (nth *round-robin1$me* st)
                               data-width)))
     :hints (("Goal" :in-theory (enable get-field
                                        f-and3
                                        round-robin1$me-inputs
                                        alt-merge$valid-st
                                        alt-merge$act0
                                        alt-merge$act)))
     :rule-classes :type-prescription))

  (local
   (defthm booleanp-round-robin1$me-act1
     (implies (and (booleanp (nth 1 inputs))
                   (or (equal (nth *round-robin1$la1* st) '(t))
                       (equal (nth *round-robin1$la1* st) '(nil)))
                   (or (equal (nth *round-robin1$lb1* st) '(t))
                       (equal (nth *round-robin1$lb1* st) '(nil)))
                   (alt-merge$valid-st (nth *round-robin1$me* st)))
              (booleanp
               (alt-merge$act1 (round-robin1$me-inputs inputs st data-width)
                               (nth *round-robin1$me* st)
                               data-width)))
     :hints (("Goal" :in-theory (enable get-field
                                        f-and3
                                        round-robin1$me-inputs
                                        alt-merge$valid-st
                                        alt-merge$act1
                                        alt-merge$act)))
     :rule-classes :type-prescription))

  (local
   (defthm round-robin1$me-act0-nil
     (implies (and (equal (nth *round-robin1$la1* st) '(nil))
                   (alt-merge$valid-st (nth *round-robin1$me* st)))
              (not (alt-merge$act0
                    (round-robin1$me-inputs inputs st data-width)
                    (nth *round-robin1$me* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 f-and3
                                 f-if
                                 round-robin1$me-inputs
                                 alt-merge$valid-st
                                 alt-merge$act0
                                 alt-merge$act)))))

  (local
   (defthm round-robin1$me-act1-nil
     (implies (and (equal (nth *round-robin1$lb1* st) '(nil))
                   (alt-merge$valid-st (nth *round-robin1$me* st)))
              (not (alt-merge$act1
                    (round-robin1$me-inputs inputs st data-width)
                    (nth *round-robin1$me* st)
                    data-width)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 f-and3
                                 f-if
                                 round-robin1$me-inputs
                                 alt-merge$valid-st
                                 alt-merge$act1
                                 alt-merge$act)))))

  (defthm round-robin1$inv-preserved
    (implies (and (round-robin1$input-format inputs data-width)
                  (round-robin1$valid-st st data-width)
                  (round-robin1$inv st))
             (round-robin1$inv
              (round-robin1$state-fn inputs st data-width)))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              queue2$step-spec
                              queue3$step-spec
                              round-robin1$input-format
                              round-robin1$valid-st
                              round-robin1$inv
                              round-robin1$state-fn
                              round-robin1$in-act
                              round-robin1$out-act
                              round-robin1$br-inputs
                              round-robin1$me-inputs
                              alt-branch$valid-st
                              alt-branch$inv
                              alt-branch$state-fn
                              alt-branch$act
                              alt-branch$act0
                              alt-branch$act1
                              alt-merge$valid-st
                              alt-merge$inv
                              alt-merge$state-fn
                              alt-merge$act
                              alt-merge$act0
                              alt-merge$act1
                              f-sr)
                             (if*
                              nfix
                              nthcdr
                              append
                              pairlis$
                              strip-cars
                              default-car
                              default-cdr
                              default-+-1
                              default-+-2
                              take-of-too-many
                              open-v-threefix)))))
  )

;; Extracting the accepted input sequence

(defun round-robin1$in-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (round-robin1$in-act inputs st data-width) t)
          (append (round-robin1$in-seq
                   (cdr inputs-lst)
                   (round-robin1$state-fn inputs st data-width)
                   data-width
                   (1- n))
                  (list (round-robin1$data-in inputs data-width)))
        (round-robin1$in-seq (cdr inputs-lst)
                             (round-robin1$state-fn inputs st data-width)
                             data-width
                             (1- n))))))

;; Extracting the valid output sequence

(defun round-robin1$out-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (round-robin1$out-act inputs st data-width) t)
          (append (round-robin1$out-seq
                   (cdr inputs-lst)
                   (round-robin1$state-fn inputs st data-width)
                   data-width
                   (1- n))
                  (list (round-robin1$data-out st)))
        (round-robin1$out-seq (cdr inputs-lst)
                              (round-robin1$state-fn inputs st data-width)
                              data-width
                              (1- n))))))

;; Input-output sequence simulator

(defund round-robin1$in-out-seq-sim (data-width n state)
  (declare (xargs :guard (and (natp data-width)
                              (natp n))
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals (round-robin1$ins-len data-width))
       ((mv inputs-lst state)
        (signal-vals-gen num-signals n state nil))
       (full '(t))
       (empty '(nil))
       (invalid-data (make-list data-width :initial-element '(x)))
       (la0 empty)
       (a0 invalid-data)
       (lb0 empty)
       (b0 invalid-data)
       (la1 empty)
       (a1 invalid-data)
       (lb1 empty)
       (b1 invalid-data)
       (q2 (list empty invalid-data
                 empty invalid-data))
       (q3 (list empty invalid-data
                 empty invalid-data
                 empty invalid-data))
       (br (list full '(nil)
                 empty '(x)))
       (me (list full '(nil)
                 empty '(x)))
       (st (list la0 a0 lb0 b0 la1 a1 lb1 b1 q2 q3 br me)))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-lst
                   (round-robin1$in-seq inputs-lst st data-width n))))
      (list (cons 'out-seq
                  (v-to-nat-lst
                   (round-robin1$out-seq inputs-lst st data-width n)))))
     state)))

;; The extracted next-state function for RR1

(defund round-robin1$step-spec (inputs st data-width)
  (b* ((data-in (round-robin1$data-in inputs data-width))
       (extracted-st (round-robin1$extract-state st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (round-robin1$out-act inputs st data-width) t)
      (cond
       ((equal (round-robin1$in-act inputs st data-width) t)
        (cons data-in (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (round-robin1$in-act inputs st data-width) t)
          (cons data-in extracted-st))
         (t extracted-st))))))

(local
 (defthm len-0-is-atom
   (equal (equal (len x) 0)
          (atom x))))

(local
 (defthmd cons-append-instances
   (and (equal (cons e (append (queue2$extract-state st)
                               x))
               (append (cons e (queue2$extract-state st))
                       x))
        (equal (cons e (append (queue3$extract-state st)
                               x))
               (append (cons e (queue3$extract-state st))
                       x)))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm consp-queue2$extract-state
     (implies (and (queue2$out-act inputs st data-width)
                   (queue2$valid-st st data-width))
              (consp (queue2$extract-state st)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue2$valid-st
                                 queue2$extract-state
                                 queue2$out-act)))
     :rule-classes :type-prescription))

  (local
   (defthm consp-queue3$extract-state
     (implies (and (queue3$out-act inputs st data-width)
                   (queue3$valid-st st data-width))
              (consp (queue3$extract-state st)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue3$valid-st
                                 queue3$extract-state
                                 queue3$out-act)))
     :rule-classes :type-prescription))

  (local
   (defthm round-robin1$q2-get-$data-in-rewrite
     (b* ((a0 (get-field *round-robin1$a0* st)))
       (implies (and (bvp (strip-cars a0))
                     (equal (len a0) data-width))
                (equal (queue2$data-in
                        (round-robin1$q2-inputs inputs st data-width)
                        data-width)
                       (strip-cars a0))))
     :hints (("Goal"
              :in-theory (enable queue2$data-in
                                 round-robin1$q2-inputs)))))

  (local
   (defthm round-robin1$q3-get-$data-in-rewrite
     (b* ((b0 (get-field *round-robin1$b0* st)))
       (implies (and (bvp (strip-cars b0))
                     (equal (len b0) data-width))
                (equal (queue3$data-in
                        (round-robin1$q3-inputs inputs st data-width)
                        data-width)
                       (strip-cars b0))))
     :hints (("Goal"
              :in-theory (enable queue3$data-in
                                 round-robin1$q3-inputs)))))

  (local
   (defthm queue2$extract-state-singleton
     (implies (and (equal (len (queue2$extract-state st))
                          1)
                   (queue2$valid-st st data-width)
                   (queue2$out-act inputs st data-width))
              (equal (queue2$extract-state st)
                     (list (queue2$data-out st))))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue2$valid-st
                                 queue2$extract-state
                                 queue2$out-act
                                 queue2$data-out)))))

  (local
   (defthm cdr-queue2$extract-state-singleton
     (implies (and (equal (len (queue2$extract-state st))
                          2)
                   (queue2$valid-st st data-width)
                   (queue2$out-act inputs st data-width))
              (equal (cdr (queue2$extract-state st))
                     (list (queue2$data-out st))))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue2$valid-st
                                 queue2$extract-state
                                 queue2$out-act
                                 queue2$data-out)))))

  (local
   (defthm queue3$extract-state-singleton
     (implies (and (equal (len (queue3$extract-state st))
                          1)
                   (queue3$valid-st st data-width)
                   (queue3$out-act inputs st data-width))
              (equal (queue3$extract-state st)
                     (list (queue3$data-out st))))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue3$valid-st
                                 queue3$extract-state
                                 queue3$out-act
                                 queue3$data-out)))))

  (local
   (defthm cdr-queue3$extract-state-singleton
     (implies (and (equal (len (queue3$extract-state st))
                          2)
                   (queue3$valid-st st data-width)
                   (queue3$out-act inputs st data-width))
              (equal (cdr (queue3$extract-state st))
                     (list (queue3$data-out st))))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue3$valid-st
                                 queue3$extract-state
                                 queue3$out-act
                                 queue3$data-out)))))

  (local
   (defthm round-robin1$step-spec-correct-aux-1
     (equal (cons e (append (interleave x y)
                            z))
            (append (interleave (cons e y)
                                x)
                    z))))

  (local
   (defthm round-robin1$step-spec-correct-aux-2
     (equal (cons e (append (cdr (interleave x y))
                            z))
            (append (cons e (cdr (interleave x y)))
                    z))))

  (local
   (defthm round-robin1$step-spec-correct-aux-3
     (implies (consp x)
              (equal (cons (car x)
                           (interleave (queue2$extract-state st)
                                       (cdr x)))
                     (interleave x (queue2$extract-state st))))))

  (local
   (defthm round-robin1$step-spec-correct-aux-4
     (implies (consp x)
              (equal (cons (car x)
                           (interleave (queue3$extract-state st)
                                       (cdr x)))
                     (interleave x (queue3$extract-state st))))))

  (local
   (defthm round-robin1$step-spec-correct-aux-5
     (implies (consp x)
              (equal (cons (car x)
                           (interleave (append y z)
                                       (cdr x)))
                     (interleave x (append y z))))
     :hints (("Goal" :in-theory (disable interleave-append-2)))))

  (defthm round-robin1$step-spec-correct
    (b* ((next-st (round-robin1$state-fn inputs st data-width)))
      (implies (and (round-robin1$input-format inputs data-width)
                    (round-robin1$valid-st st data-width)
                    (round-robin1$inv st))
               (equal (round-robin1$extract-state next-st)
                      (round-robin1$step-spec inputs st data-width))))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              cons-append-instances
                              queue2$step-spec
                              queue3$step-spec
                              round-robin1$step-spec
                              round-robin1$input-format
                              round-robin1$valid-st
                              round-robin1$st-format
                              round-robin1$inv
                              round-robin1$state-fn
                              round-robin1$in-act
                              round-robin1$out-act
                              round-robin1$extract-state
                              round-robin1$br-inputs
                              round-robin1$me-inputs
                              alt-branch$valid-st
                              alt-branch$inv
                              alt-branch$act
                              alt-branch$act0
                              alt-branch$act1
                              alt-merge$valid-st
                              alt-merge$inv
                              alt-merge$state-fn
                              alt-merge$act
                              alt-merge$act0
                              alt-merge$act1)
                             (nfix
                              b-and3
                              b-or3
                              b-not
                              not
                              take-redefinition
                              nthcdr
                              len-nthcdr
                              if*
                              pairlis$
                              strip-cars
                              default-car
                              default-cdr
                              default-+-1
                              default-+-2
                              acl2::append-of-cons)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Proving that round-robin1$valid-st is an invariant.

(encapsulate
  ()

  (local
   (defthm round-robin1$valid-st-preserved-aux
     (b* ((br-inputs (round-robin1$br-inputs inputs st data-width))
          (br (nth *round-robin1$br* st)))
       (implies (not (nth 0 inputs))
                (and (not (alt-branch$act0 br-inputs br data-width))
                     (not (alt-branch$act1 br-inputs br data-width)))))
     :hints (("Goal" :in-theory (enable round-robin1$br-inputs
                                        alt-branch$act0
                                        alt-branch$act1)))))

  (defthm round-robin1$valid-st-preserved
    (implies (and (round-robin1$input-format inputs data-width)
                  (round-robin1$valid-st st data-width))
             (round-robin1$valid-st
              (round-robin1$state-fn inputs st data-width)
              data-width))
    :hints (("Goal"
             :use ((:instance
                    queue2$valid-st-preserved
                    (inputs (round-robin1$q2-inputs inputs st data-width))
                    (st (get-field *round-robin1$q2* st)))
                   (:instance
                    queue3$valid-st-preserved
                    (inputs (round-robin1$q3-inputs inputs st data-width))
                    (st (get-field *round-robin1$q3* st)))
                   (:instance
                    alt-branch$valid-st-preserved
                    (inputs (round-robin1$br-inputs inputs st data-width))
                    (st (get-field *round-robin1$br* st)))
                   (:instance
                    alt-merge$valid-st-preserved
                    (inputs (round-robin1$me-inputs inputs st data-width))
                    (st (get-field *round-robin1$me* st))))
             :in-theory (e/d (get-field
                              round-robin1$input-format
                              round-robin1$valid-st
                              round-robin1$st-format
                              round-robin1$state-fn
                              round-robin1$in-act
                              round-robin1$out-act
                              f-sr)
                             (queue2$valid-st-preserved
                              queue3$valid-st-preserved
                              alt-branch$valid-st-preserved
                              alt-merge$valid-st-preserved
                              if*
                              nfix
                              nthcdr
                              acl2::true-listp-append)))))
  )

(defthm round-robin1$extract-state-lemma
  (implies (and (round-robin1$valid-st st data-width)
                (round-robin1$inv st)
                (equal n (1- (len (round-robin1$extract-state st))))
                (round-robin1$out-act inputs st data-width))
           (equal (append (take n (round-robin1$extract-state st))
                          (list (round-robin1$data-out st)))
                  (round-robin1$extract-state st)))
  :hints (("Goal"
           :do-not-induct t
           :use round-robin1$valid-st=>natp-data-width
           :in-theory (e/d (f-and3
                            cons-append-instances
                            left-associativity-of-append
                            round-robin1$valid-st
                            round-robin1$st-format
                            round-robin1$inv
                            round-robin1$extract-state
                            round-robin1$out-act
                            round-robin1$data-out
                            round-robin1$me-inputs
                            alt-merge$valid-st
                            alt-merge$act
                            alt-merge$act0
                            alt-merge$act1)
                           (nfix
                            b-not
                            nthcdr
                            len-nthcdr
                            if*
                            append
                            pairlis$
                            strip-cars
                            not
                            default-car
                            default-cdr
                            default-+-1
                            default-+-2
                            acl2::append-of-cons
                            acl2::associativity-of-append)))))

(encapsulate
  ()

  (local
   (defthm round-robin1$dataflow-correct-aux
     (implies
      (equal (append x1 y1)
             (append (round-robin1$in-seq inputs-lst st data-width n)
                     y2))
      (equal (append x1 y1 z)
             (append (round-robin1$in-seq inputs-lst st data-width n)
                     y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (acl2::associativity-of-append))))))

  (defthmd round-robin1$dataflow-correct
    (b* ((extracted-st (round-robin1$extract-state st))
         (final-st (round-robin1$state-fn-n inputs-lst st data-width n))
         (final-extracted-st (round-robin1$extract-state final-st)))
      (implies
       (and (round-robin1$input-format-n inputs-lst data-width n)
            (round-robin1$valid-st st data-width)
            (round-robin1$inv st))
       (equal (append final-extracted-st
                      (round-robin1$out-seq inputs-lst st data-width n))
              (append (round-robin1$in-seq inputs-lst st data-width n)
                      extracted-st))))
    :hints (("Goal"
             :in-theory (e/d (round-robin1$step-spec)
                             ()))))
  )

