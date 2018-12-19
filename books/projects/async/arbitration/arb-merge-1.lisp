;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; November 2018

(in-package "ADE")

(include-book "../link-joint")
(include-book "../tv-if")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of ARB-MERGE-1
;;; 2. Some Properties of ARB-MERGE-1

;; ======================================================================

;; 1. DE Module Generator of ARB-MERGE-1
;;
;; Construct a DE module generator for a simple first-come-first-served (FCFS)
;; arbitrated merge model using the link-joint model.

;; If two input sources are available at "approximately" the same time, the
;; arbitrated merge will RANDOMLY decide which source to service.  In our
;; modeling, we use an oracle signal "select" to perform random selections when
;; necessary.

(defconst *arb-merge-1$select-num* 1)
(defconst *arb-merge-1$go-num* 1)

(defun arb-merge-1$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 3 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun arb-merge-1$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (arb-merge-1$data-ins-len data-width)
     *arb-merge-1$select-num*
     *arb-merge-1$go-num*))

;; DE module generator of ARB-MERGE-1

(module-generator
 arb-merge-1* (data-width)
 (si 'arb-merge-1 data-width)
 (list* 'full-in0 'full-in1 'empty-out-
        (append (sis 'data0-in 0 data-width)
                (sis 'data1-in 0 data-width)
                (cons 'select ;; An oracle signal performing random selections
                      (sis 'go 0 *arb-merge-1$go-num*))))
 (list* 'act 'act0 'act1
        (sis 'data-out 0 data-width))
 ()
 (list
  '(g0 (b-select) b-bool (select))
  '(g1 (b-select~) b-not (b-select))
  '(g2 (empty-in0-) b-not (full-in0))
  '(g3 (empty-in1-) b-not (full-in1))

  '(h0 (m-full-in0-1) b-and (full-in0 empty-in1-))
  '(h1 (m-full-in0-2) b-and3 (full-in0 full-in1 b-select~))
  '(h2 (m-full-in0) b-or (m-full-in0-1 m-full-in0-2))

  '(h3 (m-full-in1-1) b-and (empty-in0- full-in1))
  '(h4 (m-full-in1-2) b-and3 (full-in0 full-in1 b-select))
  '(h5 (m-full-in1) b-or (m-full-in1-1 m-full-in1-2))
  (list 'arb-merge-1-cntl0
        '(act0)
        'joint-cntl
        (list 'm-full-in0 'empty-out- (si 'go 0)))
  (list 'arb-merge-1-cntl1
        '(act1)
        'joint-cntl
        (list 'm-full-in1 'empty-out- (si 'go 0)))
  '(arb-merge-1-cntl (act) b-or (act0 act1))

  (list 'arb-merge-1-op
        (sis 'data-out 0 data-width)
        (si 'tv-if (tree-number (make-tree data-width)))
        (cons 'act1
              (append (sis 'data1-in 0 data-width)
                      (sis 'data0-in 0 data-width)))))

 (declare (xargs :guard (natp data-width))))

;; DE netlist generator.  A generated netlist will contain an instance of
;; ARB-MERGE-1.

(defund arb-merge-1$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (arb-merge-1* data-width)
        (union$ *joint-cntl*
                (tv-if$netlist (make-tree data-width))
                :test 'equal)))

;; Recognizer for ARB-MERGE-1

(defund arb-merge-1& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (b* ((subnetlist (delete-to-eq (si 'arb-merge-1 data-width) netlist)))
    (and (equal (assoc (si 'arb-merge-1 data-width) netlist)
                (arb-merge-1* data-width))
         (joint-cntl& subnetlist)
         (tv-if& subnetlist (make-tree data-width)))))

;; Sanity check

(local
 (defthmd check-arb-merge-1$netlist-64
   (and (net-syntax-okp (arb-merge-1$netlist 64))
        (net-arity-okp (arb-merge-1$netlist 64))
        (arb-merge-1& (arb-merge-1$netlist 64) 64))))

;; Extract the input and output signals for ARB-MERGE-1

(progn
  ;; Extract the 1st input data item

  (defun arb-merge-1$data0-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 3 inputs)))

  (defthm len-arb-merge-1$data0-in
    (equal (len (arb-merge-1$data0-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable arb-merge-1$data0-in))

  ;; Extract the 2nd input data item

  (defun arb-merge-1$data1-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (b* ((width (mbe :logic (nfix data-width)
                     :exec  data-width)))
      (take width
            (nthcdr (+ 3 width) inputs))))

  (defthm len-arb-merge-1$data1-in
    (equal (len (arb-merge-1$data1-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable arb-merge-1$data1-in))

  ;; Extract the "act0" signal

  (defund arb-merge-1$act0 (inputs data-width)
    (b* ((full-in0   (nth 0 inputs))
         (full-in1   (nth 1 inputs))
         (empty-out- (nth 2 inputs))
         (select     (nth (arb-merge-1$data-ins-len data-width) inputs))
         (go-signals (nthcdr (+ (arb-merge-1$data-ins-len data-width)
                                *arb-merge-1$select-num*)
                             inputs))

         (b-select (f-bool select))
         (go-arb-merge-1 (nth 0 go-signals))

         (m-full-in0 (f-or (f-and full-in0
                                  (f-not full-in1))
                           (f-and3 full-in0
                                   full-in1
                                   (f-not b-select)))))

      (joint-act m-full-in0 empty-out- go-arb-merge-1)))

  (defthm arb-merge-1$act0-inactive
    (implies (or (not (nth 0 inputs))
                 (equal (nth 2 inputs) t))
             (not (arb-merge-1$act0 inputs data-width)))
    :hints (("Goal" :in-theory (enable f-and3 arb-merge-1$act0))))

  ;; Extract the "act1" signal

  (defund arb-merge-1$act1 (inputs data-width)
    (b* ((full-in0   (nth 0 inputs))
         (full-in1   (nth 1 inputs))
         (empty-out- (nth 2 inputs))
         (select     (nth (arb-merge-1$data-ins-len data-width) inputs))
         (go-signals (nthcdr (+ (arb-merge-1$data-ins-len data-width)
                                *arb-merge-1$select-num*)
                             inputs))

         (b-select (f-bool select))
         (go-arb-merge-1 (nth 0 go-signals))

         (m-full-in1 (f-or (f-and (f-not full-in0)
                                  full-in1)
                           (f-and3 full-in0
                                   full-in1
                                   b-select))))

      (joint-act m-full-in1 empty-out- go-arb-merge-1)))

  (defthm arb-merge-1$act1-inactive
    (implies (or (not (nth 1 inputs))
                 (equal (nth 2 inputs) t))
             (not (arb-merge-1$act1 inputs data-width)))
    :hints (("Goal" :in-theory (enable f-and3 arb-merge-1$act1))))

  (local (in-theory (enable booleanp-car-of-bv)))

  (defthm arb-merge-1$act-mutually-exclusive
    (implies (and (booleanp (nth 0 inputs))
                  (booleanp (nth 1 inputs))
                  (arb-merge-1$act0 inputs data-width))
             (not (arb-merge-1$act1 inputs data-width)))
    :hints (("Goal" :in-theory (enable f-and3
                                       arb-merge-1$act0
                                       arb-merge-1$act1))))

  ;; Extract the "act" signal

  (defund arb-merge-1$act (inputs data-width)
    (f-or (arb-merge-1$act0 inputs data-width)
          (arb-merge-1$act1 inputs data-width)))

  (defthm arb-merge-1$act-inactive
    (implies (or (and (not (nth 0 inputs))
                      (not (nth 1 inputs)))
                 (equal (nth 2 inputs) t))
             (not (arb-merge-1$act inputs data-width)))
    :hints (("Goal" :in-theory (enable arb-merge-1$act))))

  ;; Extract the output data

  (defund arb-merge-1$data-out (inputs data-width)
    (b* ((data0-in (arb-merge-1$data0-in inputs data-width))
         (data1-in (arb-merge-1$data1-in inputs data-width))
         (act1 (arb-merge-1$act1 inputs data-width)))
      (fv-if act1 data1-in data0-in)))

  (defthm len-arb-merge-1$data-out
    (equal (len (arb-merge-1$data-out inputs data-width))
           (nfix data-width))
    :hints (("Goal" :in-theory (enable arb-merge-1$data-out))))
  )

;; The value lemma for ARB-MERGE-1

(defthm arb-merge-1$value
  (b* ((inputs (list* full-in0 full-in1 empty-out-
                      (append data0-in data1-in
                              (cons select go-signals)))))
    (implies (and (posp data-width)
                  (arb-merge-1& netlist data-width)
                  (true-listp data0-in)
                  (equal (len data0-in) data-width)
                  (true-listp data1-in)
                  (equal (len data1-in) data-width))
             (equal (se (si 'arb-merge-1 data-width) inputs st netlist)
                    (list* (arb-merge-1$act inputs data-width)
                           (arb-merge-1$act0 inputs data-width)
                           (arb-merge-1$act1 inputs data-width)
                           (arb-merge-1$data-out inputs data-width)))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'arb-merge-1 data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            arb-merge-1&
                            arb-merge-1*$destructure
                            arb-merge-1$act
                            arb-merge-1$act0
                            arb-merge-1$act1
                            arb-merge-1$data0-in
                            arb-merge-1$data1-in
                            arb-merge-1$data-out)
                           (de-module-disabled-rules)))))

;; ======================================================================

;; 2. Some Properties of ARB-MERGE-1

(defthmd arb-merge-1$random-select
  (b* ((full-in0   (nth 0 inputs))
       (full-in1   (nth 1 inputs))
       (empty-out- (nth 2 inputs))
       (select     (nth (arb-merge-1$data-ins-len data-width) inputs))
       (go-signals (nthcdr (+ (arb-merge-1$data-ins-len data-width)
                              *arb-merge-1$select-num*)
                           inputs))

       (b-select (f-bool select))
       (go-arb-merge-1 (nth 0 go-signals)))
    (implies (and (equal full-in0 t)
                  (equal full-in1 t)
                  (not empty-out-)
                  go-arb-merge-1)
             (and (equal (arb-merge-1$act0 inputs data-width)
                         (not b-select))
                  (equal (arb-merge-1$act1 inputs data-width)
                         b-select))))
  :hints (("Goal" :in-theory (enable joint-act
                                     f-bool
                                     arb-merge-1$act0
                                     arb-merge-1$act1))))

(defthmd arb-merge-1$select-0
  (b* ((full-in0   (nth 0 inputs))
       (full-in1   (nth 1 inputs))
       (empty-out- (nth 2 inputs))
       (go-signals (nthcdr (+ (arb-merge-1$data-ins-len data-width)
                              *arb-merge-1$select-num*)
                           inputs))
       (go-arb-merge-1 (nth 0 go-signals)))
    (implies (and (equal full-in0 t)
                  (not full-in1)
                  (not empty-out-)
                  go-arb-merge-1)
             (equal (arb-merge-1$act0 inputs data-width)
                    t)))
  :hints (("Goal" :in-theory (enable f-bool
                                     arb-merge-1$act0))))

(defthmd arb-merge-1$select-1
  (b* ((full-in0   (nth 0 inputs))
       (full-in1   (nth 1 inputs))
       (empty-out- (nth 2 inputs))
       (go-signals (nthcdr (+ (arb-merge-1$data-ins-len data-width)
                              *arb-merge-1$select-num*)
                           inputs))
       (go-arb-merge-1 (nth 0 go-signals)))
    (implies (and (not full-in0)
                  (equal full-in1 t)
                  (not empty-out-)
                  go-arb-merge-1)
             (equal (arb-merge-1$act1 inputs data-width)
                    t)))
  :hints (("Goal" :in-theory (enable f-bool
                                     arb-merge-1$act1))))


