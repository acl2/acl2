;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; April 2019

(in-package "ADE")

(include-book "../link-joint")
(include-book "../tv-if")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of ARB-MERGE
;;; 2. Properties of ARB-MERGE

;; ======================================================================

;; 1. DE Module Generator of ARB-MERGE
;;
;; Construct a DE module generator for a simple first-come-first-served (FCFS)
;; arbitrated merge model using the link-joint model.

;; If two input sources are available at "approximately" the same time, the
;; arbitrated merge will RANDOMLY decide which source to service.  In our
;; modeling, we use an oracle signal "select" to perform random selections when
;; necessary.

(defconst *arb-merge$select-num* 1)
(defconst *arb-merge$go-num* 1)

(defun arb-merge$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 3 (* 2 (mbe :logic (nfix data-size)
                 :exec  data-size))))

(defun arb-merge$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (arb-merge$data-ins-len data-size)
     *arb-merge$select-num*
     *arb-merge$go-num*))

;; DE module generator of ARB-MERGE

(module-generator
 arb-merge* (data-size)
 (si 'arb-merge data-size)
 (list* 'full-in0 'full-in1 'empty-out-
        (append (sis 'data0-in 0 data-size)
                (sis 'data1-in 0 data-size)
                (cons 'select ;; An oracle signal performing random selections
                      (sis 'go 0 *arb-merge$go-num*))))
 (list* 'act 'act0 'act1
        (sis 'data-out 0 data-size))
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
  (list 'arb-merge-cntl0
        '(act0)
        'joint-cntl
        (list 'm-full-in0 'empty-out- (si 'go 0)))
  (list 'arb-merge-cntl1
        '(act1)
        'joint-cntl
        (list 'm-full-in1 'empty-out- (si 'go 0)))
  '(arb-merge-cntl (act) b-or (act0 act1))

  (list 'arb-merge-op
        (sis 'data-out 0 data-size)
        (si 'tv-if (tree-number (make-tree data-size)))
        (cons 'act1
              (append (sis 'data1-in 0 data-size)
                      (sis 'data0-in 0 data-size)))))

 (declare (xargs :guard (natp data-size))))

;; DE netlist generator.  A generated netlist will contain an instance of
;; ARB-MERGE.

(defund arb-merge$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (arb-merge* data-size)
        (union$ *joint-cntl*
                (tv-if$netlist (make-tree data-size))
                :test 'equal)))

;; Recognizer for ARB-MERGE

(defund arb-merge& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'arb-merge data-size) netlist)))
    (and (equal (assoc (si 'arb-merge data-size) netlist)
                (arb-merge* data-size))
         (joint-cntl& subnetlist)
         (tv-if& subnetlist (make-tree data-size)))))

;; Sanity check

(local
 (defthmd check-arb-merge$netlist-64
   (and (net-syntax-okp (arb-merge$netlist 64))
        (net-arity-okp (arb-merge$netlist 64))
        (arb-merge& (arb-merge$netlist 64) 64))))

;; Extract the input and output signals for ARB-MERGE

(progn
  ;; Extract the 1st input data item

  (defun arb-merge$data0-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (mbe :logic (nfix data-size)
               :exec  data-size)
          (nthcdr 3 inputs)))

  (defthm len-arb-merge$data0-in
    (equal (len (arb-merge$data0-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable arb-merge$data0-in))

  ;; Extract the 2nd input data item

  (defun arb-merge$data1-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (b* ((size (mbe :logic (nfix data-size)
                     :exec  data-size)))
      (take size
            (nthcdr (+ 3 size) inputs))))

  (defthm len-arb-merge$data1-in
    (equal (len (arb-merge$data1-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable arb-merge$data1-in))

  ;; Extract the "act0" signal

  (defund arb-merge$act0 (inputs data-size)
    (b* ((full-in0   (nth 0 inputs))
         (full-in1   (nth 1 inputs))
         (empty-out- (nth 2 inputs))
         (select     (nth (arb-merge$data-ins-len data-size) inputs))
         (go-signals (nthcdr (+ (arb-merge$data-ins-len data-size)
                                *arb-merge$select-num*)
                             inputs))

         (b-select (f-bool select))
         (go-arb-merge (nth 0 go-signals))

         (m-full-in0 (f-or (f-and full-in0
                                  (f-not full-in1))
                           (f-and3 full-in0
                                   full-in1
                                   (f-not b-select)))))

      (joint-act m-full-in0 empty-out- go-arb-merge)))

  (defthm arb-merge$act0-inactive
    (implies (or (not (nth 0 inputs))
                 (equal (nth 2 inputs) t))
             (not (arb-merge$act0 inputs data-size)))
    :hints (("Goal" :in-theory (enable f-and3 arb-merge$act0))))

  ;; Extract the "act1" signal

  (defund arb-merge$act1 (inputs data-size)
    (b* ((full-in0   (nth 0 inputs))
         (full-in1   (nth 1 inputs))
         (empty-out- (nth 2 inputs))
         (select     (nth (arb-merge$data-ins-len data-size) inputs))
         (go-signals (nthcdr (+ (arb-merge$data-ins-len data-size)
                                *arb-merge$select-num*)
                             inputs))

         (b-select (f-bool select))
         (go-arb-merge (nth 0 go-signals))

         (m-full-in1 (f-or (f-and (f-not full-in0)
                                  full-in1)
                           (f-and3 full-in0
                                   full-in1
                                   b-select))))

      (joint-act m-full-in1 empty-out- go-arb-merge)))

  (defthm arb-merge$act1-inactive
    (implies (or (not (nth 1 inputs))
                 (equal (nth 2 inputs) t))
             (not (arb-merge$act1 inputs data-size)))
    :hints (("Goal" :in-theory (enable f-and3 arb-merge$act1))))

  (local (in-theory (enable booleanp-car-of-bv)))

  (defthm arb-merge$act-mutually-exclusive
    (implies (and (booleanp (nth 0 inputs))
                  (booleanp (nth 1 inputs))
                  (arb-merge$act0 inputs data-size))
             (not (arb-merge$act1 inputs data-size)))
    :hints (("Goal" :in-theory (enable f-and3
                                       arb-merge$act0
                                       arb-merge$act1))))

  ;; Extract the "act" signal

  (defund arb-merge$act (inputs data-size)
    (f-or (arb-merge$act0 inputs data-size)
          (arb-merge$act1 inputs data-size)))

  (defthm arb-merge$act-inactive
    (implies (or (and (not (nth 0 inputs))
                      (not (nth 1 inputs)))
                 (equal (nth 2 inputs) t))
             (not (arb-merge$act inputs data-size)))
    :hints (("Goal" :in-theory (enable arb-merge$act))))

  ;; Extract the output data

  (defund arb-merge$data-out (inputs data-size)
    (b* ((data0-in (arb-merge$data0-in inputs data-size))
         (data1-in (arb-merge$data1-in inputs data-size))
         (act1 (arb-merge$act1 inputs data-size)))
      (fv-if act1 data1-in data0-in)))

  (defthm len-arb-merge$data-out
    (equal (len (arb-merge$data-out inputs data-size))
           (nfix data-size))
    :hints (("Goal" :in-theory (enable arb-merge$data-out))))
  )

;; The value lemma for ARB-MERGE

(defthm arb-merge$value
  (b* ((inputs (list* full-in0 full-in1 empty-out-
                      (append data0-in data1-in
                              (cons select go-signals)))))
    (implies (and (posp data-size)
                  (arb-merge& netlist data-size)
                  (true-listp data0-in)
                  (equal (len data0-in) data-size)
                  (true-listp data1-in)
                  (equal (len data1-in) data-size))
             (equal (se (si 'arb-merge data-size) inputs st netlist)
                    (list* (arb-merge$act inputs data-size)
                           (arb-merge$act0 inputs data-size)
                           (arb-merge$act1 inputs data-size)
                           (arb-merge$data-out inputs data-size)))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'arb-merge data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            arb-merge&
                            arb-merge*$destructure
                            arb-merge$act
                            arb-merge$act0
                            arb-merge$act1
                            arb-merge$data0-in
                            arb-merge$data1-in
                            arb-merge$data-out)
                           (de-module-disabled-rules)))))

;; ======================================================================

;; 2. Properties of ARB-MERGE

(defthmd arb-merge$random-select
  (b* ((full-in0   (nth 0 inputs))
       (full-in1   (nth 1 inputs))
       (empty-out- (nth 2 inputs))
       (select     (nth (arb-merge$data-ins-len data-size) inputs))
       (go-signals (nthcdr (+ (arb-merge$data-ins-len data-size)
                              *arb-merge$select-num*)
                           inputs))

       (b-select (f-bool select))
       (go-arb-merge (nth 0 go-signals)))
    (implies (and (equal full-in0 t)
                  (equal full-in1 t)
                  (not empty-out-)
                  go-arb-merge)
             (and (equal (arb-merge$act0 inputs data-size)
                         (not b-select))
                  (equal (arb-merge$act1 inputs data-size)
                         b-select))))
  :hints (("Goal" :in-theory (enable joint-act
                                     f-bool
                                     arb-merge$act0
                                     arb-merge$act1))))

(defthmd arb-merge$select-0
  (b* ((full-in0   (nth 0 inputs))
       (full-in1   (nth 1 inputs))
       (empty-out- (nth 2 inputs))
       (go-signals (nthcdr (+ (arb-merge$data-ins-len data-size)
                              *arb-merge$select-num*)
                           inputs))
       (go-arb-merge (nth 0 go-signals)))
    (implies (and (equal full-in0 t)
                  (not full-in1)
                  (not empty-out-)
                  go-arb-merge)
             (equal (arb-merge$act0 inputs data-size)
                    t)))
  :hints (("Goal" :in-theory (enable f-bool
                                     arb-merge$act0))))

(defthmd arb-merge$select-1
  (b* ((full-in0   (nth 0 inputs))
       (full-in1   (nth 1 inputs))
       (empty-out- (nth 2 inputs))
       (go-signals (nthcdr (+ (arb-merge$data-ins-len data-size)
                              *arb-merge$select-num*)
                           inputs))
       (go-arb-merge (nth 0 go-signals)))
    (implies (and (not full-in0)
                  (equal full-in1 t)
                  (not empty-out-)
                  go-arb-merge)
             (equal (arb-merge$act1 inputs data-size)
                    t)))
  :hints (("Goal" :in-theory (enable f-bool
                                     arb-merge$act1))))


