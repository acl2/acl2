;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; November 2018

(in-package "ADE")

(include-book "link-joint")
(include-book "tv-if")

(local (include-book "arithmetic-3/top" :dir :system))

;; ======================================================================

;; Construct a DE module generator for a storage-free merge joint.  Prove the
;; value lemma for this module generator.

(defconst *merge$go-num* 1)

(defun merge$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 4 (* 2 (mbe :logic (nfix data-size)
            :exec  data-size))))

(defun merge$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (merge$data-ins-len data-size)
     *merge$go-num*))

;; DE module generator of MERGE

(module-generator
 merge* (data-size)
 (si 'merge data-size)
 (list* 'full-in0 'full-in1 'empty-out- 'select
        (append (sis 'data-in0 0 data-size)
                (sis 'data-in1 0 data-size)
                (sis 'go 0 *merge$go-num*)))
 (list* 'act 'act0 'act1
        (sis 'data-out 0 data-size))
 ()
 (list
  '(g0 (select~) b-not (select))
  '(g1 (ready-in0) b-and (full-in0 select~))
  '(g2 (ready-in1) b-and (full-in1 select))
  (list 'merge-cntl0
        '(act0)
        'joint-cntl
        (list 'ready-in0 'empty-out- (si 'go 0)))
  (list 'merge-cntl1
        '(act1)
        'joint-cntl
        (list 'ready-in1 'empty-out- (si 'go 0)))
  '(merge-cntl (act) b-or (act0 act1))

  (list 'merge-op
        (sis 'data-out 0 data-size)
        (si 'tv-if (tree-number (make-tree data-size)))
        (cons 'select
              (append (sis 'data-in1 0 data-size)
                      (sis 'data-in0 0 data-size)))))

 (declare (xargs :guard (natp data-size))))

;; DE netlist generator.  A generated netlist will contain an instance of
;; MERGE.

(defund merge$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (merge* data-size)
        (union$ (tv-if$netlist (make-tree data-size))
                *joint-cntl*
                :test 'equal)))

;; Recognizer for MERGE

(defund merge& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'merge data-size) netlist)))
    (and (equal (assoc (si 'merge data-size) netlist)
                (merge* data-size))
         (joint-cntl& subnetlist)
         (tv-if& subnetlist (make-tree data-size)))))

;; Sanity check

(local
 (defthmd check-merge$netlist-64
   (and (net-syntax-okp (merge$netlist 64))
        (net-arity-okp (merge$netlist 64))
        (merge& (merge$netlist 64) 64))))

;; Extract the input and output signals for MERGE

(progn
  ;; Extract the 1st input data item

  (defun merge$data-in0 (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (mbe :logic (nfix data-size)
               :exec  data-size)
          (nthcdr 4 inputs)))

  (defthm len-merge$data-in0
    (equal (len (merge$data-in0 inputs data-size))
           (nfix data-size)))

  (in-theory (disable merge$data-in0))

  ;; Extract the 2nd input data item

  (defun merge$data-in1 (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (b* ((size (mbe :logic (nfix data-size)
                     :exec  data-size)))
      (take size
            (nthcdr (+ 4 size) inputs))))

  (defthm len-merge$data-in1
    (equal (len (merge$data-in1 inputs data-size))
           (nfix data-size)))

  (in-theory (disable merge$data-in1))

  ;; Extract the "act0" signal

  (defund merge$act0 (inputs data-size)
    (b* ((full-in0   (nth 0 inputs))
         (empty-out- (nth 2 inputs))
         (select     (nth 3 inputs))
         (go-signals (nthcdr (merge$data-ins-len data-size) inputs))

         (go-merge (nth 0 go-signals))

         (ready-in0 (f-and full-in0 (f-not select))))

      (joint-act ready-in0 empty-out- go-merge)))

  (defthm merge$act0-inactive
    (implies (or (not (nth 0 inputs))
                 (equal (nth 2 inputs) t))
             (not (merge$act0 inputs data-size)))
    :hints (("Goal" :in-theory (enable merge$act0))))

  ;; Extract the "act1" signal

  (defund merge$act1 (inputs data-size)
    (b* ((full-in1   (nth 1 inputs))
         (empty-out- (nth 2 inputs))
         (select     (nth 3 inputs))
         (go-signals (nthcdr (merge$data-ins-len data-size) inputs))

         (go-merge (nth 0 go-signals))

         (ready-in1 (f-and full-in1 select)))

      (joint-act ready-in1 empty-out- go-merge)))

  (defthm merge$act1-inactive
    (implies (or (not (nth 1 inputs))
                 (equal (nth 2 inputs) t))
             (not (merge$act1 inputs data-size)))
    :hints (("Goal" :in-theory (enable merge$act1))))

  ;; Extract the "act" signal

  (defund merge$act (inputs data-size)
    (f-or (merge$act0 inputs data-size)
          (merge$act1 inputs data-size)))

  (defthm merge$act-inactive
    (implies (or (and (not (nth 0 inputs))
                      (not (nth 1 inputs)))
                 (equal (nth 2 inputs) t))
             (not (merge$act inputs data-size)))
    :hints (("Goal" :in-theory (enable merge$act))))
  )

;; The value lemma for MERGE

(defthm merge$value
  (b* ((inputs (list* full-in0 full-in1 empty-out- select
                      (append data-in0 data-in1 go-signals))))
    (implies (and (posp data-size)
                  (merge& netlist data-size)
                  (true-listp data-in0)
                  (equal (len data-in0) data-size)
                  (true-listp data-in1)
                  (equal (len data-in1) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *merge$go-num*))
             (equal (se (si 'merge data-size) inputs st netlist)
                    (list* (merge$act inputs data-size)
                           (merge$act0 inputs data-size)
                           (merge$act1 inputs data-size)
                           (fv-if select data-in1 data-in0)))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'merge data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            merge&
                            merge*$destructure
                            merge$act
                            merge$act0
                            merge$act1)
                           (de-module-disabled-rules)))))

