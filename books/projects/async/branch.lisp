;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; November 2018

(in-package "ADE")

(include-book "link-joint")
(include-book "vector-module")

;; ======================================================================

;; Construct a DE module generator for a storage-free branch joint.  Prove the
;; value lemma for this module generator.

(defconst *branch$go-num* 1)

(defun branch$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 4 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun branch$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (branch$data-ins-len data-width)
     *branch$go-num*))

;; DE module generator of BRANCH

(module-generator
 branch* (data-width)
 (si 'branch data-width)
 (list* 'full-in 'empty-out0- 'empty-out1- 'select
        (append (sis 'data-in 0 data-width)
                (sis 'go 0 *branch$go-num*)))
 (list* 'act 'act0 'act1
        (sis 'data-out 0 data-width))
 ()
 (list
  '(g0 (select~) b-not (select))
  '(g1 (ready-out0-) b-or (empty-out0- select))
  '(g2 (ready-out1-) b-or (empty-out1- select~))
  (list 'branch-cntl0
        '(act0)
        'joint-cntl
        (list 'full-in 'ready-out0- (si 'go 0)))
  (list 'branch-cntl1
        '(act1)
        'joint-cntl
        (list 'full-in 'ready-out1- (si 'go 0)))
  '(branch-cntl (act) b-or (act0 act1))

  (list 'branch-op
        (sis 'data-out 0 data-width)
        (si 'v-buf data-width)
        (sis 'data-in 0 data-width)))

 (declare (xargs :guard (natp data-width))))

;; DE netlist generator.  A generated netlist will contain an instance of
;; BRANCH.

(defund branch$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (branch* data-width)
        (union$ (v-buf$netlist data-width)
                *joint-cntl*
                :test 'equal)))

;; Recognizer for BRANCH

(defund branch& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (b* ((subnetlist (delete-to-eq (si 'branch data-width) netlist)))
    (and (equal (assoc (si 'branch data-width) netlist)
                (branch* data-width))
         (joint-cntl& subnetlist)
         (v-buf& subnetlist data-width))))

;; Sanity check

(local
 (defthmd check-branch$netlist-64
   (and (net-syntax-okp (branch$netlist 64))
        (net-arity-okp (branch$netlist 64))
        (branch& (branch$netlist 64) 64))))

;; Extract the input and output signals for BRANCH

(progn
  ;; Extract the input data

  (defun branch$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 4 inputs)))

  (defthm len-branch$data-in
    (equal (len (branch$data-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable branch$data-in))

  ;; Extract the "act0" signal

  (defund branch$act0 (inputs data-width)
    (b* ((full-in     (nth 0 inputs))
         (empty-out0- (nth 1 inputs))
         (select      (nth 3 inputs))
         (go-signals  (nthcdr (branch$data-ins-len data-width) inputs))

         (go-branch (nth 0 go-signals))

         (ready-out0- (f-or empty-out0- select)))

      (joint-act full-in ready-out0- go-branch)))

  (defthm branch$act0-inactive
    (implies (or (not (nth 0 inputs))
                 (equal (nth 1 inputs) t))
             (not (branch$act0 inputs data-width)))
    :hints (("Goal" :in-theory (enable branch$act0))))

  ;; Extract the "act1" signal

  (defund branch$act1 (inputs data-width)
    (b* ((full-in     (nth 0 inputs))
         (empty-out1- (nth 2 inputs))
         (select      (nth 3 inputs))
         (go-signals  (nthcdr (branch$data-ins-len data-width) inputs))

         (go-branch (nth 0 go-signals))

         (ready-out1- (f-or empty-out1- (f-not select))))

      (joint-act full-in ready-out1- go-branch)))

  (defthm branch$act1-inactive
    (implies (or (not (nth 0 inputs))
                 (equal (nth 2 inputs) t))
             (not (branch$act1 inputs data-width)))
    :hints (("Goal" :in-theory (enable branch$act1))))

  ;; Extract the "act" signal

  (defund branch$act (inputs data-width)
    (f-or (branch$act0 inputs data-width)
          (branch$act1 inputs data-width)))

  (defthm branch$act-inactive
    (implies (or (not (nth 0 inputs))
                 (and (equal (nth 1 inputs) t)
                      (equal (nth 2 inputs) t)))
             (not (branch$act inputs data-width)))
    :hints (("Goal" :in-theory (enable branch$act))))
  )

;; The value lemma for BRANCH

(defthm branch$value
  (b* ((inputs (list* full-in empty-out0- empty-out1- select
                      (append data-in go-signals))))
    (implies (and (branch& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *branch$go-num*))
             (equal (se (si 'branch data-width) inputs st netlist)
                    (list* (branch$act inputs data-width)
                           (branch$act0 inputs data-width)
                           (branch$act1 inputs data-width)
                           (v-threefix data-in)))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'branch data-width) inputs st netlist))
           :in-theory (e/d (de-rules
                            branch&
                            branch*$destructure
                            branch$act
                            branch$act0
                            branch$act1)
                           (de-module-disabled-rules)))))


