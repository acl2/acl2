;; Copyright (C) 2019, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "../link-joint")
(include-book "../vector-module")

(local (in-theory (disable nth)))

;; ======================================================================

;; Construct a DE module generator for a Telescope joint.  Prove the value and
;; state lemmas for this module generator.

(defconst *telescope$go-num* 1)

(defun telescope$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (mbe :logic (nfix data-size)
            :exec  data-size)))

(defun telescope$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (telescope$data-ins-len data-size)
     *telescope$go-num*))

;; DE module generator of Telescope

(module-generator
 telescope* (data-size)
 ;; MODULE'S NAME
 (si 'telescope data-size)
 ;; INPUTS
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 data-size)
                                     (sis 'go 0 *telescope$go-num*)))
 ;; OUTPUTS
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-size))
 ;; INTERNAL STATE
 '(x)
 ;; OCCURRENCES
 (list
  ;; LINK
  ;; X
  '(x (x-status) link-cntl (out-act in-act))

  ;; JOINT
  ;; Telescope
  '(g0 (x-full-in) b-and (x-status full-in))
  '(g1 (x-empty-out-) b-or (x-status empty-out-))
  (list 'in-cntl
        '(in-act)
        'joint-cntl
        (list 'x-full-in 'empty-out- (si 'go 0)))
  (list 'out-cntl
        '(out-act)
        'joint-cntl
        (list 'full-in 'x-empty-out- (si 'go 0)))
  (list 'op
        (sis 'data-out 0 data-size)
        (si 'v-buf data-size)
        (sis 'data-in 0 data-size)))

 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'telescope '(x) 0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; Telescope.

(defund telescope$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (telescope* data-size)
        (union$ *joint-cntl*
                (v-buf$netlist data-size)
                :test 'equal)))

;; Recognizer for Telescope

(defund telescope& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'telescope data-size) netlist)))
    (and (equal (assoc (si 'telescope data-size) netlist)
                (telescope* data-size))
         (joint-cntl& subnetlist)
         (v-buf& subnetlist data-size))))

;; Sanity check

(local
 (defthmd check-telescope$netlist-64
   (and (net-syntax-okp (telescope$netlist 64))
        (net-arity-okp (telescope$netlist 64))
        (telescope& (telescope$netlist 64) 64))))

;; Constraints on the state of Telescope

(defund telescope$valid-st (st)
  (b* ((x (nth *telescope$x* st)))
    (validp x))) ;; The link status is either full or empty.

;; Extract the input and output signals for Telescope

(progn
  ;; Extract the input data

  (defun telescope$data-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (mbe :logic (nfix data-size)
               :exec  data-size)
          (nthcdr 2 inputs)))

  (defthm len-telescope$data-in
    (equal (len (telescope$data-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable telescope$data-in))

  ;; Extract the "in-act" signal

  (defund telescope$in-act (inputs st data-size)
    (b* ((full-in    (nth 0 inputs))
         (empty-out- (nth 1 inputs))
         (go-signals (nthcdr (telescope$data-ins-len data-size) inputs))

         (go (nth 0 go-signals))

         (x (nth *telescope$x* st))

         (x-full-in (f-and (car x) full-in)))
      (joint-act x-full-in empty-out- go)))

  (defthm telescope$in-act-inactive
    (implies (or (not (nth 0 inputs))
                 (equal (nth 1 inputs) t))
             (not (telescope$in-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable telescope$in-act))))

  ;; Extract the "out-act" signal

  (defund telescope$out-act (inputs st data-size)
    (b* ((full-in    (nth 0 inputs))
         (empty-out- (nth 1 inputs))
         (go-signals (nthcdr (telescope$data-ins-len data-size) inputs))

         (go (nth 0 go-signals))

         (x (nth *telescope$x* st))

         (x-empty-out- (f-or (car x) empty-out-)))
      (joint-act full-in x-empty-out- go)))

  (defthm telescope$out-act-inactive
    (implies (or (not (nth 0 inputs))
                 (equal (nth 1 inputs) t))
             (not (telescope$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable telescope$out-act))))

  ;; Extract the output data

  (defund telescope$data-out (inputs data-size)
    (v-threefix (telescope$data-in inputs data-size)))

  (defthm len-telescope$data-out
    (equal (len (telescope$data-out inputs data-size))
           (nfix data-size))
    :hints (("Goal" :in-theory (enable telescope$data-out))))

  (defthm bvp-telescope$data-out
    (implies (bvp (telescope$data-in inputs data-size))
             (bvp (telescope$data-out inputs data-size)))
    :hints (("Goal" :in-theory (enable telescope$data-out))))

  (defun telescope$outputs (inputs st data-size)
    (list* (telescope$in-act inputs st data-size)
           (telescope$out-act inputs st data-size)
           (telescope$data-out inputs data-size)))
  )

;; The value lemma for Telescope

(defthm telescope$value
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (telescope& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *telescope$go-num*))
             (equal (se (si 'telescope data-size) inputs st netlist)
                    (telescope$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'telescope data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            telescope&
                            telescope*$destructure
                            telescope$data-in
                            telescope$in-act
                            telescope$out-act
                            telescope$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of Telescope.

(defun telescope$step (inputs st data-size)
  (b* ((in-act (telescope$in-act inputs st data-size))
       (out-act (telescope$out-act inputs st data-size))

       (x (nth *telescope$x* st)))
    (list (list (f-sr out-act in-act (car x))))))

;; The state lemma for Telescope

(defthm telescope$state
  (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
    (implies (and (telescope& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *telescope$go-num*))
             (equal (de (si 'telescope data-size) inputs st netlist)
                    (telescope$step inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'telescope data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            telescope&
                            telescope*$destructure
                            telescope$in-act
                            telescope$out-act)
                           (de-module-disabled-rules)))))

(in-theory (disable telescope$step))

;; ======================================================================

;; Conditions on the inputs

(defund telescope$input-format (inputs data-size)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-size))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (telescope$data-in inputs data-size))
       (go-signals (nthcdr (telescope$data-ins-len data-size) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *telescope$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

(defthm booleanp-telescope$in-act
  (implies (and (telescope$input-format inputs data-size)
                (telescope$valid-st st))
           (booleanp (telescope$in-act inputs st data-size)))
  :hints (("Goal" :in-theory (enable telescope$input-format
                                     telescope$valid-st
                                     telescope$in-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-telescope$out-act
  (implies (and (telescope$input-format inputs data-size)
                (telescope$valid-st st))
           (booleanp (telescope$out-act inputs st data-size)))
  :hints (("Goal" :in-theory (enable telescope$input-format
                                     telescope$valid-st
                                     telescope$out-act)))
  :rule-classes (:rewrite :type-prescription))

(defthm telescope$valid-st-preserved
  (implies (and (telescope$input-format inputs data-size)
                (telescope$valid-st st))
           (telescope$valid-st
            (telescope$step inputs st data-size)))
  :hints (("Goal" :in-theory (enable f-sr
                                     telescope$input-format
                                     telescope$valid-st
                                     telescope$step
                                     telescope$in-act
                                     telescope$out-act))))



