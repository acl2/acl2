;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; March 2019

(in-package "ADE")

(include-book "../merge")
(include-book "../vector-module")
(include-book "../adders/subtractor")
(include-book "../comparators/v-less")

(local (include-book "arithmetic-3/top" :dir :system))

;; ======================================================================

;; DE Module Generator of GCD-BODY
;;
;; GCD-BODY performs the gcd operation in one iteration.

(defconst *gcd-body$go-num* *merge$go-num*)

(defun gcd-body$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (* 2 (mbe :logic (nfix data-size)
                 :exec  data-size))))

(defun gcd-body$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (gcd-body$data-ins-len data-size)
     *gcd-body$go-num*))

(module-generator
 gcd-body* (data-size)
 (si 'gcd-body data-size)
 (list* 'full-in 'empty-out-
        (append (sis 'data-in 0 (* 2 data-size))
                (sis 'go 0 *gcd-body$go-num*)))
 (list* 'act
        (sis 'data-out 0 (* 2 data-size)))
 ()
 (list
  (list 'a<b?
        '(a<b)
        (si 'v-< data-size)
        (append (rev (sis 'data-in 0 data-size))
                (rev (sis 'data-in data-size data-size))))

  (list 'a-b
        (sis 'a-b 0 (1+ data-size))
        (si 'ripple-sub data-size)
        (append (sis 'data-in 0 data-size)
                (sis 'data-in data-size data-size)))
  (list 'out0
        (sis 'data0-out 0 (* 2 data-size))
        (si 'v-buf (* 2 data-size))
        (append (sis 'a-b 0 data-size)
                (sis 'data-in data-size data-size)))
  (list 'b-a
        (sis 'b-a 0 (1+ data-size))
        (si 'ripple-sub data-size)
        (append (sis 'data-in data-size data-size)
                (sis 'data-in 0 data-size)))
  (list 'out1
        (sis 'data1-out 0 (* 2 data-size))
        (si 'v-buf (* 2 data-size))
        (append (sis 'b-a 0 data-size)
                (sis 'data-in 0 data-size)))

  (list 'me
        (list* 'act 'act0 'act1
               (sis 'data-out 0 (* 2 data-size)))
        (si 'merge (* 2 data-size))
        (list* 'full-in 'full-in 'empty-out- 'a<b
               (append (sis 'data0-out 0 (* 2 data-size))
                       (sis 'data1-out 0 (* 2 data-size))
                       (sis 'go 0 *merge$go-num*)))))
 (declare (xargs :guard (natp data-size))))

;; DE netlist generator.  A generated netlist will contain an instance of
;; GCD-BODY.

(defund gcd-body$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (gcd-body* data-size)
        (union$ (merge$netlist (* 2 data-size))
                (v-buf$netlist (* 2 data-size))
                (v-<$netlist data-size)
                (ripple-sub$netlist data-size)
                :test 'equal)))

;; Recognizer for GCD-BODY

(defund gcd-body& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'gcd-body data-size) netlist)))
    (and (equal (assoc (si 'gcd-body data-size) netlist)
                (gcd-body* data-size))
         (merge& subnetlist (* 2 data-size))
         (v-buf& subnetlist (* 2 data-size))
         (v-<& subnetlist data-size)
         (ripple-sub& subnetlist data-size))))

;; Sanity check

(local
 (defthmd check-gcd-body$netlist-64
   (and (net-syntax-okp (gcd-body$netlist 64))
        (net-arity-okp (gcd-body$netlist 64))
        (gcd-body& (gcd-body$netlist 64) 64))))

;; Extract the input and output signals for GCD-BODY

(progn
  ;; Extract the input data

  (defun gcd-body$data-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (* 2 (mbe :logic (nfix data-size)
                    :exec  data-size))
          (nthcdr 2 inputs)))

  (defthm len-gcd-body$data-in
    (equal (len (gcd-body$data-in inputs data-size))
           (* 2 (nfix data-size))))

  (in-theory (disable gcd-body$data-in))

  ;; Extract the "a<b" signal

  (defund gcd-body$a<b (inputs data-size)
    (b* ((data-in (gcd-body$data-in inputs data-size)))
      (fv-< nil t
            (rev (take data-size data-in))
            (rev (nthcdr data-size data-in)))))

  ;; Extract the 1st input data item for the merge

  (defund gcd-body$data0-out (inputs data-size)
    (b* ((data-in (gcd-body$data-in inputs data-size)))
      (v-threefix
       (append (fv-adder-output t
                                (take data-size data-in)
                                (fv-not (nthcdr data-size data-in)))
               (nthcdr data-size data-in)))))

  (defthm len-gcd-body$data0-out
    (equal (len (gcd-body$data0-out inputs data-size))
           (* 2 (nfix data-size)))
    :hints (("Goal" :in-theory (enable gcd-body$data0-out))))

  (defthm bvp-gcd-body$data0-out
    (implies (bvp (gcd-body$data-in inputs data-size))
             (bvp (gcd-body$data0-out inputs data-size)))
    :hints (("Goal" :in-theory (enable gcd-body$data0-out))))

  ;; Extract the 2nd input data item for the merge

  (defund gcd-body$data1-out (inputs data-size)
    (b* ((data-in (gcd-body$data-in inputs data-size)))
      (v-threefix
       (append (fv-adder-output t
                                (nthcdr data-size data-in)
                                (fv-not (take data-size data-in)))
               (take data-size data-in)))))

  (defthm len-gcd-body$data1-out
    (equal (len (gcd-body$data1-out inputs data-size))
           (* 2 (nfix data-size)))
    :hints (("Goal" :in-theory (enable gcd-body$data1-out))))

  (defthm bvp-gcd-body$data1-out
    (implies (bvp (gcd-body$data-in inputs data-size))
             (bvp (gcd-body$data1-out inputs data-size)))
    :hints (("Goal" :in-theory (enable gcd-body$data1-out))))

  ;; Extract the inputs for the merge joint

  (defund gcd-body$me-inputs (inputs data-size)
    (b* ((full-in    (nth 0 inputs))
         (empty-out- (nth 1 inputs))
         (go-signals (nthcdr (gcd-body$data-ins-len data-size) inputs))

         (a<b (gcd-body$a<b inputs data-size))
         (data0-out (gcd-body$data0-out inputs data-size))
         (data1-out (gcd-body$data1-out inputs data-size)))
      (list* full-in full-in empty-out- a<b
             (append data0-out data1-out go-signals))))

  ;; Extract the "act" signal

  (defund gcd-body$act (inputs data-size)
    (merge$act (gcd-body$me-inputs inputs data-size)
               (* 2 data-size)))

  (defthm gcd-body$act-inactive
    (implies (or (not (nth 0 inputs))
                 (equal (nth 1 inputs) t))
             (not (gcd-body$act inputs data-size)))
    :hints (("Goal" :in-theory (enable gcd-body$me-inputs
                                       gcd-body$act))))

  ;; Extract the output data

  (defund gcd-body$data-out (inputs data-size)
    (fv-if (gcd-body$a<b inputs data-size)
           (gcd-body$data1-out inputs data-size)
           (gcd-body$data0-out inputs data-size)))

  (defthm len-gcd-body$data-out
    (equal (len (gcd-body$data-out inputs data-size))
           (* 2 (nfix data-size)))
    :hints (("Goal" :in-theory (enable gcd-body$data-out))))

  (defthm bvp-gcd-body$data-out
    (implies (bvp (gcd-body$data-in inputs data-size))
             (bvp (gcd-body$data-out inputs data-size)))
    :hints (("Goal" :in-theory (enable gcd-body$a<b
                                       gcd-body$data-out))))
  )

;; The value lemma for GCD-BODY

(encapsulate
  ()

  (local
   (defthm list-of-singleton
     (implies (and (true-listp l)
                   (equal (len l) 1))
              (equal (list (car l))
                     l))))

  (defthm gcd-body$value
    (b* ((inputs (list* full-in empty-out-
                        (append data-in go-signals))))
      (implies (and (posp data-size)
                    (gcd-body& netlist data-size)
                    (true-listp data-in)
                    (equal (len data-in) (* 2 data-size))
                    (true-listp go-signals)
                    (equal (len go-signals) *gcd-body$go-num*))
               (equal (se (si 'gcd-body data-size) inputs st netlist)
                      (list* (gcd-body$act inputs data-size)
                             (gcd-body$data-out inputs data-size)))))
    :hints (("Goal"
             :do-not-induct t
             :expand (:free (inputs data-size)
                            (se (si 'gcd-body data-size) inputs st netlist))
             :in-theory (e/d (de-rules
                              fv-adder-output
                              gcd-body&
                              gcd-body*$destructure
                              gcd-body$data-in
                              gcd-body$me-inputs
                              gcd-body$a<b
                              gcd-body$act
                              gcd-body$data-out
                              gcd-body$data0-out
                              gcd-body$data1-out)
                             (append-take-nthcdr
                              de-module-disabled-rules)))))
  )

