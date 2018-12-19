;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; November 2018

(in-package "ADE")

(include-book "../branch")
(include-book "../tv-if")
(include-book "../comparators/fast-zero")
(include-book "../comparators/v-equal")

;; ======================================================================

;; DE Module Generator of GCD-COND
;;
;; GCD-COND checks if (A != 0) & (B != 0) & (A != B).

(defconst *gcd-cond$go-num* *branch$go-num*)

(defun gcd-cond$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 3 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun gcd-cond$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (gcd-cond$data-ins-len data-width)
     *gcd-cond$go-num*))

(module-generator
 gcd-cond* (data-width)
 (si 'gcd-cond data-width)
 (list* 'full-in 'empty-out0- 'empty-out1-
        (append (sis 'data-in 0 (* 2 data-width))
                (sis 'go 0 *gcd-cond$go-num*)))
 (list* 'act 'act0 'act1 'flag
        (append (sis 'data0-out 0 data-width)
                (sis 'data1-out 0 (* 2 data-width))))
 ()
 (list
  (list 'a=0?
        '(a=0)
        (si 'fast-zero data-width)
        (sis 'data-in 0 data-width))
  (list 'b=0?
        '(b=0)
        (si 'fast-zero data-width)
        (sis 'data-in data-width data-width))
  (list 'a=b?
        '(a=b)
        (si 'v-equal data-width)
        (append (sis 'data-in 0 data-width)
                (sis 'data-in data-width data-width)))
  '(g0 (flag) b-nor3 (a=0 b=0 a=b))
  (list 'data0-out
        (sis 'data0-out 0 data-width)
        (si 'tv-if (tree-number (make-tree data-width)))
        (cons 'a=0
              (append (sis 'data-in data-width data-width)
                      (sis 'data-in 0 data-width))))
  (list 'br
        (list* 'act 'act0 'act1
               (sis 'data1-out 0 (* 2 data-width)))
        (si 'branch (* 2 data-width))
        (list* 'full-in 'empty-out0- 'empty-out1- 'flag
               (append (sis 'data-in 0 (* 2 data-width))
                       (sis 'go 0 *branch$go-num*)))))
 (declare (xargs :guard (natp data-width))))

;; DE netlist generator.  A generated netlist will contain an instance of
;; GCD-COND.

(defund gcd-cond$netlist (data-width)
  (declare (xargs :guard (and (natp data-width)
                              (<= 2 data-width))))
  (cons (gcd-cond* data-width)
        (union$ (branch$netlist (* 2 data-width))
                (fast-zero$netlist data-width)
                (v-equal$netlist data-width)
                (tv-if$netlist (make-tree data-width))
                :test 'equal)))

;; Recognizer for GCD-COND

(defund gcd-cond& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width)
                              (<= 2 data-width))))
  (b* ((subnetlist (delete-to-eq (si 'gcd-cond data-width) netlist)))
    (and (equal (assoc (si 'gcd-cond data-width) netlist)
                (gcd-cond* data-width))
         (branch& subnetlist (* 2 data-width))
         (fast-zero& subnetlist data-width)
         (v-equal& subnetlist data-width)
         (tv-if& subnetlist (make-tree data-width)))))

;; Sanity check

(local
 (defthmd check-gcd-cond$netlist-64
   (and (net-syntax-okp (gcd-cond$netlist 64))
        (net-arity-okp (gcd-cond$netlist 64))
        (gcd-cond& (gcd-cond$netlist 64) 64))))

;; Extract the input and output signals for GCD-COND

(progn
  ;; Extract the input data

  (defun gcd-cond$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (* 2 (mbe :logic (nfix data-width)
                    :exec  data-width))
          (nthcdr 3 inputs)))

  (defthm len-gcd-cond$data-in
    (equal (len (gcd-cond$data-in inputs data-width))
           (* 2 (nfix data-width))))

  (in-theory (disable gcd-cond$data-in))

  ;; Extract the "flag" signal

  (defund gcd-cond$flag (inputs data-width)
    (b* ((data-in (gcd-cond$data-in inputs data-width))
         (a=0 (f$fast-zero (take data-width data-in)))
         (b=0 (f$fast-zero (nthcdr data-width data-in)))
         (a=b (f$v-equal (take data-width data-in)
                         (nthcdr data-width data-in))))
      (f-nor3 a=0 b=0 a=b)))

  ;; Extract the inputs for the branch joint

  (defund gcd-cond$br-inputs (inputs data-width)
    (b* ((full-in (nth 0 inputs))
         (empty-out0- (nth 1 inputs))
         (empty-out1- (nth 2 inputs))
         (flag (gcd-cond$flag inputs data-width))
         (data-in (gcd-cond$data-in inputs data-width))
         (go-signals (nthcdr (gcd-cond$data-ins-len data-width) inputs)))
      (list* full-in empty-out0- empty-out1- flag
             (append data-in go-signals))))

  ;; Extract the "act0" signal

  (defund gcd-cond$act0 (inputs data-width)
    (branch$act0 (gcd-cond$br-inputs inputs data-width)
                 (* 2 data-width)))

  (defthm gcd-cond$act0-inactive
    (implies (or (not (nth 0 inputs))
                 (equal (nth 1 inputs) t))
             (not (gcd-cond$act0 inputs data-width)))
    :hints (("Goal" :in-theory (enable gcd-cond$br-inputs
                                       gcd-cond$act0))))

  ;; Extract the "act1" signal

  (defund gcd-cond$act1 (inputs data-width)
    (branch$act1 (gcd-cond$br-inputs inputs data-width)
                 (* 2 data-width)))

  (defthm gcd-cond$act1-inactive
    (implies (or (not (nth 0 inputs))
                 (equal (nth 2 inputs) t))
             (not (gcd-cond$act1 inputs data-width)))
    :hints (("Goal" :in-theory (enable gcd-cond$br-inputs
                                       gcd-cond$act1))))

  ;; Extract the "act" signal

  (defund gcd-cond$act (inputs data-width)
    (f-or (gcd-cond$act0 inputs data-width)
          (gcd-cond$act1 inputs data-width)))

  (defthm gcd-cond$act-inactive
    (implies (or (not (nth 0 inputs))
                 (and (equal (nth 1 inputs) t)
                      (equal (nth 2 inputs) t)))
             (not (gcd-cond$act inputs data-width)))
    :hints (("Goal" :in-theory (enable gcd-cond$act))))

  ;; Extract the 1st output data item

  (defund gcd-cond$data0-out (inputs data-width)
    (b* ((data-in (gcd-cond$data-in inputs data-width)))
      (fv-if (f$fast-zero (take data-width data-in))
             (nthcdr data-width data-in)
             (take data-width data-in))))

  (defthm len-gcd-cond$data0-out
    (equal (len (gcd-cond$data0-out inputs data-width))
           (nfix data-width))
    :hints (("Goal" :in-theory (enable gcd-cond$data0-out))))

  (defthm bvp-gcd-cond$data0-out
    (implies (and (natp data-width)
                  (<= 3 data-width)
                  (bvp (gcd-cond$data-in inputs data-width)))
             (bvp (gcd-cond$data0-out inputs data-width)))
    :hints (("Goal" :in-theory (enable gcd-cond$data0-out))))

  ;; Extract the 2nd output data item

  (defund gcd-cond$data1-out (inputs data-width)
    (b* ((data-in (gcd-cond$data-in inputs data-width)))
      (v-threefix data-in)))

  (defthm len-gcd-cond$data1-out
    (equal (len (gcd-cond$data1-out inputs data-width))
           (* 2 (nfix data-width)))
    :hints (("Goal" :in-theory (enable gcd-cond$data1-out))))

  (defthm bvp-gcd-cond$data1-out
    (implies (bvp (gcd-cond$data-in inputs data-width))
             (bvp (gcd-cond$data1-out inputs data-width)))
    :hints (("Goal" :in-theory (enable gcd-cond$data1-out))))
  )

;; The value lemma for GCD-COND

(encapsulate
  ()

  (local
   (defthm list-of-singleton
     (implies (and (true-listp l)
                   (equal (len l) 1))
              (equal (list (car l))
                     l))))

  (defthm gcd-cond$value
    (b* ((inputs (list* full-in empty-out0- empty-out1-
                        (append data-in go-signals))))
      (implies (and (natp data-width)
                    (<= 3 data-width)
                    (gcd-cond& netlist data-width)
                    (true-listp data-in)
                    (equal (len data-in) (* 2 data-width))
                    (true-listp go-signals)
                    (equal (len go-signals) *gcd-cond$go-num*))
               (equal (se (si 'gcd-cond data-width) inputs st netlist)
                      (list*
                       (gcd-cond$act inputs data-width)
                       (gcd-cond$act0 inputs data-width)
                       (gcd-cond$act1 inputs data-width)
                       (gcd-cond$flag inputs data-width)
                       (append (gcd-cond$data0-out inputs data-width)
                               (gcd-cond$data1-out inputs data-width))))))
    :hints (("Goal"
             :do-not-induct t
             :expand (:free (inputs data-width)
                            (se (si 'gcd-cond data-width)
                                inputs st netlist))
             :in-theory (e/d (de-rules
                              gcd-cond&
                              gcd-cond*$destructure
                              branch$act
                              gcd-cond$data-in
                              gcd-cond$br-inputs
                              gcd-cond$act
                              gcd-cond$act0
                              gcd-cond$act1
                              gcd-cond$flag
                              gcd-cond$data0-out
                              gcd-cond$data1-out)
                             (append-take-nthcdr
                              de-module-disabled-rules)))))
  )
