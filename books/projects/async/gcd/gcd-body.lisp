;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; April 2018

(in-package "ADE")

(include-book "../merge")
(include-book "../vector-module")
(include-book "../adders/add-sub")
(include-book "../comparators/v-less")

(local (in-theory (disable nth)))

;; ======================================================================

;; DE Module Generator of GCD-BODY
;;
;; GCD-BODY performs the gcd operation in one iteration.

(defconst *gcd-body$go-num* 1)

(defun gcd-body$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun gcd-body$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (gcd-body$data-ins-len data-width)
     *gcd-body$go-num*))

(module-generator
 gcd-body* (data-width)
 (si 'gcd-body data-width)
 (list* 'full-in 'empty-out-
        (append (sis 'data-in 0 (* 2 data-width))
                (sis 'go 0 *gcd-body$go-num*)))
 (list* 'act 'act0 'act1
        (sis 'data-out 0 (* 2 data-width)))
 ()
 (list
  (list 'a<b?
        '(a<b)
        (si 'v-< data-width)
        (append (rev (sis 'data-in 0 data-width))
                (rev (sis 'data-in data-width data-width))))

  '(g0 (high) vdd ())
  (list 'a-b
        (sis 'a-b 0 (1+ data-width))
        (si 'ripple-add/sub data-width)
        (cons 'high
              (append (sis 'data-in 0 data-width)
                      (sis 'data-in data-width data-width))))
  (list 'out0
        (sis 'data-out0 0 (* 2 data-width))
        (si 'v-buf (* 2 data-width))
        (append (sis 'a-b 0 data-width)
                (sis 'data-in data-width data-width)))
  (list 'b-a
        (sis 'b-a 0 (1+ data-width))
        (si 'ripple-add/sub data-width)
        (cons 'high
              (append (sis 'data-in data-width data-width)
                      (sis 'data-in 0 data-width))))
  (list 'out1
        (sis 'data-out1 0 (* 2 data-width))
        (si 'v-buf (* 2 data-width))
        (append (sis 'data-in 0 data-width)
                (sis 'b-a 0 data-width)))

  (list 'me
        (list* 'act 'act0 'act1
               (sis 'data-out 0 (* 2 data-width)))
        (si 'merge (* 2 data-width))
        (list* 'full-in 'full-in 'empty-out- 'a<b
               (append (sis 'data-out0 0 (* 2 data-width))
                       (sis 'data-out1 0 (* 2 data-width))
                       (sis 'go 0 *merge$go-num*)))))
 :guard (natp data-width))

;; DE netlist generator.  A generated netlist will contain an instance of
;; GCD-BODY.

(defun gcd-body$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (gcd-body* data-width)
        (union$ (merge$netlist (* 2 data-width))
                (v-buf$netlist (* 2 data-width))
                (v-<$netlist data-width)
                (ripple-add/sub$netlist data-width)
                :test 'equal)))

;; Recognizer for GCD-BODY

(defund gcd-body& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (and (equal (assoc (si 'gcd-body data-width) netlist)
              (gcd-body* data-width))
       (b* ((netlist (delete-to-eq (si 'gcd-body data-width) netlist)))
         (and (merge& netlist (* 2 data-width))
              (v-buf& netlist (* 2 data-width))
              (v-<& netlist data-width)
              (ripple-add/sub& netlist data-width)))))

;; Sanity check

(local
 (defthmd check-gcd-body$netlist-64
   (and (net-syntax-okp (gcd-body$netlist 64))
        (net-arity-okp (gcd-body$netlist 64))
        (gcd-body& (gcd-body$netlist 64) 64))))

;; Extract the input and output signals from GCD-BODY

(progn
  ;; Extract the input data

  (defun gcd-body$data-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (* 2 (mbe :logic (nfix data-width)
                    :exec  data-width))
          (nthcdr 2 inputs)))

  (defthm len-gcd-body$data-in
    (equal (len (gcd-body$data-in inputs data-width))
           (* 2 (nfix data-width))))

  (in-theory (disable gcd-body$data-in))

  ;; Extract the "a<b" signal

  (defund gcd-body$a<b (inputs data-width)
    (b* ((data-in (gcd-body$data-in inputs data-width)))
      (fv-< nil t
            (rev (take data-width data-in))
            (rev (nthcdr data-width data-in)))))

  ;; Extract the 1st input data item for the merge

  (defund gcd-body$data-out0 (inputs data-width)
    (b* ((data-in (gcd-body$data-in inputs data-width)))
      (v-threefix
       (append (take data-width
                     (fv-adder t
                               (take data-width data-in)
                               (fv-not (nthcdr data-width data-in))))
               (nthcdr data-width data-in)))))

  (defthm len-gcd-body$data-out0
    (equal (len (gcd-body$data-out0 inputs data-width))
           (* 2 (nfix data-width)))
    :hints (("Goal" :in-theory (enable gcd-body$data-out0))))

  (defthm bvp-gcd-body$data-out0
    (implies (bvp (gcd-body$data-in inputs data-width))
             (bvp (gcd-body$data-out0 inputs data-width)))
    :hints (("Goal" :in-theory (enable gcd-body$data-out0))))

  ;; Extract the 2nd input data item for the merge

  (defund gcd-body$data-out1 (inputs data-width)
    (b* ((data-in (gcd-body$data-in inputs data-width)))
      (v-threefix
       (append (take data-width data-in)
               (take data-width
                     (fv-adder t
                               (nthcdr data-width data-in)
                               (fv-not (take data-width data-in))))))))

  (defthm len-gcd-body$data-out1
    (equal (len (gcd-body$data-out1 inputs data-width))
           (* 2 (nfix data-width)))
    :hints (("Goal" :in-theory (enable gcd-body$data-out1))))

  (defthm bvp-gcd-body$data-out1
    (implies (bvp (gcd-body$data-in inputs data-width))
             (bvp (gcd-body$data-out1 inputs data-width)))
    :hints (("Goal" :in-theory (enable gcd-body$data-out1))))

  ;; Extract the inputs for the merge joint

  (defund gcd-body$me-inputs (inputs data-width)
    (b* ((full-in    (nth 0 inputs))
         (empty-out- (nth 1 inputs))
         (go-signals (nthcdr (gcd-body$data-ins-len data-width) inputs))

         (a<b (gcd-body$a<b inputs data-width))
         (data-out0 (gcd-body$data-out0 inputs data-width))
         (data-out1 (gcd-body$data-out1 inputs data-width)))
      (list* full-in full-in empty-out- a<b
             (append data-out0 data-out1 go-signals))))

  ;; Extract the "act0" signal

  (defund gcd-body$act0 (inputs data-width)
    (merge$act0 (gcd-body$me-inputs inputs data-width)
                (* 2 data-width)))

  ;; Extract the "act1" signal

  (defund gcd-body$act1 (inputs data-width)
    (merge$act1 (gcd-body$me-inputs inputs data-width)
                (* 2 data-width)))

  ;; Extract the "act" signal

  (defund gcd-body$act (inputs data-width)
    (f-or (gcd-body$act0 inputs data-width)
          (gcd-body$act1 inputs data-width)))

  ;; Extract the output data

  (defund gcd-body$data-out (inputs data-width)
    (fv-if (gcd-body$a<b inputs data-width)
           (gcd-body$data-out1 inputs data-width)
           (gcd-body$data-out0 inputs data-width)))

  (defthm len-gcd-body$data-out
    (equal (len (gcd-body$data-out inputs data-width))
           (* 2 (nfix data-width)))
    :hints (("Goal" :in-theory (enable gcd-body$data-out))))

  (defthm bvp-gcd-body$data-out
    (implies (bvp (gcd-body$data-in inputs data-width))
             (bvp (gcd-body$data-out inputs data-width)))
    :hints (("Goal" :in-theory (enable gcd-body$a<b
                                       gcd-body$data-out))))
  )

(not-primp-lemma gcd-body) ;; Prove that GCD-BODY is not a DE primitive.

;; The value lemma for GCD-BODY

(encapsulate
  ()

  (local
   (defthm list-of-singleton
     (implies (and (true-listp l)
                   (equal (len l) 1))
              (equal (list (car l))
                     l))))

  (defthmd gcd-body$value
    (b* ((inputs (list* full-in empty-out-
                        (append data-in go-signals))))
      (implies (and (posp data-width)
                    (gcd-body& netlist data-width)
                    (true-listp data-in)
                    (equal (len data-in) (* 2 data-width))
                    (true-listp go-signals)
                    (equal (len go-signals) *gcd-body$go-num*))
               (equal (se (si 'gcd-body data-width) inputs st netlist)
                      (list* (gcd-body$act inputs data-width)
                             (gcd-body$act0 inputs data-width)
                             (gcd-body$act1 inputs data-width)
                             (gcd-body$data-out inputs data-width)))))
    :hints (("Goal"
             :do-not-induct t
             :do-not '(preprocess)
             :expand (se (si 'gcd-body data-width)
                         (list* full-in empty-out-
                                (append data-in go-signals))
                         st
                         netlist)
             :in-theory (e/d (de-rules
                              not-primp-gcd-body
                              gcd-body&
                              gcd-body*$destructure
                              gcd-body$data-in
                              gcd-body$me-inputs
                              gcd-body$a<b
                              gcd-body$act
                              gcd-body$act0
                              gcd-body$act1
                              gcd-body$data-out
                              gcd-body$data-out0
                              gcd-body$data-out1
                              merge$act
                              merge$value
                              v-buf$value
                              v-<$value
                              ripple-add/sub$value-2)
                             ((gcd-body*)
                              append-take-nthcdr
                              de-module-disabled-rules)))))
  )

