;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; January 2019

(in-package "ADE")

(include-book "subtractor")

;; ======================================================================

;; DE Module Generator of COUNTER

(module-generator
 counter* (data-size)
 (si 'counter data-size)
 (sis 'data-in 0 data-size)
 (sis 'data-out 0 data-size)
 ()
 (list
  '(g0 (low) vss ())
  '(g1 (high) vdd ())
  (list 'sub-1
        (sis 'data-out 0 (1+ data-size))
        (si 'ripple-sub data-size)
        (append (sis 'data-in 0 data-size)
                (cons 'high
                      (make-list (1- data-size)
                                 :initial-element 'low)))))
 (declare (xargs :guard (posp data-size))))

;; DE netlist generator.  A generated netlist will contain an instance of
;; COUNTER.

(defund counter$netlist (data-size)
  (declare (xargs :guard (posp data-size)))
  (cons (counter* data-size)
        (union$ (ripple-sub$netlist data-size)
                :test 'equal)))

;; Recognizer for COUNTER

(defund counter& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (posp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'counter data-size) netlist)))
    (and (equal (assoc (si 'counter data-size) netlist)
                (counter* data-size))
         (ripple-sub& subnetlist data-size))))

;; Sanity check

(local
 (defthmd check-counter$netlist-64
   (and (net-syntax-okp (counter$netlist 64))
        (net-arity-okp (counter$netlist 64))
        (counter& (counter$netlist 64) 64))))

;; The value lemma for COUNTER

(defthm counter$value
  (implies
   (and (posp data-size)
        (counter& netlist data-size)
        (true-listp inputs)
        (equal (len inputs) data-size))
   (equal (se (si 'counter data-size) inputs st netlist)
          (fv-adder-output t
                           inputs
                           (fv-not
                            (cons t (make-list (1- data-size)))))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (data-size)
                          (se (si 'counter data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            fv-adder-output
                            counter&
                            counter*$destructure)
                           (de-module-disabled-rules)))))

(local
 (defthm counter-works-aux
   (and (bvp (cons t (repeat n nil)))
        (equal (v-to-nat (cons t (repeat n nil)))
               1))
   :hints (("Goal" :in-theory (enable bvp v-to-nat repeat)))))

(defthm counter-works
  (implies (and (posp n)
                (equal n (len a))
                (< 0 (v-to-nat a))
                (bvp a))
           (equal (v-to-nat
                   (v-adder-output t
                                   a
                                   (v-not
                                    (cons t (repeat (1- n) nil)))))
                  (1- (v-to-nat a)))))


