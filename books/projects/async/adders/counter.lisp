;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2018

(in-package "ADE")

(include-book "subtractor")

;; ======================================================================

;; DE Module Generator of COUNTER

(module-generator
 counter* (data-width)
 (si 'counter data-width)
 (sis 'data-in 0 data-width)
 (sis 'data-out 0 data-width)
 '()
 (list
  '(g0 (low) vss ())
  '(g1 (high) vdd ())
  (list 'sub-1
        (sis 'data-out 0 (1+ data-width))
        (si 'ripple-sub data-width)
        (append (sis 'data-in 0 data-width)
                (cons 'high
                      (make-list (1- data-width)
                                 :initial-element 'low)))))
 :guard (posp data-width))

;; DE netlist generator.  A generated netlist will contain an instance of
;; COUNTER.

(defun counter$netlist (data-width)
  (declare (xargs :guard (posp data-width)))
  (cons (counter* data-width)
        (union$ (ripple-sub$netlist data-width)
                :test 'equal)))

;; Recognizer for COUNTER

(defund counter& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (posp data-width))))
  (and (equal (assoc (si 'counter data-width) netlist)
              (counter* data-width))
       (b* ((netlist (delete-to-eq (si 'counter data-width) netlist)))
         (ripple-sub& netlist data-width))))

;; Sanity check

(local
 (defthmd check-counter$netlist-64
   (and (net-syntax-okp (counter$netlist 64))
        (net-arity-okp (counter$netlist 64))
        (counter& (counter$netlist 64) 64))))

(not-primp-lemma counter) ;; Prove that COUNTER is not a DE primitive.

;; The value lemma for COUNTER

(defthm counter$value
  (implies
   (and (posp data-width)
        (counter& netlist data-width)
        (true-listp inputs)
        (equal (len inputs) data-width))
   (equal (se (si 'counter data-width) inputs st netlist)
          (take data-width
                (fv-adder t
                          inputs
                          (fv-not
                           (cons t (make-list (1- data-width))))))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (data-width)
                          (se (si 'counter data-width) inputs st netlist))
           :in-theory (e/d (de-rules
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
                   (take n
                         (v-adder t
                                  a
                                  (v-not
                                   (cons t (repeat (1- n) nil))))))
                  (1- (v-to-nat a)))))


