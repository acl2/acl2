;; Copyright (C) 2019, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "comp-interl2")
(include-book "igcd2")
(include-book "../fifo/simulators")
(include-book "../gcd/simulators")

;; ======================================================================

;;; Simulators for:
;;;
;;; 1. ARB-MERGE
;;; 2. INTERL
;;; 3. IGCD
;;; 4. COMP-INTERL

;; ======================================================================

;; 1. ARB-MERGE

(progn
  (defun arb-merge$map-to-links (st)
    (b* ((arb (nth *arb-merge$arb* st))
         (arb-buf (nth *arb-merge$arb-buf* st)))
      (map-to-links (list (cons 'arb arb)
                          (cons 'arb-buf arb-buf)))))

  (defun arb-merge$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (arb-merge$map-to-links (car x))
            (arb-merge$map-to-links-list (cdr x)))))

  (defund arb-merge$sim (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (arb-merge$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (full '(t))
         (empty '(nil))
         (st (list (list full '((nil) (nil) (nil)))
                   (list empty '((x) (x) (x))))))
      (mv (pretty-list
           (remove-dup-neighbors
            (arb-merge$map-to-links-list
             (de-sim-trace (si 'arb-merge data-size)
                           inputs-seq
                           st
                           (arb-merge$netlist data-size))))
           0)
          state)))
  )

;; 2. INTERL

(progn
  (defun interl$map-to-links (st)
    (b* ((q40-l0 (nth *interl$q40-l0* st))
         (q40-l1 (nth *interl$q40-l1* st))
         (arb-merge (nth *interl$arb-merge* st)))
      (append (list (cons 'q40-l0 (queue40-l$map-to-links q40-l0)))
              (list (cons 'q40-l1 (queue40-l$map-to-links q40-l1)))
              (list (cons 'arb-merge (arb-merge$map-to-links arb-merge))))))

  (defun interl$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (interl$map-to-links (car x))
            (interl$map-to-links-list (cdr x)))))

  (defund interl$st-gen (data-size)
    (declare (xargs :guard (natp data-size)))
    (b* ((full '(t))
         (empty '(nil))
         (q40-l0 (queue40-l$st-gen data-size))
         (q40-l1 (queue40-l$st-gen data-size))
         (arb-merge (list (list full '((nil) (nil) (nil)))
                          (list empty '((x) (x) (x))))))
      (list q40-l0 q40-l1 arb-merge)))

  (defund interl$ins-and-st-test (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (interl$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (interl$st-gen data-size)))
      (mv (and (interl$input-format-n inputs-seq data-size n)
               (interl$valid-st st data-size))
          state)))

  (local
   (defthm interl$ins-and-st-test-ok
     (interl$ins-and-st-test 4 10 state)))

  (defund interl$sim (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (interl$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (interl$st-gen data-size)))
      (mv (pretty-list
           (remove-dup-neighbors
            (interl$map-to-links-list
             (de-sim-trace (si 'interl data-size)
                           inputs-seq
                           st
                           (interl$netlist data-size))))
           0)
          state)))

  (defund interl$in-out-sim (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (interl$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (interl$st-gen data-size)))
      (mv
       (append
        (list (cons 'in0-seq
                    (v-to-nat-lst
                     (interl$in0-seq inputs-seq st data-size n))))
        (list (cons 'in1-seq
                    (v-to-nat-lst
                     (interl$in1-seq inputs-seq st data-size n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (interl$out-seq inputs-seq st data-size n)))))
       state)))
  )

;; 3. IGCD

(progn
  (defun igcd$map-to-links (st)
    (b* ((l (nth *igcd$l* st))
         (interl (nth *igcd$interl* st))
         (gcd1 (nth *igcd$gcd1* st)))
      (append (list (cons 'interl (interl$map-to-links interl)))
              (map-to-links (list (cons 'l l)))
              (list (cons 'gcd1 (gcd1$map-to-links gcd1))))))

  (defun igcd$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (igcd$map-to-links (car x))
            (igcd$map-to-links-list (cdr x)))))

  (defund igcd$st-gen (data-size)
    (declare (xargs :guard (natp data-size)))
    (b* ((empty '(nil))
         (invalid-data (make-list (* 2 data-size) :initial-element '(x)))
         (interl (interl$st-gen (* 2 data-size)))
         (gcd1 (gcd1$st-gen data-size)))
      (list (list empty invalid-data) interl gcd1)))

  (defund igcd$ins-and-st-test (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (igcd$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (igcd$st-gen data-size)))
      (mv (and (igcd$input-format-n inputs-seq data-size n)
               (igcd$valid-st st data-size)
               (igcd$inv st))
          state)))

  (local
   (defthm igcd$ins-and-st-test-ok
     (igcd$ins-and-st-test 4 10 state)))

  (defund igcd$sim (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (igcd$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (igcd$st-gen data-size)))
      (mv (pretty-list
           (remove-dup-neighbors
            (igcd$map-to-links-list
             (de-sim-trace (si 'igcd data-size)
                           inputs-seq
                           st
                           (igcd$netlist data-size))))
           0)
          state)))

  (defund igcd$in-out-sim (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (igcd$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (igcd$st-gen data-size)))
      (mv
       (append
        (list (cons 'in0-seq
                    (v-to-nat-lst
                     (igcd$in0-seq inputs-seq st data-size n))))
        (list (cons 'in1-seq
                    (v-to-nat-lst
                     (igcd$in1-seq inputs-seq st data-size n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (igcd$out-seq inputs-seq st data-size n)))))
       state)))
  )

;; 4. COMP-INTERL

(progn
  (defun comp-interl$map-to-links (st)
    (b* ((l0 (nth *comp-interl$l0* st))
         (l1 (nth *comp-interl$l1* st))
         (interl0 (nth *comp-interl$interl0* st))
         (interl1 (nth *comp-interl$interl1* st))
         (interl2 (nth *comp-interl$interl2* st)))
      (append (list (cons 'interl0 (interl$map-to-links interl0)))
              (list (cons 'interl1 (interl$map-to-links interl1)))
              (map-to-links (list (cons 'l0 l0)
                                  (cons 'l1 l1)))
              (list (cons 'interl2 (interl$map-to-links interl2))))))

  (defun comp-interl$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (comp-interl$map-to-links (car x))
            (comp-interl$map-to-links-list (cdr x)))))

  (defund comp-interl$st-gen (data-size)
    (declare (xargs :guard (natp data-size)))
    (b* ((empty '(nil))
         (invalid-data (make-list data-size :initial-element '(x)))
         (interl0 (interl$st-gen data-size))
         (interl1 (interl$st-gen data-size))
         (interl2 (interl$st-gen data-size)))
      (list (list empty invalid-data)
            (list empty invalid-data)
            interl0 interl1 interl2)))

  (defund comp-interl$ins-and-st-test (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-interl$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-interl$st-gen data-size)))
      (mv (and (comp-interl$input-format-n inputs-seq data-size n)
               (comp-interl$valid-st st data-size))
          state)))

  (local
   (defthm comp-interl$ins-and-st-test-ok
     (comp-interl$ins-and-st-test 4 10 state)))

  (defund comp-interl$sim (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-interl$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-interl$st-gen data-size)))
      (mv (pretty-list
           (remove-dup-neighbors
            (comp-interl$map-to-links-list
             (de-sim-trace (si 'comp-interl data-size)
                           inputs-seq
                           st
                           (comp-interl$netlist data-size))))
           0)
          state)))

  (defund comp-interl$in-out-sim (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-interl$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-interl$st-gen data-size)))
      (mv
       (append
        (list (cons 'in0-seq
                    (v-to-nat-lst
                     (comp-interl$in0-seq inputs-seq st data-size n))))
        (list (cons 'in1-seq
                    (v-to-nat-lst
                     (comp-interl$in1-seq inputs-seq st data-size n))))
        (list (cons 'in2-seq
                    (v-to-nat-lst
                     (comp-interl$in2-seq inputs-seq st data-size n))))
        (list (cons 'in3-seq
                    (v-to-nat-lst
                     (comp-interl$in3-seq inputs-seq st data-size n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (comp-interl$out-seq inputs-seq st data-size n)))))
       state)))
  )


