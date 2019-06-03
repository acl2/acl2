;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "gcd2")
(include-book "gcd3")
(include-book "q10-comp-gcd")
(include-book "q10-gcd1")
(include-book "../fifo/simulators")
(include-book "../serial-adder/simulators")

;; ======================================================================

;;; Simulators for:
;;;
;;; 1. GCD1
;;; 2. GCD-BODY2
;;; 3. GCD2
;;; 4. GCD-BODY3
;;; 5. GCD3
;;; 6. COMP-GCD-COND
;;; 7. COMP-GCD
;;; 8. Q10-GCD1
;;; 9. Q10-COMP-GCD

;; ======================================================================

(defun v-to-nat-split-lst (seq data-size)
    (declare (xargs :guard (and (true-list-listp seq)
                                (natp data-size))))
    (if (atom seq)
        nil
      (cons (list (v-to-nat (take data-size (car seq)))
                  (v-to-nat (nthcdr data-size (car seq))))
            (v-to-nat-split-lst (cdr seq) data-size))))

;; 1. GCD1

(progn
  (defun gcd1$map-to-links (st)
    (b* ((s (nth *gcd1$s* st))
         (l0 (nth *gcd1$l0* st))
         (l1 (nth *gcd1$l1* st))
         (l2 (nth *gcd1$l2* st)))
      (append (map-to-links1 (list (cons 's s)))
              (map-to-links (list (cons 'l0 l0)
                                  (cons 'l1 l1)
                                  (cons 'l2 l2))))))

  (defun gcd1$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (gcd1$map-to-links (car x))
            (gcd1$map-to-links-list (cdr x)))))

  (defund gcd1$st-gen (data-size)
    (declare (xargs :guard (natp data-size)))
    (b* ((full '(t))
         (empty '(nil))
         (invalid-data (make-list (* 2 data-size) :initial-element '(x))))
      (list (list full '(nil))
            (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data))))

  (defund gcd1$ins-and-st-test (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (gcd1$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (gcd1$st-gen data-size)))
      (mv (and (gcd1$input-format-n inputs-seq data-size n)
               (gcd1$valid-st st data-size)
               (gcd1$inv st))
          state)))

  (local
   (defthm gcd1$ins-and-st-test-ok
     (gcd1$ins-and-st-test 4 10 state)))

  (defund gcd1$sim (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (gcd1$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (gcd1$st-gen data-size)))
      (mv (pretty-list
           (remove-dup-neighbors
            (gcd1$map-to-links-list
             (de-sim-trace (si 'gcd1 data-size)
                           inputs-seq
                           st
                           (gcd1$netlist data-size))))
           0)
          state)))

  (defund gcd1$in-out-sim (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (gcd1$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (gcd1$st-gen data-size)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-split-lst
                     (gcd1$in-seq inputs-seq st data-size n)
                     data-size)))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (gcd1$out-seq inputs-seq st data-size n)))))
       state)))
  )

;; 2. GCD-BODY2

(progn
  (defun gcd-body2$map-to-links (st)
    (b* ((l0 (nth *gcd-body2$l0* st))
         (l1 (nth *gcd-body2$l1* st))
         (l2 (nth *gcd-body2$l2* st)))
      (map-to-links (list (cons 'l0 l0)
                          (cons 'l1 l1)
                          (cons 'l2 l2)))))

  (defun gcd-body2$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (gcd-body2$map-to-links (car x))
            (gcd-body2$map-to-links-list (cdr x)))))

  (defund gcd-body2$st-gen (data-size)
    (declare (xargs :guard (natp data-size)))
    (b* ((empty '(nil))
         (invalid-data (make-list data-size :initial-element '(x)))
         (invalid-data2 (make-list (* 2 data-size) :initial-element '(x))))
      (list (list empty invalid-data2)
            (list empty invalid-data)
            (list empty invalid-data))))

  (defund gcd-body2$ins-and-st-test (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (gcd-body2$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (gcd-body2$st-gen data-size)))
      (mv (and (gcd-body2$input-format-n inputs-seq data-size n)
               (gcd-body2$valid-st st data-size)
               (gcd-body2$inv st))
          state)))

  (local
   (defthm gcd-body2$ins-and-st-test-ok
     (gcd-body2$ins-and-st-test 4 10 state)))

  (defund gcd-body2$sim (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (gcd-body2$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (gcd-body2$st-gen data-size)))
      (mv (pretty-list
           (remove-dup-neighbors
            (gcd-body2$map-to-links-list
             (de-sim-trace (si 'gcd-body2 data-size)
                           inputs-seq
                           st
                           (gcd-body2$netlist data-size))))
           0)
          state)))

  (defund gcd-body2$in-out-sim (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (gcd-body2$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (gcd-body2$st-gen data-size)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-split-lst
                     (gcd-body2$in-seq inputs-seq st data-size n)
                     data-size)))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (gcd-body2$out-seq inputs-seq st data-size n)))))
       state)))
  )

;; 3. GCD2

(progn
  (defun gcd2$map-to-links (st)
    (b* ((s (nth *gcd2$s* st))
         (l0 (nth *gcd2$l0* st))
         (l1 (nth *gcd2$l1* st))
         (l2 (nth *gcd2$l2* st))
         (body (nth *gcd2$body* st)))
      (append (map-to-links1 (list (cons 's s)))
              (map-to-links (list (cons 'l0 l0)
                                  (cons 'l1 l1)))
              (list (cons 'body (gcd-body2$map-to-links body)))
              (map-to-links (list (cons 'l2 l2))))))

  (defun gcd2$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (gcd2$map-to-links (car x))
            (gcd2$map-to-links-list (cdr x)))))

  (defund gcd2$st-gen (data-size)
    (declare (xargs :guard (natp data-size)))
    (b* ((full '(t))
         (empty '(nil))
         (invalid-data (make-list (* 2 data-size) :initial-element '(x)))
         (body (gcd-body2$st-gen data-size)))
      (list (list full '(nil))
            (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data)
            body)))

  (defund gcd2$ins-and-st-test (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (gcd2$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (gcd2$st-gen data-size)))
      (mv (and (gcd2$input-format-n inputs-seq data-size n)
               (gcd2$valid-st st data-size)
               (gcd2$inv st data-size))
          state)))

  (local
   (defthm gcd2$ins-and-st-test-ok
     (gcd2$ins-and-st-test 4 10 state)))

  (defund gcd2$sim (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (gcd2$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (gcd2$st-gen data-size)))
      (mv (pretty-list
           (remove-dup-neighbors
            (gcd2$map-to-links-list
             (de-sim-trace (si 'gcd2 data-size)
                           inputs-seq
                           st
                           (gcd2$netlist data-size))))
           0)
          state)))

  (defund gcd2$in-out-sim (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (gcd2$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (gcd2$st-gen data-size)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-split-lst
                     (gcd2$in-seq inputs-seq st data-size n)
                     data-size)))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (gcd2$out-seq inputs-seq st data-size n)))))
       state)))
  )

;; 4. GCD-BODY3

(progn
  (defun gcd-body3$map-to-links (st)
    (b* ((l0 (nth *gcd-body3$l0* st))
         (l1 (nth *gcd-body3$l1* st))
         (l2 (nth *gcd-body3$l2* st))
         (sub (nth *gcd-body3$sub* st)))
      (append (map-to-links (list (cons 'l0 l0)))
              (list (cons 'sub (serial-sub$map-to-links sub)))
              (map-to-links (list (cons 'l1 l1)
                                  (cons 'l2 l2))))))

  (defun gcd-body3$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (gcd-body3$map-to-links (car x))
            (gcd-body3$map-to-links-list (cdr x)))))

  (defund gcd-body3$st-gen (data-size cnt-size)
    (declare (xargs :guard (and (natp data-size)
                                (posp cnt-size))))
    (b* ((empty '(nil))
         (invalid-data (make-list data-size :initial-element '(x)))
         (invalid-data2 (make-list (* 2 data-size) :initial-element '(x)))
         (sub (serial-sub$st-gen data-size cnt-size)))
      (list (list empty invalid-data2)
            (list empty invalid-data)
            (list empty invalid-data)
            sub)))

  (defund gcd-body3$ins-and-st-test (data-size cnt-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (posp cnt-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (gcd-body3$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (gcd-body3$st-gen data-size cnt-size)))
      (mv (and (gcd-body3$input-format-n inputs-seq data-size n)
               (gcd-body3$valid-st st data-size cnt-size)
               (gcd-body3$inv st data-size))
          state)))

  (local
   (defthm gcd-body3$ins-and-st-test-ok
     (gcd-body3$ins-and-st-test 4 3 10 state)))

  (defund gcd-body3$sim (data-size cnt-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (posp cnt-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (gcd-body3$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (gcd-body3$st-gen data-size cnt-size)))
      (mv (pretty-list
           (remove-dup-neighbors
            (gcd-body3$map-to-links-list
             (de-sim-trace (si 'gcd-body3 data-size)
                           inputs-seq
                           st
                           (gcd-body3$netlist data-size cnt-size))))
           0)
          state)))

  (defund gcd-body3$in-out-sim (data-size cnt-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (posp cnt-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (gcd-body3$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (gcd-body3$st-gen data-size cnt-size)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-split-lst
                     (gcd-body3$in-seq
                      inputs-seq st data-size cnt-size n)
                     data-size)))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (gcd-body3$out-seq
                      inputs-seq st data-size cnt-size n)))))
       state)))
  )

;; 5. GCD3

(progn
  (defun gcd3$map-to-links (st)
    (b* ((s (nth *gcd3$s* st))
         (l0 (nth *gcd3$l0* st))
         (l1 (nth *gcd3$l1* st))
         (l2 (nth *gcd3$l2* st))
         (body (nth *gcd3$body* st)))
      (append (map-to-links1 (list (cons 's s)))
              (map-to-links (list (cons 'l0 l0)
                                  (cons 'l1 l1)))
              (list (cons 'body (gcd-body3$map-to-links body)))
              (map-to-links (list (cons 'l2 l2))))))

  (defun gcd3$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (gcd3$map-to-links (car x))
            (gcd3$map-to-links-list (cdr x)))))

  (defund gcd3$st-gen (data-size cnt-size)
    (declare (xargs :guard (and (natp data-size)
                                (posp cnt-size))))
    (b* ((full '(t))
         (empty '(nil))
         (invalid-data (make-list (* 2 data-size) :initial-element '(x)))
         (body (gcd-body3$st-gen data-size cnt-size)))
      (list (list full '(nil))
            (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data)
            body)))

  (defund gcd3$ins-and-st-test (data-size cnt-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (posp cnt-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (gcd3$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (gcd3$st-gen data-size cnt-size)))
      (mv (and (gcd3$input-format-n inputs-seq data-size n)
               (gcd3$valid-st st data-size cnt-size)
               (gcd3$inv st data-size))
          state)))

  (local
   (defthm gcd3$ins-and-st-test-ok
     (gcd3$ins-and-st-test 4 3 10 state)))

  (defund gcd3$sim (data-size cnt-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (posp cnt-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (gcd3$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (gcd3$st-gen data-size cnt-size)))
      (mv (pretty-list
           (remove-dup-neighbors
            (gcd3$map-to-links-list
             (de-sim-trace (si 'gcd3 data-size)
                           inputs-seq
                           st
                           (gcd3$netlist data-size cnt-size))))
           0)
          state)))

  (defund gcd3$in-out-sim (data-size cnt-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (posp cnt-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (gcd3$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (gcd3$st-gen data-size cnt-size)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-split-lst
                     (gcd3$in-seq
                      inputs-seq st data-size cnt-size n)
                     data-size)))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (gcd3$out-seq
                      inputs-seq st data-size cnt-size n)))))
       state)))
  )

;; 6. COMP-GCD-COND

(progn
  (defun comp-gcd-cond$map-to-links (st)
    (b* ((a0 (nth *comp-gcd-cond$a0* st))
         (b0 (nth *comp-gcd-cond$b0* st))
         (a1 (nth *comp-gcd-cond$a1* st))
         (b1 (nth *comp-gcd-cond$b1* st))
         (q2 (nth *comp-gcd-cond$q2* st))
         (q3 (nth *comp-gcd-cond$q3* st)))
      (append (map-to-links (list (cons 'a0 a0)
                                  (cons 'b0 b0)))
              (cons (cons 'q2 (queue2$map-to-links q2))
                    (cons (cons 'q3 (queue3$map-to-links q3))
                          (map-to-links (list (cons 'a1 a1)
                                              (cons 'b1 b1))))))))

  (defun comp-gcd-cond$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (comp-gcd-cond$map-to-links (car x))
            (comp-gcd-cond$map-to-links-list (cdr x)))))

  (defund comp-gcd-cond$st-gen (data-size)
    (declare (xargs :guard (natp data-size)))
    (b* ((empty '(nil))
         (invalid-data (make-list data-size :initial-element '(x)))
         (q2 (queue2$st-gen data-size))
         (q3 (queue3$st-gen data-size)))
      (list (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data)
            q2 q3)))

  (defund comp-gcd-cond$ins-and-st-test (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd-cond$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd-cond$st-gen data-size)))
      (mv (and (comp-gcd-cond$input-format-n inputs-seq data-size n)
               (comp-gcd-cond$valid-st st data-size)
               (comp-gcd-cond$inv st))
          state)))

  (local
   (defthm comp-gcd-cond$ins-and-st-test-ok
     (comp-gcd-cond$ins-and-st-test 4 10 state)))

  (defund comp-gcd-cond$sim (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd-cond$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd-cond$st-gen data-size)))
      (mv (pretty-list
           (remove-dup-neighbors
            (comp-gcd-cond$map-to-links-list
             (de-sim-trace (si 'comp-gcd-cond data-size)
                           inputs-seq
                           st
                           (comp-gcd-cond$netlist data-size))))
           0)
          state)))

  (defund comp-gcd-cond$in-out-sim (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd-cond$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd-cond$st-gen data-size)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat2-lst
                     (comp-gcd-cond$in-seq inputs-seq st data-size n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (comp-gcd-cond$out-seq inputs-seq st data-size n)))))
       state)))
  )

;; 7. COMP-GCD

(progn
  (defun comp-gcd$map-to-links (st)
    (b* ((s (nth *comp-gcd$s* st))
         (l0 (nth *comp-gcd$l0* st))
         (l1 (nth *comp-gcd$l1* st))
         (l2 (nth *comp-gcd$l2* st))
         (br (nth *comp-gcd$br* st)))
      (append (map-to-links1 (list (cons 's s)))
              (map-to-links (list (cons 'l0 l0)
                                  (cons 'l1 l1)
                                  (cons 'l2 l2)))
              (list (cons 'br (comp-gcd-cond$map-to-links br))))))

  (defun comp-gcd$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (comp-gcd$map-to-links (car x))
            (comp-gcd$map-to-links-list (cdr x)))))

  (defund comp-gcd$st-gen (data-size)
    (declare (xargs :guard (natp data-size)))
    (b* ((full '(t))
         (empty '(nil))
         (invalid-data (make-list (* 2 data-size) :initial-element '(x)))
         (br (comp-gcd-cond$st-gen data-size)))
      (list (list full '(nil))
            (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data)
            br)))

  (defund comp-gcd$ins-and-st-test (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd$st-gen data-size)))
      (mv (and (comp-gcd$input-format-n inputs-seq data-size n)
               (comp-gcd$valid-st st data-size)
               (comp-gcd$inv st))
          state)))

  (local
   (defthm comp-gcd$ins-and-st-test-ok
     (comp-gcd$ins-and-st-test 4 10 state)))

  (defund comp-gcd$sim (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd$st-gen data-size)))
      (mv (pretty-list
           (remove-dup-neighbors
            (comp-gcd$map-to-links-list
             (de-sim-trace (si 'comp-gcd data-size)
                           inputs-seq
                           st
                           (comp-gcd$netlist data-size))))
           0)
          state)))

  (defund comp-gcd$in-out-sim (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd$st-gen data-size)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-split-lst
                     (comp-gcd$in-seq inputs-seq st data-size n)
                     data-size)))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (comp-gcd$out-seq inputs-seq st data-size n)))))
       state)))
  )

;; 8. Q10-GCD1

(progn
  (defun q10-gcd1$map-to-links (st)
    (b* ((l   (nth *q10-gcd1$l* st))
         (q10 (nth *q10-gcd1$q10* st))
         (gcd1 (nth *q10-gcd1$gcd1* st)))
      (append (list (cons 'q10 (queue10$map-to-links q10)))
              (map-to-links (list (cons 'l l)))
              (list (cons 'gcd1 (gcd1$map-to-links gcd1))))))

  (defun q10-gcd1$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (q10-gcd1$map-to-links (car x))
            (q10-gcd1$map-to-links-list (cdr x)))))

  (defund q10-gcd1$st-gen (data-size)
    (declare (xargs :guard (natp data-size)))
    (b* ((empty '(nil))
         (invalid-data (make-list (* 2 data-size) :initial-element '(x)))
         (q10 (queue10$st-gen (* 2 data-size)))
         (gcd1 (gcd1$st-gen data-size)))
      (list (list empty invalid-data) q10 gcd1)))

  (defund q10-gcd1$ins-and-st-test (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (q10-gcd1$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (q10-gcd1$st-gen data-size)))
      (mv (and (q10-gcd1$input-format-n inputs-seq data-size n)
               (q10-gcd1$valid-st st data-size)
               (q10-gcd1$inv st))
          state)))

  (local
   (defthm q10-gcd1$ins-and-st-test-ok
     (q10-gcd1$ins-and-st-test 4 10 state)))

  (defund q10-gcd1$sim (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (q10-gcd1$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (q10-gcd1$st-gen data-size)))
      (mv (pretty-list
           (remove-dup-neighbors
            (q10-gcd1$map-to-links-list
             (de-sim-trace (si 'q10-gcd1 data-size)
                           inputs-seq
                           st
                           (q10-gcd1$netlist data-size))))
           0)
          state)))

  (defund q10-gcd1$in-out-sim (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (q10-gcd1$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (q10-gcd1$st-gen data-size)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-split-lst
                     (q10-gcd1$in-seq inputs-seq st data-size n)
                     data-size)))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (q10-gcd1$out-seq inputs-seq st data-size n)))))
       state)))
  )

;; 9. Q10-COMP-GCD

(progn
  (defun q10-comp-gcd$map-to-links (st)
    (b* ((l   (nth *q10-comp-gcd$l* st))
         (q10 (nth *q10-comp-gcd$q10* st))
         (comp-gcd (nth *q10-comp-gcd$comp-gcd* st)))
      (append (list (cons 'q10 (queue10$map-to-links q10)))
              (map-to-links (list (cons 'l l)))
              (list (cons 'comp-gcd (comp-gcd$map-to-links comp-gcd))))))

  (defun q10-comp-gcd$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (q10-comp-gcd$map-to-links (car x))
            (q10-comp-gcd$map-to-links-list (cdr x)))))

  (defund q10-comp-gcd$st-gen (data-size)
    (declare (xargs :guard (natp data-size)))
    (b* ((empty '(nil))
         (invalid-data (make-list (* 2 data-size) :initial-element '(x)))
         (q10 (queue10$st-gen (* 2 data-size)))
         (comp-gcd (comp-gcd$st-gen data-size)))
      (list (list empty invalid-data) q10 comp-gcd)))

  (defund q10-comp-gcd$ins-and-st-test (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (q10-comp-gcd$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (q10-comp-gcd$st-gen data-size)))
      (mv (and (q10-comp-gcd$input-format-n inputs-seq data-size n)
               (q10-comp-gcd$valid-st st data-size)
               (q10-comp-gcd$inv st))
          state)))

  (local
   (defthm q10-comp-gcd$ins-and-st-test-ok
     (q10-comp-gcd$ins-and-st-test 4 10 state)))

  (defund q10-comp-gcd$sim (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (q10-comp-gcd$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (q10-comp-gcd$st-gen data-size)))
      (mv (pretty-list
           (remove-dup-neighbors
            (q10-comp-gcd$map-to-links-list
             (de-sim-trace (si 'q10-comp-gcd data-size)
                           inputs-seq
                           st
                           (q10-comp-gcd$netlist data-size))))
           0)
          state)))

  (defund q10-comp-gcd$in-out-sim (data-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (q10-comp-gcd$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (q10-comp-gcd$st-gen data-size)))
      (mv
       (append
        (list
         (cons 'in-seq
               (v-to-nat-split-lst
                (q10-comp-gcd$in-seq inputs-seq st data-size n)
                data-size)))
        (list
         (cons 'out-seq
               (v-to-nat-lst
                (q10-comp-gcd$out-seq inputs-seq st data-size n)))))
       state)))
  )


