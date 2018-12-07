;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; December 2018

(in-package "ADE")

(include-book "comp-gcd")
(include-book "comp-gcd2")
(include-book "q10-comp-gcd3")
(include-book "q10-gcd")
(include-book "../fifo/simulators")
(include-book "../serial-adder/simulators")

;; ======================================================================

;;; Simulators for:
;;;
;;; 1. GCD
;;; 2. COMP-GCD-BODY
;;; 3. COMP-GCD
;;; 4. COMP-GCD-BODY2
;;; 5. COMP-GCD2
;;; 6. COMP-GCD-COND
;;; 7. COMP-GCD3
;;; 8. Q10-GCD
;;; 9. Q10-COMP-GCD3

;; ======================================================================

(defun v-to-nat-split-lst (seq data-width)
    (declare (xargs :guard (and (true-list-listp seq)
                                (natp data-width))))
    (if (atom seq)
        nil
      (cons (list (v-to-nat (take data-width (car seq)))
                  (v-to-nat (nthcdr data-width (car seq))))
            (v-to-nat-split-lst (cdr seq) data-width))))

;; 1. GCD

(progn
  (defun gcd$map-to-links (st)
    (b* ((s (get-field *gcd$s* st))
         (l0 (get-field *gcd$l0* st))
         (l1 (get-field *gcd$l1* st))
         (l2 (get-field *gcd$l2* st)))
      (append (map-to-links1 (list (cons 's s)))
              (map-to-links (list (cons 'l0 l0)
                                  (cons 'l1 l1)
                                  (cons 'l2 l2))))))

  (defun gcd$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (gcd$map-to-links (car x))
            (gcd$map-to-links-list (cdr x)))))

  (defund gcd$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((full '(t))
         (empty '(nil))
         (invalid-data (make-list (* 2 data-width) :initial-element '(x))))
      (list (list full '(nil))
            (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data))))

  (defund gcd$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (gcd$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (gcd$st-gen data-width)))
      (mv (and (gcd$input-format-n inputs-seq data-width n)
               (gcd$valid-st st data-width)
               (gcd$inv st))
          state)))

  (local
   (defthm gcd$ins-and-st-test-ok
     (gcd$ins-and-st-test 4 10 state)))

  (defund gcd$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (gcd$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (gcd$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (gcd$map-to-links-list
             (de-sim-trace (si 'gcd data-width)
                           inputs-seq
                           st
                           (gcd$netlist data-width))))
           0)
          state)))

  (defund gcd$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (gcd$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (gcd$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-split-lst
                     (gcd$in-seq inputs-seq st data-width n)
                     data-width)))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (gcd$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 2. COMP-GCD-BODY

(progn
  (defun comp-gcd-body$map-to-links (st)
    (b* ((l0 (get-field *comp-gcd-body$l0* st))
         (l1 (get-field *comp-gcd-body$l1* st))
         (l2 (get-field *comp-gcd-body$l2* st)))
      (map-to-links (list (cons 'l0 l0)
                          (cons 'l1 l1)
                          (cons 'l2 l2)))))

  (defun comp-gcd-body$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (comp-gcd-body$map-to-links (car x))
            (comp-gcd-body$map-to-links-list (cdr x)))))

  (defund comp-gcd-body$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (invalid-data2 (make-list (* 2 data-width) :initial-element '(x))))
      (list (list empty invalid-data2)
            (list empty invalid-data)
            (list empty invalid-data))))

  (defund comp-gcd-body$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd-body$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd-body$st-gen data-width)))
      (mv (and (comp-gcd-body$input-format-n inputs-seq data-width n)
               (comp-gcd-body$valid-st st data-width)
               (comp-gcd-body$inv st))
          state)))

  (local
   (defthm comp-gcd-body$ins-and-st-test-ok
     (comp-gcd-body$ins-and-st-test 4 10 state)))

  (defund comp-gcd-body$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd-body$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd-body$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (comp-gcd-body$map-to-links-list
             (de-sim-trace (si 'comp-gcd-body data-width)
                           inputs-seq
                           st
                           (comp-gcd-body$netlist data-width))))
           0)
          state)))

  (defund comp-gcd-body$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd-body$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd-body$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-split-lst
                     (comp-gcd-body$in-seq inputs-seq st data-width n)
                     data-width)))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (comp-gcd-body$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 3. COMP-GCD

(progn
  (defun comp-gcd$map-to-links (st)
    (b* ((s (get-field *comp-gcd$s* st))
         (l0 (get-field *comp-gcd$l0* st))
         (l1 (get-field *comp-gcd$l1* st))
         (l2 (get-field *comp-gcd$l2* st))
         (body (get-field *comp-gcd$body* st)))
      (append (map-to-links1 (list (cons 's s)))
              (map-to-links (list (cons 'l0 l0)
                                  (cons 'l1 l1)))
              (list (cons 'body (comp-gcd-body$map-to-links body)))
              (map-to-links (list (cons 'l2 l2))))))

  (defun comp-gcd$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (comp-gcd$map-to-links (car x))
            (comp-gcd$map-to-links-list (cdr x)))))

  (defund comp-gcd$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((full '(t))
         (empty '(nil))
         (invalid-data (make-list (* 2 data-width) :initial-element '(x)))
         (body (comp-gcd-body$st-gen data-width)))
      (list (list full '(nil))
            (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data)
            body)))

  (defund comp-gcd$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd$st-gen data-width)))
      (mv (and (comp-gcd$input-format-n inputs-seq data-width n)
               (comp-gcd$valid-st st data-width)
               (comp-gcd$inv st data-width))
          state)))

  (local
   (defthm comp-gcd$ins-and-st-test-ok
     (comp-gcd$ins-and-st-test 4 10 state)))

  (defund comp-gcd$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (comp-gcd$map-to-links-list
             (de-sim-trace (si 'comp-gcd data-width)
                           inputs-seq
                           st
                           (comp-gcd$netlist data-width))))
           0)
          state)))

  (defund comp-gcd$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-split-lst
                     (comp-gcd$in-seq inputs-seq st data-width n)
                     data-width)))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (comp-gcd$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 4. COMP-GCD-BODY2

(progn
  (defun comp-gcd-body2$map-to-links (st)
    (b* ((l0 (get-field *comp-gcd-body2$l0* st))
         (l1 (get-field *comp-gcd-body2$l1* st))
         (l2 (get-field *comp-gcd-body2$l2* st))
         (sub (get-field *comp-gcd-body2$sub* st)))
      (append (map-to-links (list (cons 'l0 l0)))
              (list (cons 'sub (serial-sub$map-to-links sub)))
              (map-to-links (list (cons 'l1 l1)
                                  (cons 'l2 l2))))))

  (defun comp-gcd-body2$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (comp-gcd-body2$map-to-links (car x))
            (comp-gcd-body2$map-to-links-list (cdr x)))))

  (defund comp-gcd-body2$st-gen (data-width cnt-width)
    (declare (xargs :guard (and (natp data-width)
                                (posp cnt-width))))
    (b* ((empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (invalid-data2 (make-list (* 2 data-width) :initial-element '(x)))
         (sub (serial-sub$st-gen data-width cnt-width)))
      (list (list empty invalid-data2)
            (list empty invalid-data)
            (list empty invalid-data)
            sub)))

  (defund comp-gcd-body2$ins-and-st-test (data-width cnt-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (posp cnt-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd-body2$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd-body2$st-gen data-width cnt-width)))
      (mv (and (comp-gcd-body2$input-format-n inputs-seq data-width n)
               (comp-gcd-body2$valid-st st data-width cnt-width)
               (comp-gcd-body2$inv st data-width))
          state)))

  (local
   (defthm comp-gcd-body2$ins-and-st-test-ok
     (comp-gcd-body2$ins-and-st-test 4 3 10 state)))

  (defund comp-gcd-body2$sim (data-width cnt-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (posp cnt-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd-body2$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd-body2$st-gen data-width cnt-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (comp-gcd-body2$map-to-links-list
             (de-sim-trace (si 'comp-gcd-body2 data-width)
                           inputs-seq
                           st
                           (comp-gcd-body2$netlist data-width cnt-width))))
           0)
          state)))

  (defund comp-gcd-body2$in-out-sim (data-width cnt-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (posp cnt-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd-body2$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd-body2$st-gen data-width cnt-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-split-lst
                     (comp-gcd-body2$in-seq
                      inputs-seq st data-width cnt-width n)
                     data-width)))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (comp-gcd-body2$out-seq
                      inputs-seq st data-width cnt-width n)))))
       state)))
  )

;; 5. COMP-GCD2

(progn
  (defun comp-gcd2$map-to-links (st)
    (b* ((s (get-field *comp-gcd2$s* st))
         (l0 (get-field *comp-gcd2$l0* st))
         (l1 (get-field *comp-gcd2$l1* st))
         (l2 (get-field *comp-gcd2$l2* st))
         (body (get-field *comp-gcd2$body* st)))
      (append (map-to-links1 (list (cons 's s)))
              (map-to-links (list (cons 'l0 l0)
                                  (cons 'l1 l1)))
              (list (cons 'body (comp-gcd-body2$map-to-links body)))
              (map-to-links (list (cons 'l2 l2))))))

  (defun comp-gcd2$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (comp-gcd2$map-to-links (car x))
            (comp-gcd2$map-to-links-list (cdr x)))))

  (defund comp-gcd2$st-gen (data-width cnt-width)
    (declare (xargs :guard (and (natp data-width)
                                (posp cnt-width))))
    (b* ((full '(t))
         (empty '(nil))
         (invalid-data (make-list (* 2 data-width) :initial-element '(x)))
         (body (comp-gcd-body2$st-gen data-width cnt-width)))
      (list (list full '(nil))
            (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data)
            body)))

  (defund comp-gcd2$ins-and-st-test (data-width cnt-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (posp cnt-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd2$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd2$st-gen data-width cnt-width)))
      (mv (and (comp-gcd2$input-format-n inputs-seq data-width n)
               (comp-gcd2$valid-st st data-width cnt-width)
               (comp-gcd2$inv st data-width))
          state)))

  (local
   (defthm comp-gcd2$ins-and-st-test-ok
     (comp-gcd2$ins-and-st-test 4 3 10 state)))

  (defund comp-gcd2$sim (data-width cnt-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (posp cnt-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd2$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd2$st-gen data-width cnt-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (comp-gcd2$map-to-links-list
             (de-sim-trace (si 'comp-gcd2 data-width)
                           inputs-seq
                           st
                           (comp-gcd2$netlist data-width cnt-width))))
           0)
          state)))

  (defund comp-gcd2$in-out-sim (data-width cnt-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (posp cnt-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd2$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd2$st-gen data-width cnt-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-split-lst
                     (comp-gcd2$in-seq
                      inputs-seq st data-width cnt-width n)
                     data-width)))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (comp-gcd2$out-seq
                      inputs-seq st data-width cnt-width n)))))
       state)))
  )

;; 6. COMP-GCD-COND

(progn
  (defun comp-gcd-cond$map-to-links (st)
    (b* ((a0 (get-field *comp-gcd-cond$a0* st))
         (b0 (get-field *comp-gcd-cond$b0* st))
         (a1 (get-field *comp-gcd-cond$a1* st))
         (b1 (get-field *comp-gcd-cond$b1* st))
         (q2 (get-field *comp-gcd-cond$q2* st))
         (q3 (get-field *comp-gcd-cond$q3* st)))
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

  (defund comp-gcd-cond$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (q2 (queue2$st-gen data-width))
         (q3 (queue3$st-gen data-width)))
      (list (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data)
            q2 q3)))

  (defund comp-gcd-cond$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd-cond$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd-cond$st-gen data-width)))
      (mv (and (comp-gcd-cond$input-format-n inputs-seq data-width n)
               (comp-gcd-cond$valid-st st data-width)
               (comp-gcd-cond$inv st))
          state)))

  (local
   (defthm comp-gcd-cond$ins-and-st-test-ok
     (comp-gcd-cond$ins-and-st-test 4 10 state)))

  (defund comp-gcd-cond$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd-cond$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd-cond$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (comp-gcd-cond$map-to-links-list
             (de-sim-trace (si 'comp-gcd-cond data-width)
                           inputs-seq
                           st
                           (comp-gcd-cond$netlist data-width))))
           0)
          state)))

  (defund comp-gcd-cond$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd-cond$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd-cond$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat2-lst
                     (comp-gcd-cond$in-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (comp-gcd-cond$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 7. COMP-GCD3

(progn
  (defun comp-gcd3$map-to-links (st)
    (b* ((s (get-field *comp-gcd3$s* st))
         (l0 (get-field *comp-gcd3$l0* st))
         (l1 (get-field *comp-gcd3$l1* st))
         (l2 (get-field *comp-gcd3$l2* st))
         (br (get-field *comp-gcd3$br* st)))
      (append (map-to-links1 (list (cons 's s)))
              (map-to-links (list (cons 'l0 l0)
                                  (cons 'l1 l1)
                                  (cons 'l2 l2)))
              (list (cons 'br (comp-gcd-cond$map-to-links br))))))

  (defun comp-gcd3$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (comp-gcd3$map-to-links (car x))
            (comp-gcd3$map-to-links-list (cdr x)))))

  (defund comp-gcd3$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((full '(t))
         (empty '(nil))
         (invalid-data (make-list (* 2 data-width) :initial-element '(x)))
         (br (comp-gcd-cond$st-gen data-width)))
      (list (list full '(nil))
            (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data)
            br)))

  (defund comp-gcd3$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd3$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd3$st-gen data-width)))
      (mv (and (comp-gcd3$input-format-n inputs-seq data-width n)
               (comp-gcd3$valid-st st data-width)
               (comp-gcd3$inv st))
          state)))

  (local
   (defthm comp-gcd3$ins-and-st-test-ok
     (comp-gcd3$ins-and-st-test 4 10 state)))

  (defund comp-gcd3$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd3$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd3$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (comp-gcd3$map-to-links-list
             (de-sim-trace (si 'comp-gcd3 data-width)
                           inputs-seq
                           st
                           (comp-gcd3$netlist data-width))))
           0)
          state)))

  (defund comp-gcd3$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-gcd3$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-gcd3$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-split-lst
                     (comp-gcd3$in-seq inputs-seq st data-width n)
                     data-width)))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (comp-gcd3$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 8. Q10-GCD

(progn
  (defun q10-gcd$map-to-links (st)
    (b* ((l   (get-field *q10-gcd$l* st))
         (q10 (get-field *q10-gcd$q10* st))
         (gcd (get-field *q10-gcd$gcd* st)))
      (append (list (cons 'q10 (queue10$map-to-links q10)))
              (map-to-links (list (cons 'l l)))
              (list (cons 'gcd (gcd$map-to-links gcd))))))

  (defun q10-gcd$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (q10-gcd$map-to-links (car x))
            (q10-gcd$map-to-links-list (cdr x)))))

  (defund q10-gcd$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((empty '(nil))
         (invalid-data (make-list (* 2 data-width) :initial-element '(x)))
         (q10 (queue10$st-gen (* 2 data-width)))
         (gcd (gcd$st-gen data-width)))
      (list (list empty invalid-data) q10 gcd)))

  (defund q10-gcd$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (q10-gcd$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (q10-gcd$st-gen data-width)))
      (mv (and (q10-gcd$input-format-n inputs-seq data-width n)
               (q10-gcd$valid-st st data-width)
               (q10-gcd$inv st))
          state)))

  (local
   (defthm q10-gcd$ins-and-st-test-ok
     (q10-gcd$ins-and-st-test 4 10 state)))

  (defund q10-gcd$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (q10-gcd$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (q10-gcd$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (q10-gcd$map-to-links-list
             (de-sim-trace (si 'q10-gcd data-width)
                           inputs-seq
                           st
                           (q10-gcd$netlist data-width))))
           0)
          state)))

  (defund q10-gcd$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (q10-gcd$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (q10-gcd$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-split-lst
                     (q10-gcd$in-seq inputs-seq st data-width n)
                     data-width)))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (q10-gcd$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 9. Q10-COMP-GCD3

(progn
  (defun q10-comp-gcd3$map-to-links (st)
    (b* ((l   (get-field *q10-comp-gcd3$l* st))
         (q10 (get-field *q10-comp-gcd3$q10* st))
         (comp-gcd3 (get-field *q10-comp-gcd3$comp-gcd3* st)))
      (append (list (cons 'q10 (queue10$map-to-links q10)))
              (map-to-links (list (cons 'l l)))
              (list (cons 'comp-gcd3 (comp-gcd3$map-to-links comp-gcd3))))))

  (defun q10-comp-gcd3$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (q10-comp-gcd3$map-to-links (car x))
            (q10-comp-gcd3$map-to-links-list (cdr x)))))

  (defund q10-comp-gcd3$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((empty '(nil))
         (invalid-data (make-list (* 2 data-width) :initial-element '(x)))
         (q10 (queue10$st-gen (* 2 data-width)))
         (comp-gcd3 (comp-gcd3$st-gen data-width)))
      (list (list empty invalid-data) q10 comp-gcd3)))

  (defund q10-comp-gcd3$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (q10-comp-gcd3$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (q10-comp-gcd3$st-gen data-width)))
      (mv (and (q10-comp-gcd3$input-format-n inputs-seq data-width n)
               (q10-comp-gcd3$valid-st st data-width)
               (q10-comp-gcd3$inv st))
          state)))

  (local
   (defthm q10-comp-gcd3$ins-and-st-test-ok
     (q10-comp-gcd3$ins-and-st-test 4 10 state)))

  (defund q10-comp-gcd3$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (q10-comp-gcd3$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (q10-comp-gcd3$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (q10-comp-gcd3$map-to-links-list
             (de-sim-trace (si 'q10-comp-gcd3 data-width)
                           inputs-seq
                           st
                           (q10-comp-gcd3$netlist data-width))))
           0)
          state)))

  (defund q10-comp-gcd3$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (q10-comp-gcd3$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (q10-comp-gcd3$st-gen data-width)))
      (mv
       (append
        (list
         (cons 'in-seq
               (v-to-nat-split-lst
                (q10-comp-gcd3$in-seq inputs-seq st data-width n)
                data-width)))
        (list
         (cons 'out-seq
               (v-to-nat-lst
                (q10-comp-gcd3$out-seq inputs-seq st data-width n)))))
       state)))
  )


