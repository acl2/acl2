;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; September 2018

(in-package "ADE")

(include-book "q3-comp-gcd")
(include-book "q3-gcd")
(include-book "../fifo/simulators")

;; ======================================================================

;;; Simulators for:
;;;
;;; 1. GCD
;;; 2. COMP-GCD-COND
;;; 3. COMP-GCD
;;; 4. Q3-GCD
;;; 5. Q3-COMP-GCD

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

;; 2. COMP-GCD-COND

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

;; 3. COMP-GCD

(progn
  (defun comp-gcd$map-to-links (st)
    (b* ((s (get-field *comp-gcd$s* st))
         (l0 (get-field *comp-gcd$l0* st))
         (l1 (get-field *comp-gcd$l1* st))
         (l2 (get-field *comp-gcd$l2* st))
         (br (get-field *comp-gcd$br* st)))
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

  (defund comp-gcd$st-gen (data-width)
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
               (comp-gcd$inv st))
          state)))

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

;; 4. Q3-GCD

(progn
  (defun q3-gcd$map-to-links (st)
    (b* ((l   (get-field *q3-gcd$l* st))
         (q3  (get-field *q3-gcd$q3* st))
         (gcd (get-field *q3-gcd$gcd* st)))
      (append (list (cons 'q3 (queue3$map-to-links q3)))
              (map-to-links (list (cons 'l l)))
              (list (cons 'gcd (gcd$map-to-links gcd))))))

  (defun q3-gcd$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (q3-gcd$map-to-links (car x))
            (q3-gcd$map-to-links-list (cdr x)))))

  (defund q3-gcd$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((empty '(nil))
         (invalid-data (make-list (* 2 data-width) :initial-element '(x)))
         (q3 (queue3$st-gen (* 2 data-width)))
         (gcd (gcd$st-gen data-width)))
      (list (list empty invalid-data) q3 gcd)))

  (defund q3-gcd$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (q3-gcd$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (q3-gcd$st-gen data-width)))
      (mv (and (q3-gcd$input-format-n inputs-seq data-width n)
               (q3-gcd$valid-st st data-width)
               (q3-gcd$inv st))
          state)))

  (defund q3-gcd$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (q3-gcd$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (q3-gcd$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (q3-gcd$map-to-links-list
             (de-sim-trace (si 'q3-gcd data-width)
                           inputs-seq
                           st
                           (q3-gcd$netlist data-width))))
           0)
          state)))

  (defund q3-gcd$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (q3-gcd$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (q3-gcd$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-split-lst
                     (q3-gcd$in-seq inputs-seq st data-width n)
                     data-width)))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (q3-gcd$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 5. Q3-COMP-GCD

(progn
  (defun q3-comp-gcd$map-to-links (st)
    (b* ((l   (get-field *q3-comp-gcd$l* st))
         (q3  (get-field *q3-comp-gcd$q3* st))
         (comp-gcd (get-field *q3-comp-gcd$comp-gcd* st)))
      (append (list (cons 'q3 (queue3$map-to-links q3)))
              (map-to-links (list (cons 'l l)))
              (list (cons 'comp-gcd (comp-gcd$map-to-links comp-gcd))))))

  (defun q3-comp-gcd$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (q3-comp-gcd$map-to-links (car x))
            (q3-comp-gcd$map-to-links-list (cdr x)))))

  (defund q3-comp-gcd$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((empty '(nil))
         (invalid-data (make-list (* 2 data-width) :initial-element '(x)))
         (q3 (queue3$st-gen (* 2 data-width)))
         (comp-gcd (comp-gcd$st-gen data-width)))
      (list (list empty invalid-data) q3 comp-gcd)))

  (defund q3-comp-gcd$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (q3-comp-gcd$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (q3-comp-gcd$st-gen data-width)))
      (mv (and (q3-comp-gcd$input-format-n inputs-seq data-width n)
               (q3-comp-gcd$valid-st st data-width)
               (q3-comp-gcd$inv st))
          state)))

  (defund q3-comp-gcd$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (q3-comp-gcd$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (q3-comp-gcd$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (q3-comp-gcd$map-to-links-list
             (de-sim-trace (si 'q3-comp-gcd data-width)
                           inputs-seq
                           st
                           (q3-comp-gcd$netlist data-width))))
           0)
          state)))

  (defund q3-comp-gcd$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (q3-comp-gcd$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (q3-comp-gcd$st-gen data-width)))
      (mv
       (append
        (list
         (cons 'in-seq
               (v-to-nat-split-lst
                (q3-comp-gcd$in-seq inputs-seq st data-width n)
                data-width)))
        (list
         (cons 'out-seq
               (v-to-nat-lst
                (q3-comp-gcd$out-seq inputs-seq st data-width n)))))
       state)))
  )
