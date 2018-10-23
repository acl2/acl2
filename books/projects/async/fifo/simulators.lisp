;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; September 2018

(in-package "ADE")

(include-book "comp-v-or")
(include-book "queue9-l")
(include-book "queue10")
(include-book "queue11-l")
(include-book "queue20-l")
(include-book "round-robin1")
(include-book "round-robin2")
(include-book "round-robin3")
(include-book "wig-wag")

;; ======================================================================

;;; Simulators for:
;;;
;;; 1.  Q2
;;; 2.  Q3
;;; 3.  Q4
;;; 4.  Q5
;;; 5.  Q10
;;; 6.  Q3-L
;;; 7.  Q4-L
;;; 8.  Q5-L
;;; 9.  Q8-L
;;; 10. Q9-L
;;; 11. Q10-L
;;; 12. Q11-L
;;; 13. Q20-L
;;; 14. COMP-V-OR
;;; 15. ALT-MERGE
;;; 16. ALT-BRANCH
;;; 17. WW
;;; 18. RR1
;;; 19. RR2
;;; 20. RR3

;; ======================================================================

;; 1. Q2

(progn
  (defun queue2$map-to-links (st)
    (b* ((l0 (get-field *queue2$l0* st))
         (l1 (get-field *queue2$l1* st)))
      (map-to-links (list (cons 'l0 l0)
                          (cons 'l1 l1)))))

  (defun queue2$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (queue2$map-to-links (car x))
            (queue2$map-to-links-list (cdr x)))))

  (defund queue2$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x))))
      (list (list empty invalid-data)
            (list empty invalid-data))))

  (defund queue2$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue2$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         ;;(- (cw "~x0~%" inputs-seq))
         (st (queue2$st-gen data-width)))
      (mv (and (queue2$input-format-n inputs-seq data-width n)
               (queue2$valid-st st data-width))
          state)))

  (defund queue2$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue2$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue2$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (queue2$map-to-links-list
             (de-sim-trace (si 'queue2 data-width)
                           inputs-seq
                           st
                           (queue2$netlist data-width))))
           0)
          state)))

  (defund queue2$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue2$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue2$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-lst
                     (queue2$in-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (queue2$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 2. Q3

(progn
  (defun queue3$map-to-links (st)
    (b* ((l0 (get-field *queue3$l0* st))
         (l1 (get-field *queue3$l1* st))
         (l2 (get-field *queue3$l2* st)))
      (map-to-links (list (cons 'l0 l0)
                          (cons 'l1 l1)
                          (cons 'l2 l2)))))

  (defun queue3$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (queue3$map-to-links (car x))
            (queue3$map-to-links-list (cdr x)))))

  (defund queue3$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x))))
      (list (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data))))

  (defund queue3$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue3$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue3$st-gen data-width)))
      (mv (and (queue3$input-format-n inputs-seq data-width n)
               (queue3$valid-st st data-width))
          state)))

  (defund queue3$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue3$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue3$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (queue3$map-to-links-list
             (de-sim-trace (si 'queue3 data-width)
                           inputs-seq
                           st
                           (queue3$netlist data-width))))
           0)
          state)))

  (defund queue3$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue3$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue3$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-lst
                     (queue3$in-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (queue3$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 3. Q4

(progn
  (defun queue4$map-to-links (st)
    (b* ((l0 (get-field *queue4$l0* st))
         (l1 (get-field *queue4$l1* st))
         (l2 (get-field *queue4$l2* st))
         (l3 (get-field *queue4$l3* st)))
      (map-to-links (list (cons 'l0 l0)
                          (cons 'l1 l1)
                          (cons 'l2 l2)
                          (cons 'l3 l3)))))

  (defun queue4$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (queue4$map-to-links (car x))
            (queue4$map-to-links-list (cdr x)))))

  (defund queue4$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x))))
      (list (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data))))

  (defund queue4$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue4$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue4$st-gen data-width)))
      (mv (and (queue4$input-format-n inputs-seq data-width n)
               (queue4$valid-st st data-width))
          state)))

  (defund queue4$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue4$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue4$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (queue4$map-to-links-list
             (de-sim-trace (si 'queue4 data-width)
                           inputs-seq
                           st
                           (queue4$netlist data-width))))
           0)
          state)))

  (defund queue4$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue4$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue4$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-lst
                     (queue4$in-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (queue4$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 4. Q5

(progn
  (defun queue5$map-to-links (st)
    (b* ((l0 (get-field *queue5$l0* st))
         (l1 (get-field *queue5$l1* st))
         (l2 (get-field *queue5$l2* st))
         (l3 (get-field *queue5$l3* st))
         (l4 (get-field *queue5$l4* st)))
      (map-to-links (list (cons 'l0 l0)
                          (cons 'l1 l1)
                          (cons 'l2 l2)
                          (cons 'l3 l3)
                          (cons 'l4 l4)))))

  (defun queue5$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (queue5$map-to-links (car x))
            (queue5$map-to-links-list (cdr x)))))

  (defund queue5$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x))))
      (list (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data))))

  (defund queue5$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue5$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue5$st-gen data-width)))
      (mv (and (queue5$input-format-n inputs-seq data-width n)
               (queue5$valid-st st data-width))
          state)))

  (defund queue5$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue5$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue5$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (queue5$map-to-links-list
             (de-sim-trace (si 'queue5 data-width)
                           inputs-seq
                           st
                           (queue5$netlist data-width))))
           0)
          state)))

  (defund queue5$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue5$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue5$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-lst
                     (queue5$in-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (queue5$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 5. Q10

(progn
  (defun queue10$map-to-links (st)
    (b* ((l (get-field *queue10$l* st))
         (q4 (get-field *queue10$q4* st))
         (q5 (get-field *queue10$q5* st)))
      (append (list (cons 'q4 (queue4$map-to-links q4)))
              (map-to-links (list (cons 'l l)))
              (list (cons 'q5 (queue5$map-to-links q5))))))

  (defun queue10$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (queue10$map-to-links (car x))
            (queue10$map-to-links-list (cdr x)))))

  (defund queue10$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (q4 (queue4$st-gen data-width))
         (q5 (queue5$st-gen data-width)))
      (list (list empty invalid-data)
            q4 q5)))

  (defund queue10$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue10$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue10$st-gen data-width)))
      (mv (and (queue10$input-format-n inputs-seq data-width n)
               (queue10$valid-st st data-width))
          state)))

  (defund queue10$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue10$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue10$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (queue10$map-to-links-list
             (de-sim-trace (si 'queue10 data-width)
                           inputs-seq
                           st
                           (queue10$netlist data-width))))
           0)
          state)))

  (defund queue10$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue10$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue10$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-lst
                     (queue10$in-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (queue10$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 6. Q3-L

(progn
  (defun queue3-l$map-to-links (st)
    (b* ((l0 (get-field *queue3-l$l0* st))
         (l1 (get-field *queue3-l$l1* st))
         (l2 (get-field *queue3-l$l2* st)))
      (map-to-links (list (cons 'l0 l0)
                          (cons 'l1 l1)
                          (cons 'l2 l2)))))

  (defun queue3-l$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (queue3-l$map-to-links (car x))
            (queue3-l$map-to-links-list (cdr x)))))

  (defund queue3-l$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x))))
      (list (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data))))

  (defund queue3-l$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue3-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue3-l$st-gen data-width)))
      (mv (and (queue3-l$input-format-n inputs-seq st data-width n)
               (queue3-l$valid-st st data-width))
          state)))

  (defund queue3-l$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue3-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue3-l$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (queue3-l$map-to-links-list
             (de-sim-trace (si 'queue3-l data-width)
                           inputs-seq
                           st
                           (queue3-l$netlist data-width))))
           0)
          state)))

  (defund queue3-l$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue3-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue3-l$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-lst
                     (queue3-l$in-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (queue3-l$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 7. Q4-L

(progn
  (defun queue4-l$map-to-links (st)
    (b* ((l0 (get-field *queue4-l$l0* st))
         (l1 (get-field *queue4-l$l1* st))
         (l2 (get-field *queue4-l$l2* st))
         (l3 (get-field *queue4-l$l3* st)))
      (map-to-links (list (cons 'l0 l0)
                          (cons 'l1 l1)
                          (cons 'l2 l2)
                          (cons 'l3 l3)))))

  (defun queue4-l$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (queue4-l$map-to-links (car x))
            (queue4-l$map-to-links-list (cdr x)))))

  (defund queue4-l$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x))))
      (list (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data))))

  (defund queue4-l$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue4-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue4-l$st-gen data-width)))
      (mv (and (queue4-l$input-format-n inputs-seq st data-width n)
               (queue4-l$valid-st st data-width))
          state)))

  (defund queue4-l$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue4-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue4-l$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (queue4-l$map-to-links-list
             (de-sim-trace (si 'queue4-l data-width)
                           inputs-seq
                           st
                           (queue4-l$netlist data-width))))
           0)
          state)))

  (defund queue4-l$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue4-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue4-l$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-lst
                     (queue4-l$in-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (queue4-l$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 8. Q5-L

(progn
  (defun queue5-l$map-to-links (st)
    (b* ((l0 (get-field *queue5-l$l0* st))
         (l1 (get-field *queue5-l$l1* st))
         (l2 (get-field *queue5-l$l2* st))
         (l3 (get-field *queue5-l$l3* st))
         (l4 (get-field *queue5-l$l4* st)))
      (map-to-links (list (cons 'l0 l0)
                          (cons 'l1 l1)
                          (cons 'l2 l2)
                          (cons 'l3 l3)
                          (cons 'l4 l4)))))

  (defun queue5-l$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (queue5-l$map-to-links (car x))
            (queue5-l$map-to-links-list (cdr x)))))

  (defund queue5-l$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x))))
      (list (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data))))

  (defund queue5-l$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue5-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue5-l$st-gen data-width)))
      (mv (and (queue5-l$input-format-n inputs-seq st data-width n)
               (queue5-l$valid-st st data-width))
          state)))

  (defund queue5-l$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue5-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue5-l$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (queue5-l$map-to-links-list
             (de-sim-trace (si 'queue5-l data-width)
                           inputs-seq
                           st
                           (queue5-l$netlist data-width))))
           0)
          state)))

  (defund queue5-l$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue5-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue5-l$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-lst
                     (queue5-l$in-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (queue5-l$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 9. Q8-L

(progn
  (defun queue8-l$map-to-links (st)
    (b* ((q4-l0 (get-field *queue8-l$q4-l0* st))
         (q4-l1 (get-field *queue8-l$q4-l1* st)))
      (append (list (cons 'q4-l0 (queue4-l$map-to-links q4-l0)))
              (list (cons 'q4-l1 (queue4-l$map-to-links q4-l1))))))

  (defun queue8-l$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (queue8-l$map-to-links (car x))
            (queue8-l$map-to-links-list (cdr x)))))

  (defund queue8-l$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((q4-l0 (queue4-l$st-gen data-width))
         (q4-l1 (queue4-l$st-gen data-width)))
      (list q4-l0 q4-l1)))

  (defund queue8-l$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue8-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue8-l$st-gen data-width)))
      (mv (and (queue8-l$input-format-n inputs-seq st data-width n)
               (queue8-l$valid-st st data-width))
          state)))

  (defund queue8-l$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue8-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue8-l$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (queue8-l$map-to-links-list
             (de-sim-trace (si 'queue8-l data-width)
                           inputs-seq
                           st
                           (queue8-l$netlist data-width))))
           0)
          state)))

  (defund queue8-l$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue8-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue8-l$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-lst
                     (queue8-l$in-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (queue8-l$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 10. Q9-L

(progn
  (defun queue9-l$map-to-links (st)
    (b* ((q4-l (get-field *queue9-l$q4-l* st))
         (q5-l (get-field *queue9-l$q5-l* st)))
      (append (list (cons 'q4-l (queue4-l$map-to-links q4-l)))
              (list (cons 'q5-l (queue5-l$map-to-links q5-l))))))

  (defun queue9-l$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (queue9-l$map-to-links (car x))
            (queue9-l$map-to-links-list (cdr x)))))

  (defund queue9-l$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((q4-l (queue4-l$st-gen data-width))
         (q5-l (queue5-l$st-gen data-width)))
      (list q4-l q5-l)))

  (defund queue9-l$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue9-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue9-l$st-gen data-width)))
      (mv (and (queue9-l$input-format-n inputs-seq st data-width n)
               (queue9-l$valid-st st data-width))
          state)))

  (defund queue9-l$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue9-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue9-l$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (queue9-l$map-to-links-list
             (de-sim-trace (si 'queue9-l data-width)
                           inputs-seq
                           st
                           (queue9-l$netlist data-width))))
           0)
          state)))

  (defund queue9-l$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue9-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue9-l$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-lst
                     (queue9-l$in-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (queue9-l$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 11. Q10-L

(progn
  (defun queue10-l$map-to-links (st)
    (b* ((q5-l0 (get-field *queue10-l$q5-l0* st))
         (q5-l1 (get-field *queue10-l$q5-l1* st)))
      (append (list (cons 'q5-l0 (queue5-l$map-to-links q5-l0)))
              (list (cons 'q5-l1 (queue5-l$map-to-links q5-l1))))))

  (defun queue10-l$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (queue10-l$map-to-links (car x))
            (queue10-l$map-to-links-list (cdr x)))))

  (defund queue10-l$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((q5-l0 (queue5-l$st-gen data-width))
         (q5-l1 (queue5-l$st-gen data-width)))
      (list q5-l0 q5-l1)))

  (defund queue10-l$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue10-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue10-l$st-gen data-width)))
      (mv (and (queue10-l$input-format-n inputs-seq st data-width n)
               (queue10-l$valid-st st data-width))
          state)))

  (defund queue10-l$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue10-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue10-l$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (queue10-l$map-to-links-list
             (de-sim-trace (si 'queue10-l data-width)
                           inputs-seq
                           st
                           (queue10-l$netlist data-width))))
           0)
          state)))

  (defund queue10-l$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue10-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue10-l$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-lst
                     (queue10-l$in-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (queue10-l$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 12. Q11-L

(progn
  (defun queue11-l$map-to-links (st)
    (b* ((q3-l (get-field *queue11-l$q3-l* st))
         (q8-l (get-field *queue11-l$q8-l* st)))
      (append (list (cons 'q3-l (queue3-l$map-to-links q3-l)))
              (list (cons 'q8-l (queue8-l$map-to-links q8-l))))))

  (defun queue11-l$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (queue11-l$map-to-links (car x))
            (queue11-l$map-to-links-list (cdr x)))))

  (defund queue11-l$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((q3-l (queue3-l$st-gen data-width))
         (q8-l (queue8-l$st-gen data-width)))
      (list q3-l q8-l)))

  (defund queue11-l$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue11-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue11-l$st-gen data-width)))
      (mv (and (queue11-l$input-format-n inputs-seq st data-width n)
               (queue11-l$valid-st st data-width))
          state)))

  (defund queue11-l$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue11-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue11-l$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (queue11-l$map-to-links-list
             (de-sim-trace (si 'queue11-l data-width)
                           inputs-seq
                           st
                           (queue11-l$netlist data-width))))
           0)
          state)))

  (defund queue11-l$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue11-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue11-l$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-lst
                     (queue11-l$in-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (queue11-l$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 13. Q20-L

(progn
  (defun queue20-l$map-to-links (st)
    (b* ((q10-l0 (get-field *queue20-l$q10-l0* st))
         (q10-l1 (get-field *queue20-l$q10-l1* st)))
      (append (list (cons 'q10-l0 (queue10-l$map-to-links q10-l0)))
              (list (cons 'q10-l1 (queue10-l$map-to-links q10-l1))))))

  (defun queue20-l$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (queue20-l$map-to-links (car x))
            (queue20-l$map-to-links-list (cdr x)))))

  (defund queue20-l$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((q10-l0 (queue10-l$st-gen data-width))
         (q10-l1 (queue10-l$st-gen data-width)))
      (list q10-l0 q10-l1)))

  (defund queue20-l$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue20-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue20-l$st-gen data-width)))
      (mv (and (queue20-l$input-format-n inputs-seq st data-width n)
               (queue20-l$valid-st st data-width))
          state)))

  (defund queue20-l$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue20-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue20-l$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (queue20-l$map-to-links-list
             (de-sim-trace (si 'queue20-l data-width)
                           inputs-seq
                           st
                           (queue20-l$netlist data-width))))
           0)
          state)))

  (defund queue20-l$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue20-l$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (queue20-l$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-lst
                     (queue20-l$in-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (queue20-l$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 14. COMP-V-OR

(progn
  (defun comp-v-or$map-to-links (st)
    (b* ((a0 (get-field *comp-v-or$a0* st))
         (b0 (get-field *comp-v-or$b0* st))
         (a1 (get-field *comp-v-or$a1* st))
         (b1 (get-field *comp-v-or$b1* st))
         (q2 (get-field *comp-v-or$q2* st))
         (q3 (get-field *comp-v-or$q3* st)))
      (append (map-to-links (list (cons 'a0 a0)
                                  (cons 'b0 b0)))
              (cons (cons 'q2 (queue2$map-to-links q2))
                    (cons (cons 'q3 (queue3$map-to-links q3))
                          (map-to-links (list (cons 'a1 a1)
                                              (cons 'b1 b1))))))))

  (defun comp-v-or$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (comp-v-or$map-to-links (car x))
            (comp-v-or$map-to-links-list (cdr x)))))

  (defund comp-v-or$st-gen (data-width)
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

  (defund comp-v-or$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-v-or$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-v-or$st-gen data-width)))
      (mv (and (comp-v-or$input-format-n inputs-seq data-width n)
               (comp-v-or$valid-st st data-width)
               (comp-v-or$inv st))
          state)))

  (defund comp-v-or$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-v-or$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-v-or$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (comp-v-or$map-to-links-list
             (de-sim-trace (si 'comp-v-or data-width)
                           inputs-seq
                           st
                           (comp-v-or$netlist data-width))))
           0)
          state)))

  (defund comp-v-or$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-v-or$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-v-or$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat2-lst
                     (comp-v-or$in-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (comp-v-or$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 15. ALT-MERGE

(progn
  (defun alt-merge$map-to-links (st)
    (b* ((select (get-field *alt-merge$select* st))
         (select-buf (get-field *alt-merge$select-buf* st)))
      (map-to-links1 (list (cons 'select select)
                           (cons 'select-buf select-buf)))))

  (defun alt-merge$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (alt-merge$map-to-links (car x))
            (alt-merge$map-to-links-list (cdr x)))))

  (defund alt-merge$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (alt-merge$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (full '(t))
         (empty '(nil))
         (st (list (list full '(nil))
                   (list empty '(x)))))
      (mv (pretty-list
           (remove-dup-neighbors
            (alt-merge$map-to-links-list
             (de-sim-trace (si 'alt-merge data-width)
                           inputs-seq
                           st
                           (alt-merge$netlist data-width))))
           0)
          state)))
  )

;; 16. ALT-BRANCH

(progn
  (defun alt-branch$map-to-links (st)
    (b* ((select (get-field *alt-branch$select* st))
         (select-buf (get-field *alt-branch$select-buf* st)))
      (map-to-links1 (list (cons 'select select)
                           (cons 'select-buf select-buf)))))

  (defun alt-branch$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (alt-branch$map-to-links (car x))
            (alt-branch$map-to-links-list (cdr x)))))

  (defund alt-branch$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (alt-branch$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (full '(t))
         (empty '(nil))
         (st (list (list full '(nil))
                   (list empty '(x)))))
      (mv (pretty-list
           (remove-dup-neighbors
            (alt-branch$map-to-links-list
             (de-sim-trace (si 'alt-branch data-width)
                           inputs-seq
                           st
                           (alt-branch$netlist data-width))))
           0)
          state)))
  )

;; 17. WW

(progn
  (defun wig-wag$map-to-links (st)
    (b* ((l0 (get-field *wig-wag$l0* st))
         (l1 (get-field *wig-wag$l1* st))
         (br (get-field *wig-wag$br* st))
         (me (get-field *wig-wag$me* st)))
      (append (list (cons 'alt-branch (alt-branch$map-to-links br)))
              (map-to-links (list (cons 'l0 l0)
                                  (cons 'l1 l1)))
              (list (cons 'alt-merge (alt-merge$map-to-links me))))))

  (defun wig-wag$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (wig-wag$map-to-links (car x))
            (wig-wag$map-to-links-list (cdr x)))))

  (defund wig-wag$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((full '(t))
         (empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (br (list (list full '(nil))
                   (list empty '(x))))
         (me (list (list full '(nil))
                   (list empty '(x)))))
      (list (list empty invalid-data)
            (list empty invalid-data)
            br me)))

  (defund wig-wag$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (wig-wag$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (wig-wag$st-gen data-width)))
      (mv (and (wig-wag$input-format-n inputs-seq data-width n)
               (wig-wag$valid-st st data-width)
               (wig-wag$inv st))
          state)))

  (defund wig-wag$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (wig-wag$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (wig-wag$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (wig-wag$map-to-links-list
             (de-sim-trace (si 'wig-wag data-width)
                           inputs-seq
                           st
                           (wig-wag$netlist data-width))))
           0)
          state)))

  (defund wig-wag$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (wig-wag$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (wig-wag$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-lst
                     (wig-wag$in-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (wig-wag$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 18. RR1

(progn
  (defun round-robin1$map-to-links (st)
    (b* ((a0 (get-field *round-robin1$a0* st))
         (b0 (get-field *round-robin1$b0* st))
         (a1 (get-field *round-robin1$a1* st))
         (b1 (get-field *round-robin1$b1* st))
         (q2 (get-field *round-robin1$q2* st))
         (q3 (get-field *round-robin1$q3* st))
         (br (get-field *round-robin1$br* st))
         (me (get-field *round-robin1$me* st)))
      (append (list (cons 'alt-branch (alt-branch$map-to-links br)))
              (map-to-links (list (cons 'a0 a0)
                                  (cons 'b0 b0)))
              (cons (cons 'q2 (queue2$map-to-links q2))
                    (cons (cons 'q3 (queue3$map-to-links q3))
                          (map-to-links (list (cons 'a1 a1)
                                              (cons 'b1 b1)))))
              (list (cons 'alt-merge (alt-merge$map-to-links me))))))

  (defun round-robin1$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (round-robin1$map-to-links (car x))
            (round-robin1$map-to-links-list (cdr x)))))

  (defund round-robin1$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((full '(t))
         (empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (q2 (queue2$st-gen data-width))
         (q3 (queue3$st-gen data-width))
         (br (list (list full '(nil))
                   (list empty '(x))))
         (me (list (list full '(nil))
                   (list empty '(x)))))
      (list (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data)
            (list empty invalid-data)
            q2 q3 br me)))

  (defund round-robin1$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (round-robin1$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (round-robin1$st-gen data-width)))
      (mv (and (round-robin1$input-format-n inputs-seq data-width n)
               (round-robin1$valid-st st data-width)
               (round-robin1$inv st))
          state)))

  (defund round-robin1$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (round-robin1$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (round-robin1$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (round-robin1$map-to-links-list
             (de-sim-trace (si 'round-robin1 data-width)
                           inputs-seq
                           st
                           (round-robin1$netlist data-width))))
           0)
          state)))

  (defund round-robin1$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (round-robin1$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (round-robin1$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-lst
                     (round-robin1$in-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (round-robin1$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 19. RR2

(progn
  (defun round-robin2$map-to-links (st)
    (b* ((q4-l (get-field *round-robin2$q4-l* st))
         (q5-l (get-field *round-robin2$q5-l* st))
         (br (get-field *round-robin2$br* st))
         (me (get-field *round-robin2$me* st)))
      (append (list (cons 'alt-branch (alt-branch$map-to-links br)))
              (list (cons 'q4-l (queue4-l$map-to-links q4-l)))
              (list (cons 'q5-l (queue5-l$map-to-links q5-l)))
              (list (cons 'alt-merge (alt-merge$map-to-links me))))))

  (defun round-robin2$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (round-robin2$map-to-links (car x))
            (round-robin2$map-to-links-list (cdr x)))))

  (defund round-robin2$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((full '(t))
         (empty '(nil))
         (q4-l (queue4-l$st-gen data-width))
         (q5-l (queue5-l$st-gen data-width))
         (br (list (list full '(nil))
                   (list empty '(x))))
         (me (list (list full '(nil))
                   (list empty '(x)))))
      (list q4-l q5-l br me)))

  (defund round-robin2$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (round-robin2$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (round-robin2$st-gen data-width)))
      (mv (and (round-robin2$input-format-n inputs-seq data-width n)
               (round-robin2$valid-st st data-width)
               (round-robin2$inv st))
          state)))

  (defund round-robin2$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (round-robin2$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (round-robin2$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (round-robin2$map-to-links-list
             (de-sim-trace (si 'round-robin2 data-width)
                           inputs-seq
                           st
                           (round-robin2$netlist data-width))))
           0)
          state)))

  (defund round-robin2$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (round-robin2$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (round-robin2$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-lst
                     (round-robin2$in-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (round-robin2$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 20. RR3

(progn
  (defun round-robin3$map-to-links (st)
    (b* ((q8-l (get-field *round-robin3$q8-l* st))
         (q10-l (get-field *round-robin3$q10-l* st))
         (br (get-field *round-robin3$br* st))
         (me (get-field *round-robin3$me* st)))
      (append (list (cons 'alt-branch (alt-branch$map-to-links br)))
              (list (cons 'q8-l (queue8-l$map-to-links q8-l)))
              (list (cons 'q10-l (queue10-l$map-to-links q10-l)))
              (list (cons 'alt-merge (alt-merge$map-to-links me))))))

  (defun round-robin3$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (round-robin3$map-to-links (car x))
            (round-robin3$map-to-links-list (cdr x)))))

  (defund round-robin3$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((full '(t))
         (empty '(nil))
         (q8-l (queue8-l$st-gen data-width))
         (q10-l (queue10-l$st-gen data-width))
         (br (list (list full '(nil))
                   (list empty '(x))))
         (me (list (list full '(nil))
                   (list empty '(x)))))
      (list q8-l q10-l br me)))

  (defund round-robin3$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (round-robin3$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (round-robin3$st-gen data-width)))
      (mv (and (round-robin3$input-format-n inputs-seq data-width n)
               (round-robin3$valid-st st data-width)
               (round-robin3$inv st))
          state)))

  (defund round-robin3$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (round-robin3$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (round-robin3$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (round-robin3$map-to-links-list
             (de-sim-trace (si 'round-robin3 data-width)
                           inputs-seq
                           st
                           (round-robin3$netlist data-width))))
           0)
          state)))

  (defund round-robin3$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (round-robin3$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (round-robin3$st-gen data-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-lst
                     (round-robin3$in-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (round-robin3$out-seq inputs-seq st data-width n)))))
       state)))
  )


