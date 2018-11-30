;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; November 2018

(in-package "ADE")

(include-book "comp-interl")
(include-book "igcd")
(include-book "interl-ll")
(include-book "../fifo/simulators")
(include-book "../gcd/simulators")

;; ======================================================================

;;; Simulators for:
;;;
;;; 1. ARB-MERGE
;;; 2. INTERL
;;; 3. INTERL-LL
;;; 4. IGCD
;;; 5. COMP-INTERL

;; ======================================================================

;; 1. ARB-MERGE

(progn
  (defun arb-merge$map-to-links (st)
    (b* ((arb (get-field *arb-merge$arb* st))
         (arb-buf (get-field *arb-merge$arb-buf* st)))
      (map-to-links (list (cons 'arb arb)
                          (cons 'arb-buf arb-buf)))))

  (defun arb-merge$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (arb-merge$map-to-links (car x))
            (arb-merge$map-to-links-list (cdr x)))))

  (defund arb-merge$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (arb-merge$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (full '(t))
         (empty '(nil))
         (st (list (list full '((nil) (nil)))
                   (list empty '((x) (x))))))
      (mv (pretty-list
           (remove-dup-neighbors
            (arb-merge$map-to-links-list
             (de-sim-trace (si 'arb-merge data-width)
                           inputs-seq
                           st
                           (arb-merge$netlist data-width))))
           0)
          state)))
  )

;; 2. INTERL

(progn
  (defun interl$map-to-links (st)
    (b* ((q20-l0 (get-field *interl$q20-l0* st))
         (q20-l1 (get-field *interl$q20-l1* st))
         ;; (arb-merge (get-field *interl$arb-merge* st))
         )
      (append (list (cons 'q20-l0 (queue20-l$map-to-links q20-l0)))
              (list (cons 'q20-l1 (queue20-l$map-to-links q20-l1)))
              ;; (list (cons 'arb-merge (arb-merge$map-to-links arb-merge)))
              )))

  (defun interl$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (interl$map-to-links (car x))
            (interl$map-to-links-list (cdr x)))))

  (defund interl$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* (;; (full '(t))
         ;; (empty '(nil))
         (q20-l0 (queue20-l$st-gen data-width))
         (q20-l1 (queue20-l$st-gen data-width))
         ;; (arb-merge (list (list full '((nil) (nil)))
         ;;                  (list empty '((x) (x)))))
         )
      (list q20-l0 q20-l1 ;; arb-merge
            )))

  (defund interl$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (interl$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (interl$st-gen data-width)))
      (mv (and (interl$input-format-n inputs-seq data-width n)
               (interl$valid-st st data-width))
          state)))

  (defund interl$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (interl$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (interl$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (interl$map-to-links-list
             (de-sim-trace (si 'interl data-width)
                           inputs-seq
                           st
                           (interl$netlist data-width))))
           0)
          state)))

  (defund interl$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (interl$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (interl$st-gen data-width)))
      (mv
       (append
        (list (cons 'in0-seq
                    (v-to-nat-lst
                     (interl$in0-seq inputs-seq st data-width n))))
        (list (cons 'in1-seq
                    (v-to-nat-lst
                     (interl$in1-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (interl$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 3. INTERL-LL

(progn
  (defun interl-ll$map-to-links (st)
    (b* ((q9-l (get-field *interl-ll$q9-l* st))
         (q11-l (get-field *interl-ll$q11-l* st))
         (arb-merge (get-field *interl-ll$arb-merge* st)))
      (append (list (cons 'q9-l (queue9-l$map-to-links q9-l)))
              (list (cons 'q11-l (queue11-l$map-to-links q11-l)))
              (list (cons 'arb-merge (arb-merge$map-to-links arb-merge))))))

  (defun interl-ll$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (interl-ll$map-to-links (car x))
            (interl-ll$map-to-links-list (cdr x)))))

  (defund interl-ll$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((full '(t))
         (empty '(nil))
         (q9-l (queue9-l$st-gen data-width))
         (q11-l (queue11-l$st-gen data-width))
         (arb-merge (list (list full '((nil) (nil)))
                          (list empty '((x) (x))))))
      (list q9-l q11-l arb-merge)))

  (defund interl-ll$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (interl-ll$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (interl-ll$st-gen data-width)))
      (mv (and (interl-ll$input-format-n inputs-seq st data-width n)
               (interl-ll$valid-st st data-width))
          state)))

  (defund interl-ll$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (interl-ll$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (interl-ll$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (interl-ll$map-to-links-list
             (de-sim-trace (si 'interl-ll data-width)
                           inputs-seq
                           st
                           (interl-ll$netlist data-width))))
           0)
          state)))

  (defund interl-ll$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (interl-ll$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (interl-ll$st-gen data-width)))
      (mv
       (append
        (list (cons 'in0-seq
                    (v-to-nat-lst
                     (interl-ll$in0-seq inputs-seq st data-width n))))
        (list (cons 'in1-seq
                    (v-to-nat-lst
                     (interl-ll$in1-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (interl-ll$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 4. IGCD

(progn
  (defun igcd$map-to-links (st)
    (b* ((l (get-field *igcd$l* st))
         (interl (get-field *igcd$interl* st))
         (gcd (get-field *igcd$gcd* st)))
      (append (list (cons 'interl (interl$map-to-links interl)))
              (map-to-links (list (cons 'l l)))
              (list (cons 'gcd (gcd$map-to-links gcd))))))

  (defun igcd$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (igcd$map-to-links (car x))
            (igcd$map-to-links-list (cdr x)))))

  (defund igcd$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((empty '(nil))
         (invalid-data (make-list (* 2 data-width) :initial-element '(x)))
         (interl (interl$st-gen (* 2 data-width)))
         (gcd (gcd$st-gen data-width)))
      (list (list empty invalid-data) interl gcd)))

  (defund igcd$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (igcd$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (igcd$st-gen data-width)))
      (mv (and (igcd$input-format-n inputs-seq data-width n)
               (igcd$valid-st st data-width)
               (igcd$inv st))
          state)))

  (defund igcd$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (igcd$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (igcd$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (igcd$map-to-links-list
             (de-sim-trace (si 'igcd data-width)
                           inputs-seq
                           st
                           (igcd$netlist data-width))))
           0)
          state)))

  (defund igcd$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (igcd$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (igcd$st-gen data-width)))
      (mv
       (append
        (list (cons 'in0-seq
                    (v-to-nat-lst
                     (igcd$in0-seq inputs-seq st data-width n))))
        (list (cons 'in1-seq
                    (v-to-nat-lst
                     (igcd$in1-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (igcd$out-seq inputs-seq st data-width n)))))
       state)))
  )

;; 5. COMP-INTERL

(progn
  (defun comp-interl$map-to-links (st)
    (b* ((l0 (get-field *comp-interl$l0* st))
         (l1 (get-field *comp-interl$l1* st))
         (interl0 (get-field *comp-interl$interl0* st))
         (interl1 (get-field *comp-interl$interl1* st))
         (interl2 (get-field *comp-interl$interl2* st)))
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

  (defund comp-interl$st-gen (data-width)
    (declare (xargs :guard (natp data-width)))
    (b* ((empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (interl0 (interl$st-gen data-width))
         (interl1 (interl$st-gen data-width))
         (interl2 (interl$st-gen data-width)))
      (list (list empty invalid-data)
            (list empty invalid-data)
            interl0 interl1 interl2)))

  (defund comp-interl$ins-and-st-test (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-interl$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-interl$st-gen data-width)))
      (mv (and (comp-interl$input-format-n inputs-seq data-width n)
               (comp-interl$valid-st st data-width))
          state)))

  (defund comp-interl$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-interl$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-interl$st-gen data-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (comp-interl$map-to-links-list
             (de-sim-trace (si 'comp-interl data-width)
                           inputs-seq
                           st
                           (comp-interl$netlist data-width))))
           0)
          state)))

  (defund comp-interl$in-out-sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (comp-interl$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (comp-interl$st-gen data-width)))
      (mv
       (append
        (list (cons 'in0-seq
                    (v-to-nat-lst
                     (comp-interl$in0-seq inputs-seq st data-width n))))
        (list (cons 'in1-seq
                    (v-to-nat-lst
                     (comp-interl$in1-seq inputs-seq st data-width n))))
        (list (cons 'in2-seq
                    (v-to-nat-lst
                     (comp-interl$in2-seq inputs-seq st data-width n))))
        (list (cons 'in3-seq
                    (v-to-nat-lst
                     (comp-interl$in3-seq inputs-seq st data-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (comp-interl$out-seq inputs-seq st data-width n)))))
       state)))
  )


