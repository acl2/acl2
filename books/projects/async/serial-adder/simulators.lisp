;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "piso-sreg")
(include-book "serial-add")
(include-book "serial-sub")

;; ======================================================================

;;; Simulators for:
;;;
;;; 1. PISO-SREG
;;; 2. PISO2-SREG
;;; 3. SIPO-SREG
;;; 4. SERIAL-ADD
;;; 5. SERIAL-SUB

;; ======================================================================

;; 1. PISO-SREG

(progn
  (defun piso-sreg$map-to-links (st)
    (b* ((r-data (nth *piso-sreg$r-data* st))
         (r-cnt (nth *piso-sreg$r-cnt* st))
         (w-data (nth *piso-sreg$w-data* st))
         (w-cnt (nth *piso-sreg$w-cnt* st)))
      (map-to-links (list (cons 'r-data r-data)
                          (cons 'r-cnt r-cnt)
                          (cons 'w-data w-data)
                          (cons 'w-cnt w-cnt)))))

  (defun piso-sreg$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (piso-sreg$map-to-links (car x))
            (piso-sreg$map-to-links-list (cdr x)))))

  (defund piso-sreg$st-gen (data-size cnt-size)
    (declare (xargs :guard (and (natp data-size)
                                (natp cnt-size))))
    (b* ((full '(t))
         (empty '(nil))
         (invalid-data (make-list data-size :initial-element '(x)))
         (zero-data (make-list data-size :initial-element '(nil)))
         (invalid-cnt (make-list cnt-size :initial-element '(x)))
         (zero-cnt (make-list cnt-size :initial-element '(nil))))
      (list (list full zero-data)
            (list full zero-cnt)
            (list empty invalid-data)
            (list empty invalid-cnt))))

  (defund piso-sreg$ins-and-st-test (data-size cnt-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp cnt-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (piso-sreg$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (piso-sreg$st-gen data-size cnt-size)))
      (mv (and (piso-sreg$input-format-n inputs-seq data-size n)
               (piso-sreg$valid-st st data-size cnt-size)
               (piso-sreg$inv st))
          state)))

  (local
   (defthm piso-sreg$ins-and-st-test-ok
     (piso-sreg$ins-and-st-test 4 3 10 state)))

  (defund piso-sreg$sim (data-size cnt-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp cnt-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (piso-sreg$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (piso-sreg$st-gen data-size cnt-size)))
      (mv (pretty-list
           (remove-dup-neighbors
            (piso-sreg$map-to-links-list
             (de-sim-trace (si 'piso-sreg data-size)
                           inputs-seq
                           st
                           (piso-sreg$netlist data-size cnt-size))))
           0)
          state)))

  (defund piso-sreg$in-out-sim (data-size cnt-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp cnt-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (piso-sreg$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (piso-sreg$st-gen data-size cnt-size)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-lst
                     (piso-sreg$in-seq
                      inputs-seq st data-size cnt-size n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (pairlis$
                      (piso-sreg$out-seq
                       inputs-seq st data-size cnt-size n)
                      nil)))))
       state)))
  )

;; 2. PISO2-SREG

(progn
  (defun piso2-sreg$map-to-links (st)
    (b* ((r-data0 (nth *piso2-sreg$r-data0* st))
         (r-cnt0 (nth *piso2-sreg$r-cnt0* st))
         (w-data0 (nth *piso2-sreg$w-data0* st))
         (w-cnt0 (nth *piso2-sreg$w-cnt0* st))
         (r-data1 (nth *piso2-sreg$r-data1* st))
         (r-cnt1 (nth *piso2-sreg$r-cnt1* st))
         (w-data1 (nth *piso2-sreg$w-data1* st))
         (w-cnt1 (nth *piso2-sreg$w-cnt1* st)))
      (map-to-links (list (cons 'r-data0 r-data0)
                          (cons 'r-cnt0 r-cnt0)
                          (cons 'w-data0 w-data0)
                          (cons 'w-cnt0 w-cnt0)
                          (cons 'r-data1 r-data1)
                          (cons 'r-cnt1 r-cnt1)
                          (cons 'w-data1 w-data1)
                          (cons 'w-cnt1 w-cnt1)))))

  (defun piso2-sreg$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (piso2-sreg$map-to-links (car x))
            (piso2-sreg$map-to-links-list (cdr x)))))

  (defund piso2-sreg$st-gen (data-size cnt-size)
    (declare (xargs :guard (and (natp data-size)
                                (natp cnt-size))))
    (b* ((full '(t))
         (empty '(nil))
         (invalid-data (make-list data-size :initial-element '(x)))
         (zero-data (make-list data-size :initial-element '(nil)))
         (invalid-cnt (make-list cnt-size :initial-element '(x)))
         (zero-cnt (make-list cnt-size :initial-element '(nil))))
      (list (list full zero-data)
            (list full zero-cnt)
            (list empty invalid-data)
            (list empty invalid-cnt)
            (list full zero-data)
            (list full zero-cnt)
            (list empty invalid-data)
            (list empty invalid-cnt))))

  (defund piso2-sreg$ins-and-st-test (data-size cnt-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp cnt-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (piso2-sreg$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (piso2-sreg$st-gen data-size cnt-size)))
      (mv (and (piso2-sreg$input-format-n inputs-seq data-size n)
               (piso2-sreg$valid-st st data-size cnt-size)
               (piso2-sreg$inv st))
          state)))

  (local
   (defthm piso2-sreg$ins-and-st-test-ok
     (piso2-sreg$ins-and-st-test 4 3 10 state)))

  (defund piso2-sreg$sim (data-size cnt-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp cnt-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (piso2-sreg$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (piso2-sreg$st-gen data-size cnt-size)))
      (mv (pretty-list
           (remove-dup-neighbors
            (piso2-sreg$map-to-links-list
             (de-sim-trace (si 'piso2-sreg data-size)
                           inputs-seq
                           st
                           (piso2-sreg$netlist data-size cnt-size))))
           0)
          state)))

  (defund piso2-sreg$in-out-sim (data-size cnt-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (natp cnt-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (piso2-sreg$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (piso2-sreg$st-gen data-size cnt-size)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat2-lst
                     (piso2-sreg$in-seq
                      inputs-seq st data-size cnt-size n))))
        (list (cons 'out0-seq
                    (v-to-nat-lst
                     (pairlis$
                      (piso2-sreg$out0-seq
                       inputs-seq st data-size cnt-size n)
                      nil))))
        (list (cons 'out1-seq
                    (v-to-nat-lst
                     (pairlis$
                      (piso2-sreg$out1-seq
                       inputs-seq st data-size cnt-size n)
                      nil)))))
       state)))
  )

;; 3. SIPO-SREG

(progn
  (defun sipo-sreg$map-to-links (st)
    (b* ((r-data (nth *sipo-sreg$r-data* st))
         (r-cnt (nth *sipo-sreg$r-cnt* st))
         (w-data (nth *sipo-sreg$w-data* st))
         (w-cnt (nth *sipo-sreg$w-cnt* st)))
      (map-to-links (list (cons 'r-data r-data)
                          (cons 'r-cnt r-cnt)
                          (cons 'w-data w-data)
                          (cons 'w-cnt w-cnt)))))

  (defun sipo-sreg$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (sipo-sreg$map-to-links (car x))
            (sipo-sreg$map-to-links-list (cdr x)))))

  (defund sipo-sreg$st-gen (data-size cnt-size)
    (declare (xargs :guard (and (natp data-size)
                                (posp cnt-size))))
    (b* ((full '(t))
         (empty '(nil))
         (invalid-data (make-list data-size :initial-element '(x)))
         (zero-data (make-list data-size :initial-element '(nil)))
         (invalid-cnt (make-list cnt-size :initial-element '(x)))
         (full-cnt (append (make-list (1- cnt-size) :initial-element '(nil))
                           '((t)))))
      (list (list full zero-data)
            (list full full-cnt)
            (list empty invalid-data)
            (list empty invalid-cnt))))

  (defund sipo-sreg$ins-and-st-test (data-size cnt-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (posp cnt-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals *sipo-sreg$ins-len*)
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (sipo-sreg$st-gen data-size cnt-size)))
      (mv (and (sipo-sreg$input-format-n inputs-seq n)
               (sipo-sreg$valid-st st data-size cnt-size)
               (sipo-sreg$inv st))
          state)))

  (local
   (defthm sipo-sreg$ins-and-st-test-ok
     (sipo-sreg$ins-and-st-test 4 3 10 state)))

  (defund sipo-sreg$sim (data-size cnt-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (posp cnt-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals *sipo-sreg$ins-len*)
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (sipo-sreg$st-gen data-size cnt-size)))
      (mv (pretty-list
           (remove-dup-neighbors
            (sipo-sreg$map-to-links-list
             (de-sim-trace (si 'sipo-sreg data-size)
                           inputs-seq
                           st
                           (sipo-sreg$netlist data-size cnt-size))))
           0)
          state)))

  (defund sipo-sreg$in-out-sim (data-size cnt-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (posp cnt-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals *sipo-sreg$ins-len*)
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (sipo-sreg$st-gen data-size cnt-size)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-lst
                     (pairlis$
                      (sipo-sreg$in-seq
                       inputs-seq st data-size cnt-size n)
                      nil))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (sipo-sreg$out-seq
                      inputs-seq st data-size cnt-size n)))))
       state)))
  )

;; 4. SERIAL-ADD

(progn
  (defun serial-add$map-to-links (st)
    (b* ((a (nth *serial-add$a* st))
         (b (nth *serial-add$b* st))
         (ci (nth *serial-add$ci* st))
         (s (nth *serial-add$s* st))
         (co (nth *serial-add$co* st))
         (done (nth *serial-add$done* st))
         (piso2 (nth *serial-add$piso2* st))
         (sipo (nth *serial-add$sipo* st)))
      (append
       (list (cons 'piso2 (piso2-sreg$map-to-links piso2)))
       (map-to-links1 (list (cons 'a a)
                            (cons 'b b)
                            (cons 'ci ci)
                            (cons 's s)
                            (cons 'co co)
                            (cons 'done done)))
       (list (cons 'sipo (sipo-sreg$map-to-links sipo))))))

  (defun serial-add$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (serial-add$map-to-links (car x))
            (serial-add$map-to-links-list (cdr x)))))

  (defund serial-add$st-gen (data-size cnt-size)
    (declare (xargs :guard (and (natp data-size)
                                (posp cnt-size))))
    (b* ((full '(t))
         (empty '(nil))
         (a (list empty '(nil)))
         (b (list empty '(nil)))
         (ci (list full '(nil)))
         (s (list empty '(nil)))
         (co (list empty '(nil)))
         (done (list empty '(nil)))
         (piso2 (piso2-sreg$st-gen data-size cnt-size))
         (sipo (sipo-sreg$st-gen data-size cnt-size)))
      (list a b ci s co done piso2 sipo)))

  (defund serial-add$ins-and-st-test (data-size cnt-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (posp cnt-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (serial-add$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (serial-add$st-gen data-size cnt-size)))
      (mv (and (serial-add$input-format-n inputs-seq data-size n)
               (serial-add$valid-st st data-size cnt-size)
               (serial-add$inv st data-size))
          state)))

  (local
   (defthm serial-add$ins-and-st-test-ok
     (serial-add$ins-and-st-test 4 3 10 state)))

  (defund serial-add$sim (data-size cnt-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (posp cnt-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (serial-add$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (serial-add$st-gen data-size cnt-size)))
      (mv (pretty-list
           (remove-dup-neighbors
            (serial-add$map-to-links-list
             (de-sim-trace (si 'serial-add data-size)
                           inputs-seq
                           st
                           (serial-add$netlist data-size cnt-size))))
           0)
          state)))

  (defund serial-add$in-out-sim (data-size cnt-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (posp cnt-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (serial-add$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (serial-add$st-gen data-size cnt-size)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat2-lst
                     (serial-add$in-seq
                      inputs-seq st data-size cnt-size n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (serial-add$out-seq
                      inputs-seq st data-size cnt-size n)))))
       state)))
  )

;; 5. SERIAL-SUB

(progn
  (defun serial-sub$map-to-links (st)
    (b* ((a (nth *serial-sub$a* st))
         (b (nth *serial-sub$b* st))
         (ci (nth *serial-sub$ci* st))
         (s (nth *serial-sub$s* st))
         (co (nth *serial-sub$co* st))
         (done (nth *serial-sub$done* st))
         (piso2 (nth *serial-sub$piso2* st))
         (sipo (nth *serial-sub$sipo* st)))
      (append
       (list (cons 'piso2 (piso2-sreg$map-to-links piso2)))
       (map-to-links1 (list (cons 'a a)
                            (cons 'b b)
                            (cons 'ci ci)
                            (cons 's s)
                            (cons 'co co)
                            (cons 'done done)))
       (list (cons 'sipo (sipo-sreg$map-to-links sipo))))))

  (defun serial-sub$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (serial-sub$map-to-links (car x))
            (serial-sub$map-to-links-list (cdr x)))))

  (defund serial-sub$st-gen (data-size cnt-size)
    (declare (xargs :guard (and (natp data-size)
                                (posp cnt-size))))
    (b* ((full '(t))
         (empty '(nil))
         (a (list empty '(nil)))
         (b (list empty '(nil)))
         (ci (list full '(t)))
         (s (list empty '(nil)))
         (co (list empty '(nil)))
         (done (list empty '(nil)))
         (piso2 (piso2-sreg$st-gen data-size cnt-size))
         (sipo (sipo-sreg$st-gen data-size cnt-size)))
      (list a b ci s co done piso2 sipo)))

  (defund serial-sub$ins-and-st-test (data-size cnt-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (posp cnt-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (serial-sub$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (serial-sub$st-gen data-size cnt-size)))
      (mv (and (serial-sub$input-format-n inputs-seq data-size n)
               (serial-sub$valid-st st data-size cnt-size)
               (serial-sub$inv st data-size))
          state)))

  (local
   (defthm serial-sub$ins-and-st-test-ok
     (serial-sub$ins-and-st-test 4 3 10 state)))

  (defund serial-sub$sim (data-size cnt-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (posp cnt-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (serial-sub$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (serial-sub$st-gen data-size cnt-size)))
      (mv (pretty-list
           (remove-dup-neighbors
            (serial-sub$map-to-links-list
             (de-sim-trace (si 'serial-sub data-size)
                           inputs-seq
                           st
                           (serial-sub$netlist data-size cnt-size))))
           0)
          state)))

  (defund serial-sub$in-out-sim (data-size cnt-size n state)
    (declare (xargs :guard (and (natp data-size)
                                (posp cnt-size)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (serial-sub$ins-len data-size))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (serial-sub$st-gen data-size cnt-size)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat2-lst
                     (serial-sub$in-seq
                      inputs-seq st data-size cnt-size n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (serial-sub$out-seq
                      inputs-seq st data-size cnt-size n)))))
       state)))
  )


