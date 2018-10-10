;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2018

(in-package "ADE")

(include-book "serial-add")
(include-book "serial-sub")
(include-book "shift-register-piso")

;; ======================================================================

;;; Simulators for:
;;;
;;; 1. SHIFT-REGISTER-PISO
;;; 2. SHIFT-REGISTER2-PISO
;;; 3. SHIFT-REGISTER-SIPO
;;; 4. SERIAL-ADD
;;; 5. SERIAL-SUB

;; ======================================================================

;; 1. SHIFT-REGISTER-PISO

(progn
  (defun shift-register-piso$map-to-links (st)
    (b* ((r-reg (get-field *shift-register-piso$r-reg* st))
         (r-cnt (get-field *shift-register-piso$r-cnt* st))
         (w-reg (get-field *shift-register-piso$w-reg* st))
         (w-cnt (get-field *shift-register-piso$w-cnt* st)))
      (map-to-links (list (cons 'r-reg r-reg)
                          (cons 'r-cnt r-cnt)
                          (cons 'w-reg w-reg)
                          (cons 'w-cnt w-cnt)))))

  (defun shift-register-piso$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (shift-register-piso$map-to-links (car x))
            (shift-register-piso$map-to-links-list (cdr x)))))

  (defund shift-register-piso$st-gen (data-width cnt-width)
    (declare (xargs :guard (and (natp data-width)
                                (natp cnt-width))))
    (b* ((full '(t))
         (empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (zero-data (make-list data-width :initial-element '(nil)))
         (invalid-cnt (make-list cnt-width :initial-element '(x)))
         (zero-cnt (make-list cnt-width :initial-element '(nil))))
      (list (list full zero-data)
            (list full zero-cnt)
            (list empty invalid-data)
            (list empty invalid-cnt))))

  (defund shift-register-piso$ins-and-st-test (data-width cnt-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp cnt-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (shift-register-piso$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (shift-register-piso$st-gen data-width cnt-width)))
      (mv (and (shift-register-piso$input-format-n inputs-seq data-width n)
               (shift-register-piso$valid-st st data-width cnt-width)
               (shift-register-piso$inv st))
          state)))

  (defund shift-register-piso$sim (data-width cnt-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp cnt-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (shift-register-piso$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (shift-register-piso$st-gen data-width cnt-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (shift-register-piso$map-to-links-list
             (de-sim-trace (si 'shift-register-piso data-width)
                           inputs-seq
                           st
                           (shift-register-piso$netlist data-width cnt-width))))
           0)
          state)))

  (defund shift-register-piso$in-out-sim (data-width cnt-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp cnt-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (shift-register-piso$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (shift-register-piso$st-gen data-width cnt-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-lst
                     (shift-register-piso$in-seq
                      inputs-seq st data-width cnt-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (pairlis$
                      (shift-register-piso$out-seq
                       inputs-seq st data-width cnt-width n)
                      nil)))))
       state)))
  )

;; 2. SHIFT-REGISTER2-PISO

(progn
  (defun shift-register2-piso$map-to-links (st)
    (b* ((r-reg0 (get-field *shift-register2-piso$r-reg0* st))
         (r-cnt0 (get-field *shift-register2-piso$r-cnt0* st))
         (w-reg0 (get-field *shift-register2-piso$w-reg0* st))
         (w-cnt0 (get-field *shift-register2-piso$w-cnt0* st))
         (r-reg1 (get-field *shift-register2-piso$r-reg1* st))
         (r-cnt1 (get-field *shift-register2-piso$r-cnt1* st))
         (w-reg1 (get-field *shift-register2-piso$w-reg1* st))
         (w-cnt1 (get-field *shift-register2-piso$w-cnt1* st)))
      (map-to-links (list (cons 'r-reg0 r-reg0)
                          (cons 'r-cnt0 r-cnt0)
                          (cons 'w-reg0 w-reg0)
                          (cons 'w-cnt0 w-cnt0)
                          (cons 'r-reg1 r-reg1)
                          (cons 'r-cnt1 r-cnt1)
                          (cons 'w-reg1 w-reg1)
                          (cons 'w-cnt1 w-cnt1)))))

  (defun shift-register2-piso$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (shift-register2-piso$map-to-links (car x))
            (shift-register2-piso$map-to-links-list (cdr x)))))

  (defund shift-register2-piso$st-gen (data-width cnt-width)
    (declare (xargs :guard (and (natp data-width)
                                (natp cnt-width))))
    (b* ((full '(t))
         (empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (zero-data (make-list data-width :initial-element '(nil)))
         (invalid-cnt (make-list cnt-width :initial-element '(x)))
         (zero-cnt (make-list cnt-width :initial-element '(nil))))
      (list (list full zero-data)
            (list full zero-cnt)
            (list empty invalid-data)
            (list empty invalid-cnt)
            (list full zero-data)
            (list full zero-cnt)
            (list empty invalid-data)
            (list empty invalid-cnt))))

  (defund shift-register2-piso$ins-and-st-test (data-width cnt-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp cnt-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (shift-register2-piso$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (shift-register2-piso$st-gen data-width cnt-width)))
      (mv (and (shift-register2-piso$input-format-n inputs-seq data-width n)
               (shift-register2-piso$valid-st st data-width cnt-width)
               (shift-register2-piso$inv st))
          state)))

  (defund shift-register2-piso$sim (data-width cnt-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp cnt-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (shift-register2-piso$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (shift-register2-piso$st-gen data-width cnt-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (shift-register2-piso$map-to-links-list
             (de-sim-trace (si 'shift-register2-piso data-width)
                           inputs-seq
                           st
                           (shift-register2-piso$netlist data-width cnt-width))))
           0)
          state)))

  (defund shift-register2-piso$in-out-sim (data-width cnt-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp cnt-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (shift-register2-piso$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (shift-register2-piso$st-gen data-width cnt-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat2-lst
                     (shift-register2-piso$in-seq
                      inputs-seq st data-width cnt-width n))))
        (list (cons 'out0-seq
                    (v-to-nat-lst
                     (pairlis$
                      (shift-register2-piso$out0-seq
                       inputs-seq st data-width cnt-width n)
                      nil))))
        (list (cons 'out1-seq
                    (v-to-nat-lst
                     (pairlis$
                      (shift-register2-piso$out1-seq
                       inputs-seq st data-width cnt-width n)
                      nil)))))
       state)))
  )

;; 3. SHIFT-REGISTER-SIPO

(progn
  (defun shift-register-sipo$map-to-links (st)
    (b* ((r-reg (get-field *shift-register-sipo$r-reg* st))
         (r-cnt (get-field *shift-register-sipo$r-cnt* st))
         (w-reg (get-field *shift-register-sipo$w-reg* st))
         (w-cnt (get-field *shift-register-sipo$w-cnt* st)))
      (map-to-links (list (cons 'r-reg r-reg)
                          (cons 'r-cnt r-cnt)
                          (cons 'w-reg w-reg)
                          (cons 'w-cnt w-cnt)))))

  (defun shift-register-sipo$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (shift-register-sipo$map-to-links (car x))
            (shift-register-sipo$map-to-links-list (cdr x)))))

  (defund shift-register-sipo$st-gen (data-width cnt-width)
    (declare (xargs :guard (and (natp data-width)
                                (posp cnt-width))))
    (b* ((full '(t))
         (empty '(nil))
         (invalid-data (make-list data-width :initial-element '(x)))
         (zero-data (make-list data-width :initial-element '(nil)))
         (invalid-cnt (make-list cnt-width :initial-element '(x)))
         (full-cnt (append (make-list (1- cnt-width) :initial-element '(nil))
                           '((t)))))
      (list (list full zero-data)
            (list full full-cnt)
            (list empty invalid-data)
            (list empty invalid-cnt))))

  (defund shift-register-sipo$ins-and-st-test (data-width cnt-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (posp cnt-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals *shift-register-sipo$ins-len*)
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (shift-register-sipo$st-gen data-width cnt-width)))
      (mv (and (shift-register-sipo$input-format-n inputs-seq n)
               (shift-register-sipo$valid-st st data-width cnt-width)
               (shift-register-sipo$inv st))
          state)))

  (defund shift-register-sipo$sim (data-width cnt-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (posp cnt-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals *shift-register-sipo$ins-len*)
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (shift-register-sipo$st-gen data-width cnt-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (shift-register-sipo$map-to-links-list
             (de-sim-trace (si 'shift-register-sipo data-width)
                           inputs-seq
                           st
                           (shift-register-sipo$netlist data-width cnt-width))))
           0)
          state)))

  (defund shift-register-sipo$in-out-sim (data-width cnt-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (posp cnt-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals *shift-register-sipo$ins-len*)
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (shift-register-sipo$st-gen data-width cnt-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat-lst
                     (pairlis$
                      (shift-register-sipo$in-seq
                       inputs-seq st data-width cnt-width n)
                      nil))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (shift-register-sipo$out-seq
                      inputs-seq st data-width cnt-width n)))))
       state)))
  )

;; 4. SERIAL-ADD

(progn
  (defun serial-add$map-to-links (st)
    (b* ((a (get-field *serial-add$a* st))
         (b (get-field *serial-add$b* st))
         (ci (get-field *serial-add$ci* st))
         (s (get-field *serial-add$s* st))
         (co (get-field *serial-add$co* st))
         (done (get-field *serial-add$done* st))
         (sregs2 (get-field *serial-add$sregs2* st))
         (sreg (get-field *serial-add$sreg* st)))
      (append
       (list (cons 'sregs2 (shift-register2-piso$map-to-links sregs2)))
       (map-to-links1 (list (cons 'a a)
                            (cons 'b b)
                            (cons 'ci ci)
                            (cons 's s)
                            (cons 'co co)
                            (cons 'done done)))
       (list (cons 'sreg (shift-register-sipo$map-to-links sreg))))))

  (defun serial-add$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (serial-add$map-to-links (car x))
            (serial-add$map-to-links-list (cdr x)))))

  (defund serial-add$st-gen (data-width cnt-width)
    (declare (xargs :guard (and (natp data-width)
                                (posp cnt-width))))
    (b* ((full '(t))
         (empty '(nil))
         (a (list empty '(nil)))
         (b (list empty '(nil)))
         (ci (list full '(nil)))
         (s (list empty '(nil)))
         (co (list empty '(nil)))
         (done (list empty '(nil)))
         (sregs2 (shift-register2-piso$st-gen data-width cnt-width))
         (sreg (shift-register-sipo$st-gen data-width cnt-width)))
      (list a b ci s co done sregs2 sreg)))

  (defund serial-add$ins-and-st-test (data-width cnt-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (posp cnt-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (serial-add$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (serial-add$st-gen data-width cnt-width)))
      (mv (and (serial-add$input-format-n inputs-seq data-width n)
               (serial-add$valid-st st data-width cnt-width)
               (serial-add$inv st data-width))
          state)))

  (defund serial-add$sim (data-width cnt-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (posp cnt-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (serial-add$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (serial-add$st-gen data-width cnt-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (serial-add$map-to-links-list
             (de-sim-trace (si 'serial-add data-width)
                           inputs-seq
                           st
                           (serial-add$netlist data-width cnt-width))))
           0)
          state)))

  (defund serial-add$in-out-sim (data-width cnt-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (posp cnt-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (serial-add$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (serial-add$st-gen data-width cnt-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat2-lst
                     (serial-add$in-seq
                      inputs-seq st data-width cnt-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (serial-add$out-seq
                      inputs-seq st data-width cnt-width n)))))
       state)))
  )

;; 5. SERIAL-SUB

(progn
  (defun serial-sub$map-to-links (st)
    (b* ((a (get-field *serial-sub$a* st))
         (b (get-field *serial-sub$b* st))
         (ci (get-field *serial-sub$ci* st))
         (s (get-field *serial-sub$s* st))
         (co (get-field *serial-sub$co* st))
         (done (get-field *serial-sub$done* st))
         (sregs2 (get-field *serial-sub$sregs2* st))
         (sreg (get-field *serial-sub$sreg* st)))
      (append
       (list (cons 'sregs2 (shift-register2-piso$map-to-links sregs2)))
       (map-to-links1 (list (cons 'a a)
                            (cons 'b b)
                            (cons 'ci ci)
                            (cons 's s)
                            (cons 'co co)
                            (cons 'done done)))
       (list (cons 'sreg (shift-register-sipo$map-to-links sreg))))))

  (defun serial-sub$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (serial-sub$map-to-links (car x))
            (serial-sub$map-to-links-list (cdr x)))))

  (defund serial-sub$st-gen (data-width cnt-width)
    (declare (xargs :guard (and (natp data-width)
                                (posp cnt-width))))
    (b* ((full '(t))
         (empty '(nil))
         (a (list empty '(nil)))
         (b (list empty '(nil)))
         (ci (list full '(t)))
         (s (list empty '(nil)))
         (co (list empty '(nil)))
         (done (list empty '(nil)))
         (sregs2 (shift-register2-piso$st-gen data-width cnt-width))
         (sreg (shift-register-sipo$st-gen data-width cnt-width)))
      (list a b ci s co done sregs2 sreg)))

  (defund serial-sub$ins-and-st-test (data-width cnt-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (posp cnt-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (serial-sub$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (serial-sub$st-gen data-width cnt-width)))
      (mv (and (serial-sub$input-format-n inputs-seq data-width n)
               (serial-sub$valid-st st data-width cnt-width)
               (serial-sub$inv st data-width))
          state)))

  (defund serial-sub$sim (data-width cnt-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (posp cnt-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (serial-sub$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (serial-sub$st-gen data-width cnt-width)))
      (mv (pretty-list
           (remove-dup-neighbors
            (serial-sub$map-to-links-list
             (de-sim-trace (si 'serial-sub data-width)
                           inputs-seq
                           st
                           (serial-sub$netlist data-width cnt-width))))
           0)
          state)))

  (defund serial-sub$in-out-sim (data-width cnt-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (posp cnt-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (serial-sub$ins-len data-width))
         ((mv inputs-seq state)
          (signal-vals-gen num-signals n state nil))
         (st (serial-sub$st-gen data-width cnt-width)))
      (mv
       (append
        (list (cons 'in-seq
                    (v-to-nat2-lst
                     (serial-sub$in-seq
                      inputs-seq st data-width cnt-width n))))
        (list (cons 'out-seq
                    (v-to-nat-lst
                     (serial-sub$out-seq
                      inputs-seq st data-width cnt-width n)))))
       state)))
  )


