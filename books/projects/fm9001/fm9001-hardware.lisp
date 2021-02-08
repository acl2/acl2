;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

;; The low-level, 4-valued, functional specification of the FM9001, with the
;; test logic disabled.

(in-package "FM9001")

(include-book "control")
(include-book "core-alu")
(include-book "extend-immediate")
(include-book "flags")
(include-book "regfile")
(include-book "tv-dec-pass")

;; ======================================================================

;; Internal states.

(defun regs (st)
  (declare (xargs :guard (true-listp st)))
  (nth 0 st))

(defun flags (st)
  (declare (xargs :guard (true-listp st)))
  (nth 1 st))

(defun a-reg (st)
  (declare (xargs :guard (true-listp st)))
  (nth 2 st))

(defun b-reg (st)
  (declare (xargs :guard (true-listp st)))
  (nth 3 st))

(defun i-reg (st)
  (declare (xargs :guard (true-listp st)))
  (nth 4 st))

(defun data-out (st)
  (declare (xargs :guard (true-listp st)))
  (nth 5 st))

(defun addr-out (st)
  (declare (xargs :guard (true-listp st)))
  (nth 6 st))

(defun reset- (st)
  (declare (xargs :guard (true-listp st)))
  (nth 7 st))

(defun dtack- (st)
  (declare (xargs :guard (true-listp st)))
  (nth 8 st))

(defun hold- (st)
  (declare (xargs :guard (true-listp st)))
  (nth 9 st))

(defun pc-reg (st)
  (declare (xargs :guard (true-listp st)))
  (nth 10 st))

(defun cntl-state (st)
  (declare (xargs :guard (true-listp st)))
  (nth 11 st))

(deftheory fm9001-hardware-state-accessors
  '(regs flags a-reg b-reg i-reg data-out addr-out reset- dtack- hold-
         pc-reg cntl-state))

(in-theory (disable fm9001-hardware-state-accessors))

;; External Inputs.

(defun reset--input (ext-in)
  (declare (xargs :guard (true-listp ext-in)))
  (nth 0 ext-in))

(defun hold--input (ext-in)
  (declare (xargs :guard (true-listp ext-in)))
  (nth 1 ext-in))

(defun pc-reg-input (ext-in)
  (declare (xargs :guard (true-listp ext-in)))
  (subseq-list ext-in 2 6))

(deftheory fm9001-external-input-accessors
  '(reset--input hold--input pc-reg-input))

(in-theory (disable fm9001-external-input-accessors))

;; ======================================================================

;; FM9001-NEXT-STATE

;; The specification of the next state of the processor and memory for a single
;; clock cycle.

(defund FM9001-next-state (total-state external-inputs)
  (let ((p-state (caar total-state))
        (mem-state (caadr total-state)))

    (let ((regs        (regs       p-state))
          (flags       (flags      p-state))
          (a-reg       (a-reg      p-state))
          (b-reg       (b-reg      p-state))
          (i-reg       (i-reg      p-state))
          (data-out    (data-out   p-state))
          (addr-out    (addr-out   p-state))
          (last-reset- (reset-     p-state))
          (last-dtack- (dtack-     p-state))
          (last-hold-  (hold-      p-state))
          (last-pc-reg (pc-reg     p-state))
          (cntl-state  (cntl-state p-state))

          (reset-    (reset--input external-inputs))
          (hold-     (hold--input  external-inputs))
          (pc-reg-in (pc-reg-input external-inputs)))

      (let ((major-state      (major-state      (v-threefix
                                                 (strip-cars cntl-state))))
            (rw-              (rw-              (v-threefix
                                                 (strip-cars cntl-state))))
            (strobe-          (strobe-          (v-threefix
                                                 (strip-cars cntl-state))))
            (hdack-           (hdack-           (v-threefix
                                                 (strip-cars cntl-state))))
            (we-regs          (we-regs          (v-threefix
                                                 (strip-cars cntl-state))))
            (we-flags         (we-flags         (v-threefix
                                                 (strip-cars cntl-state))))
            (we-a-reg         (we-a-reg         (v-threefix
                                                 (strip-cars cntl-state))))
            (we-b-reg         (we-b-reg         (v-threefix
                                                 (strip-cars cntl-state))))
            (we-i-reg         (we-i-reg         (v-threefix
                                                 (strip-cars cntl-state))))
            (we-data-out      (we-data-out      (v-threefix
                                                 (strip-cars cntl-state))))
            (we-addr-out      (we-addr-out      (v-threefix
                                                 (strip-cars cntl-state))))
            (we-hold-         (we-hold-         (v-threefix
                                                 (strip-cars cntl-state))))
            (we-pc-reg        (we-pc-reg        (v-threefix
                                                 (strip-cars cntl-state))))
            (data-in-select   (data-in-select   (v-threefix
                                                 (strip-cars cntl-state))))
            (dec-addr-out     (dec-addr-out     (v-threefix
                                                 (strip-cars cntl-state))))
            (select-immediate (select-immediate (v-threefix
                                                 (strip-cars cntl-state))))
            (regs-address     (regs-address     (v-threefix
                                                 (strip-cars cntl-state))))
            (alu-c            (alu-c            (v-threefix
                                                 (strip-cars cntl-state))))
            (alu-op           (alu-op           (v-threefix
                                                 (strip-cars cntl-state))))
            (alu-zero         (alu-zero         (v-threefix
                                                 (strip-cars cntl-state))))
            (alu-mpg          (alu-mpg          (v-threefix
                                                 (strip-cars cntl-state)))))

        ;; ADDR-OUT, RW- and STROBE- are tristate when HOLDing, and pulled
        ;; high by external pullups.  The EXT- (external) signals are used
        ;; only by the memory interface.

        (let ((ext-addr-out
               (v-pullup (vft-buf (f-buf hdack-)
                                  (v-threefix (strip-cars addr-out)))))
              (ext-rw-
               (f-pullup (ft-buf (f-buf hdack-) (f-buf rw-))))
              (ext-strobe-
               (f-pullup (ft-buf (f-buf hdack-) strobe-)))
              (ext-data-out
               (vft-buf (f-not (f-buf rw-))
                        (v-threefix (strip-cars data-out)))))
          (let ((mem-response
                 (memory-value mem-state ext-strobe- ext-rw-
                               ext-addr-out
                               (make-list 32 :initial-element *X*))))
            (let ((dtack- (car mem-response))
                  (ext-data-bus (v-pullup
                                 (v-wire ext-data-out
                                         (cdr mem-response)))))
              (let ((reg-bus (f$extend-immediate
                              select-immediate
                              (a-immediate (v-threefix
                                            (strip-cars i-reg)))
                              (f$read-regs regs-address regs)))
                    (alu-bus (f$core-alu alu-c
                                         (v-threefix
                                          (strip-cars a-reg))
                                         (v-threefix
                                          (strip-cars b-reg))
                                         alu-zero alu-mpg alu-op
                                         (make-tree 32)))
                    (data-in (v-threefix
                              (v-wire ext-data-bus
                                      ext-data-out))))
                (let ((addr-out-bus (f$dec-pass dec-addr-out reg-bus))
                      (abi-bus
                       (fv-if (f-nand data-in-select
                                      (f-not (car last-dtack-)))
                              reg-bus
                              data-in)))
                  (list
                   (list
                    (list
                     (f$write-regs we-regs regs-address regs
                                   (bv alu-bus))
                     (pairlis$
                      (f$update-flags (strip-cars flags)
                                      we-flags
                                      alu-bus)
                      nil)
                     (pairlis$
                      (fv-if we-a-reg abi-bus (strip-cars a-reg))
                      nil)
                     (pairlis$
                      (fv-if we-b-reg abi-bus (strip-cars b-reg))
                      nil)
                     (pairlis$
                      (fv-if we-i-reg abi-bus (strip-cars i-reg))
                      nil)
                     (pairlis$
                      (fv-if we-data-out (bv alu-bus)
                             (strip-cars data-out))
                      nil)
                     (pairlis$
                      (fv-if we-addr-out addr-out-bus
                             (strip-cars addr-out))
                      nil)
                     (list (f-buf reset-))
                     (list (f-or strobe- (f-buf dtack-)))
                     (list (f-if we-hold-
                                 (f-buf hold-)
                                 (car last-hold-)))
                     (pairlis$
                      (fv-if we-pc-reg
                             pc-reg-in
                             (strip-cars last-pc-reg))
                      nil)
                     (pairlis$
                      (v-threefix (f$next-cntl-state
                                   (f-buf (car last-reset-))
                                   (f-buf (car last-dtack-))
                                   (f-buf (car last-hold-))
                                   rw-
                                   major-state
                                   (v-threefix (strip-cars i-reg))
                                   (v-threefix (strip-cars flags))
                                   (v-threefix
                                    (strip-cars last-pc-reg))
                                   regs-address))
                      nil)))
                   (list
                    (next-memory-state
                     mem-state ext-strobe- ext-rw-
                     ext-addr-out
                     ext-data-bus))))))))))))

;; RUN-FM9001 -- Simulates N clock cycles.

(defun run-fm9001 (st inputs n)
  (if (zp n)
      st
    (run-fm9001 (fm9001-next-state st (car inputs))
                (cdr inputs)
                (1- n))))

(defthm run-fm9001-base-case
  (implies (zp n)
           (equal (run-fm9001 st inputs n)
                  st)))

(defthmd run-fm9001-step-case
  (implies (not (zp n))
           (equal (run-fm9001 st inputs n)
                  (run-fm9001 (fm9001-next-state st (car inputs))
                              (cdr inputs)
                              (1- n)))))

(defthm run-fm9001-+
  (implies (and (natp m)
                (natp n))
           (equal (run-fm9001 st inputs (+ n m))
                  (run-fm9001 (run-fm9001 st inputs n)
                              (nthcdr n inputs)
                              m)))
  :hints (("Goal"
           :induct (run-fm9001 st inputs n))))

(defthm run-fm9001-plus
  (implies (and (natp m)
                (natp n))
           (equal (run-fm9001 st inputs (plus n m))
                  (run-fm9001 (run-fm9001 st inputs n)
                              (nthcdr n inputs)
                              m)))
  :hints (("Goal" :in-theory (e/d (plus)
                                  (commutativity-of-+)))))

(in-theory (disable run-fm9001))

;; ======================================================================

;; FM9001-STATE-STRUCTURE state

(defun fm9001-state-structure (st)
  (declare (xargs :guard t))
  (and (equal (len st) 2)
       (true-listp st)

       (equal (len (car st)) 1)
       (true-listp (car st))
       (equal (len (caar st)) 12)
       (true-listp (caar st))

       (equal (len (cadr st)) 1)
       (true-listp (cadr st))
       (equal (len (caadr st)) 8)
       (true-listp (caadr st))

       (equal (len (caaar st)) 4)
       (true-listp (caaar st))))

(defthm fm9001-state-structure$step
  (implies (fm9001-state-structure st)
           (fm9001-state-structure (fm9001-next-state st external-inputs)))
  :hints (("Goal" :in-theory (enable fm9001-next-state))))

(defthm fm9001-state-structure$induction
  (implies (fm9001-state-structure st)
           (fm9001-state-structure (run-fm9001 st inputs steps)))
  :hints (("Goal" :in-theory (e/d (run-fm9001)
                                  (fm9001-state-structure)))))

(defthm fm9001-state-as-a-list
  (implies (fm9001-state-structure st)
           (equal (list
                   (list (list (list (caaaar st)
                                     (car (cdaaar st))
                                     (cadr (cdaaar st))
                                     (caddr (cdaaar st)))
                               (cadaar st)
                               (car (cddaar st))
                               (cadr (cddaar st))
                               (caddr (cddaar st))
                               (cadddr (cddaar st))
                               (car (cddddr (cddaar st)))
                               (cadr (cddddr (cddaar st)))
                               (caddr (cddddr (cddaar st)))
                               (cadddr (cddddr (cddaar st)))
                               (car (cddddr (cddddr (cddaar st))))
                               (cadr (cddddr (cddddr (cddaar st))))))
                   (list (list (caaadr st)
                               (car (cdaadr st))
                               (cadr (cdaadr st))
                               (caddr (cdaadr st))
                               (cadddr (cdaadr st))
                               (car (cddddr (cdaadr st)))
                               (cadr (cddddr (cdaadr st)))
                               (caddr (cddddr (cdaadr st))))))
                  st))
  :hints (("Goal" :in-theory (enable open-len))))

(in-theory (disable fm9001-state-structure))

