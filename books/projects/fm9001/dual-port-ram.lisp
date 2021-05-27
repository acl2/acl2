;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

(in-package "FM9001")

(include-book "memory")

;; ======================================================================

;; This file contains a model of a dual-port ram:

;; (DUAL-PORT-RAM-VALUE bits address-lines args st)

;; returns the RAM output, i.e., the contents of the memory addressed by the
;; read-adress port.

;; (DUAL-PORT-RAM-STATE bits address-lines args st)

;; updates the state of the RAM.

;; The ARGS are assumed to be structured as follows:

;; 0..(ADDRESS-LINES - 1)               -- A (read port) address.
;; ADDRESS-LINES..(2*ADDRESS-LINES - 1) -- B (write port) address.
;; (2*ADDRESS-LINES)                    -- WEN, active low.
;; remainder                            -- DATA lines.

;; WARNING -- This is a sequential model of what is essentially a
;; level-sensitive device.  Note that this state-holding device has no clock
;; input.  Spikes on WEN, or changes on B-ADDRESS while WEN is active may cause
;; unanticipated changes in the memory state of the real device.

;; The dual-port RAM used in the register file of the FM9001 is surrounded by
;; sequential logic that ensures that setup and hold constraints are met.  See
;; the file "regfile.lisp".

(defun dual-port-ram-value (bits address-lines args st)
  (declare (xargs :guard (and (natp bits)
                              (natp address-lines)
                              (true-listp args))))
  (let ((a-address (subseq-list args 0 address-lines))
        (b-address (subseq-list args address-lines
                                (* 2 address-lines)))
        (wen (nth (* 2 address-lines) args)))
    ;; If the read address is unknown, or the device is potentially write
    ;; enabled and there is a potential write at the read address, then read
    ;; out X's.  Otherwise, read out the vector from the ST.
    (if (or (not (bvp a-address))
            (and (not (equal wen t))
                 (or (not (bvp b-address))
                     (equal a-address b-address))))
        (make-list bits :initial-element *x*)
      (let ((val (read-mem a-address st)))
        (if (and (true-listp val)
                 (equal (len val) bits))
            val
          ;; Return an unknown proper list of the right length if we don't read
          ;; a proper list of the right length.
          (make-list bits :initial-element *x*))))))

(defthm true-listp-dual-port-ram-value
  (true-listp (dual-port-ram-value bits address-lines args st))
  :rule-classes :type-prescription)

(defthm len-dual-port-ram-value
  (equal (len (dual-port-ram-value bits address-lines args st))
         (nfix bits)))

(defun dual-port-ram-state (bits address-lines args st)
  (declare (xargs :guard (and (natp bits)
                              (natp address-lines)
                              (true-listp args))))
  (let ((b-address (subseq-list args address-lines
                                (* 2 address-lines)))
        (wen (nth (* 2 address-lines) args))
        ;; Use SUBSEQ-LIST instead of NTHCDR so that we are guaranteed that
        ;; this argument has the right length and is a TRUE-LISTP.  Note that
        ;; we use bits below rather than (len args) in order to ensure that
        ;; data has the right length.
        (data
         (subseq-list args
                      (1+ (* 2 address-lines))
                      (+ 1 (* 2 address-lines) bits))))
    ;; If WEN is solidly high, do nothing.
    (if (equal wen t)
        st
      ;; There is a potential write.  If the address is unknown, wipe out the
      ;; state.
      (if (not (bvp b-address))
          (constant-ram st (make-list bits :initial-element *x*))
        ;; If WEN is solidly low, update the state with data, otherwise X out
        ;; the addressed entry.
        (if (equal wen nil)
            (write-mem b-address st data)
          (write-mem b-address st (make-list bits :initial-element *x*)))))))

(defthm true-listp-dual-port-ram-state
  (implies (true-listp st)
           (true-listp (dual-port-ram-state bits address-lines args st)))
  :rule-classes :type-prescription)

(defthm len-dual-port-ram-state
  (equal (len (dual-port-ram-state bits address-lines args st))
         (len st)))
