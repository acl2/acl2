;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

(in-package "FM9001")

(include-book "memory")
(include-book "utils")

;; ======================================================================

;; This is a model of a generic memory for the FM9001.  Besides the state
;; component, the memory takes as input a STROBE (active low), a read/write
;; line (low to write), and address and data lines.

;; The state component consists of the memory contents, a memory control state
;; (see below), a "clock" (see below), a "count" used for DTACK scheduling, a
;; flag indicating that DTACK has been asserted, the last value of RW- and the
;; last address and data inputs.

;; Address lines, and data lines on a write, must be stable for one cycle
;; before the strobe is activated, and one cycle after the strobe is released.
;; On a write, the same setup/hold constraints also must be met by the low
;; pulse on RW-.

;; Memory control states:

;; 0 -- The quiet state.
;; 1 -- Read wait.
;; 2 -- Write wait.
;; x -- Error.

;; The "clock" is an oracle that specifies the wait for DTACK.  Whenever the
;; STROBE is activated, then (CAR clock) is the number of memory delays for
;; this memory operation, and the new "clock" becomes (CDR clock).  For
;; simulation purposes we normally set this to 0 to provide minimum delays
;; since both the CAR and CDR of 0 are 0.

(defun consp-or-nil (x)
  (declare (xargs :guard t))
  (if (consp x) x nil))

(defthm car-of-consp-or-nil
  (equal (car (consp-or-nil x))
         (car x)))

(defthm cdr-of-consp-or-nil
  (equal (cdr (consp-or-nil x))
         (cdr x)))

(defthm double-consp-or-nil-canceled
  (equal (consp-or-nil (consp-or-nil x))
         (consp-or-nil x)))

(in-theory (disable consp-or-nil))

(defun next-memory-state (st strobe- rw- address data)
  (declare (xargs :guard (true-listp address)))
  ;; (declare (xargs :guard-debug t
  ;;                 :guard (and (true-listp st)
  ;;                             (true-listp address)
  ;;                             (consp (caddr st))
  ;;                             (natp (caaddr st))
  ;;                             (natp (cadddr st)))))
  (b* ((st              (list-fix st))
       (mem             (car st))
       (cntl            (cadr st))
       (clock           (consp-or-nil (caddr st)))
       (count           (nfix (cadddr st)))
       (?dtack-asserted (car (cddddr st)))
       (last-rw-        (cadr (cddddr st)))
       (last-address    (caddr (cddddr st)))
       (last-data       (cadddr (cddddr st))))

    (let ((mem-delay (nfix (car clock)))
          (rw-address-data
           (list (3v-fix rw-)
                 (v-threefix address)
                 (if (booleanp rw-)
                     (if rw-
                         (v-threefix last-data)
                       (v-threefix data))
                   (make-list (len data) :initial-element *x*)))))
      (let
          ((reset       (list* mem 0 clock 0 t rw-address-data))
           (start-read  (list* mem 1 (cdr clock)
                               (1- mem-delay) (zp mem-delay)
                               rw-address-data))
           (start-write (list* mem 2 (cdr clock)
                               (1- mem-delay) (zp mem-delay)
                               rw-address-data))
           (read-error  (list* mem 3 (cdr clock)
                               (1- mem-delay) (zp mem-delay)
                               rw-address-data))
           (write-error (list* (constant-ram mem (make-list 32
                                                            :initial-element
                                                            *x*))
                               3 (cdr clock)
                               (1- mem-delay) (zp mem-delay)
                               rw-address-data))
           (reset-error  (list* (constant-ram mem (make-list 32
                                                             :initial-element
                                                             *x*))
                                0 clock 0 t
                                rw-address-data))
           (finish-write (list* (write-mem address mem data) 0 clock 0 t
                                rw-address-data))
           (read-wait  (list* mem 1 clock (1- count) (zp count)
                              rw-address-data))
           (write-wait (list* mem 2 clock (1- count) (zp count)
                              rw-address-data))
           (error-wait (list* mem 3 clock (1- count) (zp count)
                              rw-address-data)))

        (let ((bvp-equal-address (and (bvp address)
                                      (bvp last-address)
                                      (equal address last-address)))
              (bvp-equal-data (and (bvp data)
                                   (bvp last-data)
                                   (equal data last-data))))

          (if (and (booleanp strobe-) (booleanp rw-))

              (case cntl
                (0 (if strobe-
                       reset
                     (if rw-
                         (if (and last-rw- (booleanp last-rw-))
                             (if bvp-equal-address
                                 start-read
                               read-error)
                           write-error)
                       (if (and (not last-rw-) ;; Subtle
                                bvp-equal-address
                                bvp-equal-data)
                           start-write
                         write-error))))

                (1 (if strobe-
                       (if rw-
                           reset
                         reset-error)
                     (if rw-
                         (if bvp-equal-address
                             read-wait
                           read-error)
                       write-error)))

                (2 (if strobe-
                       (if rw-
                           reset-error
                         (if (and bvp-equal-address
                                  bvp-equal-data
                                  (zp count))
                             finish-write
                           reset-error))
                     (if rw-
                         write-error
                       (if (and bvp-equal-address
                                bvp-equal-data)
                           write-wait
                         write-error))))

                (otherwise (if strobe-
                               (if rw-
                                   reset
                                 reset-error)
                             (if rw-
                                 error-wait
                               write-error))))

            reset-error))))))

(defthm len-next-memory-state
  (equal (len (next-memory-state st strobe- rw- address data))
         8)
  :hints (("Goal" :in-theory (disable zp-open nfix))))

(in-theory (disable next-memory-state))

(defun memory-value (st strobe- rw- address data)
  (declare (xargs :guard (true-listp address)))
  (b* ((st              (list-fix st))
       (mem             (car st))
       (cntl            (cadr st))
       (clock           (consp-or-nil (caddr st)))
       (count           (nfix (cadddr st)))
       (dtack-asserted  (car (cddddr st)))
       (?last-rw-       (cadr (cddddr st)))
       (last-address    (caddr (cddddr st)))
       (?last-data      (cadddr (cddddr st))))
    (let ((mem-delay   (nfix (car clock)))
          (x-vector    (make-list (len data) :initial-element *x*))
          (z-vector    (make-list (len data) :initial-element *z*)))

      (let ((unknown        (cons *x* x-vector))
            (default        (cons *x* z-vector))
            (read-wait      (cons t x-vector))
            (write-wait     (cons t z-vector))
            (dtack-0        (cons (if* (zp mem-delay) nil t)
                                  (if* rw- x-vector z-vector)))
            (dtack-read     (cons nil
                                  (if* dtack-asserted
                                       (read-mem address mem)
                                       x-vector)))
            (dtack-read-default  (cons nil x-vector))
            (dtack-write-default  (cons nil z-vector)))

        (let ((bvp-equal-address (and* (equal address last-address)
                                       (and* (bvp address)
                                             (bvp last-address)))))
          (if* (and* (booleanp strobe-) (booleanp rw-))
               (case cntl
                 (0 (if* strobe-
                         default
                         dtack-0))

                 (1 (if* strobe-
                         default
                         (if* rw-
                              (if* bvp-equal-address
                                   (if* (zp count)
                                        dtack-read
                                        read-wait)
                                   (if* (zp count)
                                        dtack-read-default
                                        read-wait))
                              (if* (zp count)
                                   dtack-write-default
                                   write-wait))))

                 (2 (if* strobe-
                         default
                         (if* (zp count)
                              dtack-write-default
                              write-wait)))

                 (otherwise (if* strobe-
                                 default
                                 (if* rw-
                                      (if* (zp count)
                                           dtack-read-default
                                           read-wait)
                                      (if* (zp count)
                                           dtack-write-default
                                           write-wait)))))

               unknown))))))

(defthm true-listp-memory-value
  (implies (and (memory-properp 32 32 (car st))
                (equal (len address) 32))
           (true-listp (memory-value st strobe- rw- address data)))
  :rule-classes (:rewrite :type-prescription))

(defthm true-listp-cdr-memory-value
  (implies (and (memory-properp 32 32 (car st))
                (equal (len address) 32))
           (true-listp (cdr (memory-value st strobe- rw- address data))))
  :rule-classes (:rewrite :type-prescription))

(defthm len-memory-value
  (implies (and (memory-properp 32 32 (car st))
                (equal (len address) 32)
                (equal (len data) 32))
           (equal (len (memory-value st strobe- rw- address data))
                  33))
  :hints (("Goal" :in-theory (disable zp-open nfix))))

(defthm len-cdr-memory-value
  (implies (and (memory-properp 32 32 (car st))
                (equal (len address) 32)
                (equal (len data) 32))
           (equal (len (cdr (memory-value st strobe- rw- address data)))
                  32))
  :hints (("Goal" :in-theory (disable zp-open nfix))))

(defthm equal-memory-value
  (implies (equal (len data1) (len data2))
           (equal (equal (memory-value st strobe- rw- address data1)
                         (memory-value st strobe- rw- address data2))
                  t)))

(in-theory (disable memory-value))

;; A couple of helper definitions to make it easy to call the FM9001 memory.

(defun mem-value (args st)
  (declare (xargs :guard (true-listp args)))
  (let ((rw-     (car args))
        (strobe- (cadr args))
        (address (subseq-list args 2 34))
        (data    (subseq-list args 34 66)))
    (memory-value st strobe- rw- address data)))

(defthm true-listp-mem-value
  (implies (memory-properp 32 32 (car st))
           (true-listp (mem-value args st)))
  :rule-classes (:rewrite :type-prescription))

(defthm len-mem-value
  (implies (memory-properp 32 32 (car st))
           (equal (len (mem-value args st))
                  33)))

(defun mem-state (args st)
  (declare (xargs :guard (true-listp args)))
  (let ((rw-     (car args))
        (strobe- (cadr args))
        (address (subseq-list args 2 34))
        (data    (subseq-list args 34 66)))
    (next-memory-state st strobe- rw- address data)))

(defthm len-mem-state
  (equal (len (mem-state args st))
         8))

(in-theory (disable mem-value mem-state))





