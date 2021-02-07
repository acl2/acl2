;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

(in-package "FM9001")

(include-book "de")
(include-book "list-rewrites")
(include-book "macros")

;; ======================================================================

;; Below are definitions of some simple circuits which we think of as
;; primitives, even though they are constructed from more than 1 macrocell.

;; B-BUF-PWR -- In the LSI Logic implementation, this "super-buffer" can
;; drive 64 loads in 1.6ns.

(defconst *b-buf-pwr*
  '((b-buf-pwr
     (in)
     (out)
     ()
     ((g0 (out-) b-not (in))
      (g1 (out)  b-not-b4ip (out-))))))

(defthmd b-buf-pwr-okp
  (and (net-syntax-okp *b-buf-pwr*)
       (net-arity-okp *b-buf-pwr*)))

(defund b-buf-pwr& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (netlist-hyps netlist b-buf-pwr))

(defthmd b-buf-pwr$value
  (implies (b-buf-pwr& netlist)
           (equal (se 'b-buf-pwr (list in) sts netlist)
                  (list (f-buf in))))
  :hints (("Goal" :in-theory (enable se-rules
                                      b-buf-pwr&
                                      3vp
                                      f-gates))))

;; DP-RAM-16x32

;; We prefer to think of the DP-RAM-16x32 arguments as being structured as two
;; addresses, the write enable, and the data.

(defthmd dp-ram-16x32-args-crock
  (implies (and (equal (len a) 4) (true-listp a)
                (equal (len b) 4) (true-listp b)
                (equal (len c) 32) (true-listp c))
           (equal (append a (append b (cons x c)))
                  (append (list-as-collected-nth a 4 0)
                          (append (list-as-collected-nth b 4 0)
                                  (cons x
                                        (list-as-collected-nth c 32 0))))))
  :hints (("Goal"
           :use ((:instance equal-len-4-as-collected-nth
                            (l a))
                 (:instance equal-len-4-as-collected-nth
                            (l b))
                 (:instance equal-len-32-as-collected-nth
                            (l c)))
           :in-theory (disable open-list-as-collected-nth))))

(defthmd dp-ram-16x32$structured-value
  (implies (and (equal (len a) 4) (true-listp a)
                (equal (len b) 4) (true-listp b)
                (equal (len c) 32) (true-listp c))
           (equal (se 'dp-ram-16x32 (append a (append b (cons x c)))
                      sts netlist)
                  (dual-port-ram-value 32 4
                                       (append a (append b (cons x c)))
                                       (car sts))))
  :hints (("Goal"
           :in-theory (e/d (se-rules
                             dp-ram-16x32-args-crock)
                            (dual-port-ram-value)))))

(defthmd dp-ram-16x32$structured-state
  (implies (and (equal (len a) 4) (true-listp a)
                (equal (len b) 4) (true-listp b)
                (equal (len c) 32) (true-listp c))
           (equal (de 'dp-ram-16x32 (append a (append b (cons x c)))
                      sts netlist)
                  (list
                   (dual-port-ram-state 32 4
                                        (append a (append b (cons x c)))
                                        (car sts)))))
  :hints (("Goal"
           :in-theory (e/d (de-rules
                             dp-ram-16x32-args-crock)
                            (dual-port-ram-state)))))

;; MEM-32x32

;; We prefer to think of the MEM-32x32 arguments as being structured as an
;; address, data-bus, a strobe, and a read-write signal.

(defthmd mem-32x32-args-crock
  (implies (and (equal (len addr) 32) (true-listp addr)
                (equal (len data) 32) (true-listp data))
           (equal (cons rw-
                        (cons strobe-
                              (append addr data)))
                  (cons rw-
                        (cons strobe-
                              (append (list-as-collected-nth addr 32 0)
                                      (list-as-collected-nth data 32 0))))))
  :hints (("Goal"
           :use ((:instance equal-len-32-as-collected-nth
                            (l addr))
                 (:instance equal-len-32-as-collected-nth
                            (l data)))
           :in-theory (disable open-list-as-collected-nth))))

(defthmd mem-32x32$structured-value-1
  (implies (and (equal (len addr) 32) (true-listp addr)
                (equal (len data) 32) (true-listp data))
           (equal (se 'mem-32x32
                      (cons rw-
                            (cons strobe-
                                  (append addr data)))
                      sts netlist)
                  (memory-value (car sts) strobe- rw-
                                (list (nth 0 addr)
                                      (nth 1 addr)
                                      (nth 2 addr)
                                      (nth 3 addr)
                                      (nth 4 addr)
                                      (nth 5 addr)
                                      (nth 6 addr)
                                      (nth 7 addr)
                                      (nth 8 addr)
                                      (nth 9 addr)
                                      (nth 10 addr)
                                      (nth 11 addr)
                                      (nth 12 addr)
                                      (nth 13 addr)
                                      (nth 14 addr)
                                      (nth 15 addr)
                                      (nth 16 addr)
                                      (nth 17 addr)
                                      (nth 18 addr)
                                      (nth 19 addr)
                                      (nth 20 addr)
                                      (nth 21 addr)
                                      (nth 22 addr)
                                      (nth 23 addr)
                                      (nth 24 addr)
                                      (nth 25 addr)
                                      (nth 26 addr)
                                      (nth 27 addr)
                                      (nth 28 addr)
                                      (nth 29 addr)
                                      (nth 30 addr)
                                      (nth 31 addr))
                                (list (nth 0 data)
                                      (nth 1 data)
                                      (nth 2 data)
                                      (nth 3 data)
                                      (nth 4 data)
                                      (nth 5 data)
                                      (nth 6 data)
                                      (nth 7 data)
                                      (nth 8 data)
                                      (nth 9 data)
                                      (nth 10 data)
                                      (nth 11 data)
                                      (nth 12 data)
                                      (nth 13 data)
                                      (nth 14 data)
                                      (nth 15 data)
                                      (nth 16 data)
                                      (nth 17 data)
                                      (nth 18 data)
                                      (nth 19 data)
                                      (nth 20 data)
                                      (nth 21 data)
                                      (nth 22 data)
                                      (nth 23 data)
                                      (nth 24 data)
                                      (nth 25 data)
                                      (nth 26 data)
                                      (nth 27 data)
                                      (nth 28 data)
                                      (nth 29 data)
                                      (nth 30 data)
                                      (nth 31 data)))))
  :hints (("Goal"
           :in-theory (e/d (se-rules
                             mem-value
                             mem-32x32-args-crock)
                            (nth)))))

(defthmd mem-32x32$structured-value
  (implies (and (equal (len addr) 32) (true-listp addr)
                (equal (len data) 32) (true-listp data))
           (equal (se 'mem-32x32
                      (cons rw-
                            (cons strobe-
                                  (append addr data)))
                      sts netlist)
                  (memory-value (car sts) strobe- rw- addr data)))
  :hints (("Goal"
           :use ((:instance equal-len-32-as-collected-nth
                            (l addr))
                 (:instance equal-len-32-as-collected-nth
                            (l data)))
           :in-theory (e/d (mem-32x32$structured-value-1)
                           (nth)))))

(defthmd mem-32x32$structured-state-1
  (implies (and (equal (len addr) 32) (true-listp addr)
                (equal (len data) 32) (true-listp data))
           (equal (de 'mem-32x32
                      (cons rw-
                            (cons strobe-
                                  (append addr data)))
                      sts netlist)
                  (list
                   (next-memory-state (car sts) strobe- rw-
                                      (list (nth 0 addr)
                                            (nth 1 addr)
                                            (nth 2 addr)
                                            (nth 3 addr)
                                            (nth 4 addr)
                                            (nth 5 addr)
                                            (nth 6 addr)
                                            (nth 7 addr)
                                            (nth 8 addr)
                                            (nth 9 addr)
                                            (nth 10 addr)
                                            (nth 11 addr)
                                            (nth 12 addr)
                                            (nth 13 addr)
                                            (nth 14 addr)
                                            (nth 15 addr)
                                            (nth 16 addr)
                                            (nth 17 addr)
                                            (nth 18 addr)
                                            (nth 19 addr)
                                            (nth 20 addr)
                                            (nth 21 addr)
                                            (nth 22 addr)
                                            (nth 23 addr)
                                            (nth 24 addr)
                                            (nth 25 addr)
                                            (nth 26 addr)
                                            (nth 27 addr)
                                            (nth 28 addr)
                                            (nth 29 addr)
                                            (nth 30 addr)
                                            (nth 31 addr))
                                      (list (nth 0 data)
                                            (nth 1 data)
                                            (nth 2 data)
                                            (nth 3 data)
                                            (nth 4 data)
                                            (nth 5 data)
                                            (nth 6 data)
                                            (nth 7 data)
                                            (nth 8 data)
                                            (nth 9 data)
                                            (nth 10 data)
                                            (nth 11 data)
                                            (nth 12 data)
                                            (nth 13 data)
                                            (nth 14 data)
                                            (nth 15 data)
                                            (nth 16 data)
                                            (nth 17 data)
                                            (nth 18 data)
                                            (nth 19 data)
                                            (nth 20 data)
                                            (nth 21 data)
                                            (nth 22 data)
                                            (nth 23 data)
                                            (nth 24 data)
                                            (nth 25 data)
                                            (nth 26 data)
                                            (nth 27 data)
                                            (nth 28 data)
                                            (nth 29 data)
                                            (nth 30 data)
                                            (nth 31 data))))))
  :hints (("Goal"
           :in-theory (e/d (de-rules
                             mem-state
                             mem-32x32-args-crock)
                            (nth)))))

(defthmd mem-32x32$structured-state
  (implies (and (equal (len addr) 32) (true-listp addr)
                (equal (len data) 32) (true-listp data))
           (equal (de 'mem-32x32
                      (cons rw-
                            (cons strobe-
                                  (append addr data)))
                      sts netlist)
                  (list
                   (next-memory-state (car sts) strobe- rw- addr data))))
  :hints (("Goal"
           :use ((:instance equal-len-32-as-collected-nth
                            (l addr))
                 (:instance equal-len-32-as-collected-nth
                            (l data)))
           :in-theory (e/d (mem-32x32$structured-state-1)
                           (nth)))))
