;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

(in-package "FM9001")

(include-book "alu-spec")
(include-book "memory")
(include-book "reg")
(include-book "tv-if")
(include-book "v-equal")

;; ======================================================================

;; Boolean specifications of register file access.

(defun read-regs (address regs)
  (declare (xargs :guard (and (true-listp address)
                              (true-listp regs)
                              (alistp (car regs))
                              (alistp (cadr regs))
                              (alistp (caddr regs))
                              (alistp (cadddr regs)))))
  (let ((regfile      (caar regs))
        (last-we      (caadr regs))
        (last-data    (strip-cars (caddr regs)))
        (last-address (strip-cars (cadddr regs))))
    (if (and last-we (v-iff address last-address))
        (v-fourfix last-data)
      (read-mem address regfile))))

(defthm read-regs=read-mem
  (implies (not (caadr regs))
           (equal (read-regs v-addr regs)
                  (read-mem v-addr (caar regs)))))

(defthm bvp-read-regs
  (implies (and (memory-okp (len v-addr) width (caar regs))
                (bvp (strip-cars (caddr regs))))
           (bvp (read-regs v-addr regs)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-read-regs-32
  (implies (and (memory-okp (len v-addr) 32 (caar regs))
                (bvp (strip-cars (caddr regs))))
           (bvp (read-regs v-addr regs)))
  :rule-classes (:rewrite :type-prescription))

(defthm len-read-regs-32
  (implies (and (memory-okp (len v-addr) 32 (caar regs))
                (equal (len (caddr regs)) 32))
           (equal (len (read-regs v-addr regs))
                  32)))

(defun write-regs (we address regs data)
  (declare (xargs :guard (and (true-listp address)
                              (true-listp data)
                              (true-listp regs)
                              (alistp (car regs))
                              (alistp (cadr regs))
                              (alistp (caddr regs))
                              (alistp (cadddr regs)))))
  (let ((regfile      (caar regs))
        (last-we      (caadr regs))
        (last-data    (strip-cars (caddr regs)))
        (last-address (strip-cars (cadddr regs))))
    (list (list (if last-we
                    (write-mem last-address regfile last-data)
                  regfile))
          (list we)
          (pairlis$ (if we data last-data) nil)
          (pairlis$ (if we address last-address) nil))))

(defthm write-regs-write-regs-nil
  (equal (write-regs we addr1 (write-regs nil addr2 regs data2) data1)
         (write-regs we addr1 regs data1)))

(defthm write-regs-nil-bv-crock
  (equal (write-regs nil addr regs (bv x))
         (write-regs nil 0 regs 0)))

(defthm true-listp-caddr-write-regs
  (true-listp (caddr (write-regs we address regs data)))
  :rule-classes :type-prescription)

(defthm bvp-strip-cars-caddr-write-regs
  (implies (bvp (strip-cars (caddr regs)))
           (bvp (strip-cars (caddr (write-regs nil address regs data)))))
  :rule-classes (:rewrite :type-prescription))

(defthm true-listp-cadddr-write-regs
  (true-listp (cadddr (write-regs we address regs data)))
  :rule-classes :type-prescription)

(defthm bvp-strip-cars-cadddr-write-regs
  (implies (bvp (strip-cars (cadddr regs)))
           (bvp (strip-cars (cadddr (write-regs nil address regs data)))))
  :rule-classes (:rewrite :type-prescription))

(defthm len-write-regs
  (equal (len (write-regs we address regs data))
         4))

(defthm write-regs-if
  (equal (write-regs (if c a b) address regs data)
         (if c
             (write-regs a address regs data)
           (write-regs b address regs data))))

(defthm write-regs-ok
  (and
   (equal (memory-okp n m (caar (write-regs we address regs data)))
          (if (caadr regs)
              (memory-okp n m (write-mem (strip-cars (cadddr regs))
                                         (caar regs)
                                         (strip-cars (caddr regs))))
            (memory-okp n m (caar regs))))
   (equal (booleanp (caadr (write-regs we address regs data)))
          (booleanp we))
   (implies (true-listp data)
            (equal (bvp (strip-cars (caddr (write-regs we address regs
                                                       data))))
                   (if we
                       (bvp data)
                     (bvp (strip-cars (caddr regs))))))
   (equal (len (caddr (write-regs we address regs data)))
          (if we
              (len data)
            (len (caddr regs))))
   (implies (true-listp address)
            (equal (bvp (strip-cars (cadddr (write-regs we address regs
                                                        data))))
                   (if we
                       (bvp address)
                     (bvp (strip-cars (cadddr regs))))))
   (equal (len (cadddr (write-regs we address regs data)))
          (if we
              (len address)
            (len (cadddr regs))))))

(defthm read-regs-write-regs-nil
  (implies (and (all-ramp-mem (len addr) (caar regs))
                (equal (len addr) (len (cadddr regs))))
           (equal (read-regs addr (write-regs nil address regs value))
                  (read-regs addr regs)))
  :hints (("Goal"
           :use (:instance all-ramp-mem->ramp-mem
                           (v-addr (strip-cars (cadddr regs)))
                           (mem (caar regs))))))

(defthm all-ramp-mem-after-write-regs
  (implies (and (all-ramp-mem n (caar regs))
                (equal (len (cadddr regs)) n))
           (all-ramp-mem n (caar (write-regs we address regs data))))
  :hints (("Goal"
           :use (:instance all-ramp-mem-after-write-mem
                           (mem (caar regs))
                           (v-addr (strip-cars (cadddr regs)))
                           (value (strip-cars (caddr regs))))))
  :rule-classes (:rewrite :type-prescription))

(defthm read-regs=read-mem-write-mem
  (implies (and (all-ramp-mem (len v-addr1) (caar regs))
                (equal (len v-addr1) (len (cadddr regs)))
                (caadr regs))
           (equal (read-regs v-addr1 regs)
                  (read-mem v-addr1
                            (write-mem (strip-cars (cadddr regs))
                                       (caar regs)
                                       (strip-cars (caddr regs))))))
  :hints (("Goal"
           :use (:instance all-ramp-mem->ramp-mem
                           (v-addr (strip-cars (cadddr regs)))
                           (mem (caar regs))))))

(in-theory (disable read-regs write-regs))

;; ======================================================================

;; Hardware Implementation of the Register File

(module-generator
 regfile* ()
 'REGFILE
 (list* 'clk 'te 'ti 'we 'disable-regfile- 'test-regfile-
        (append (sis 'address 0 4) (sis 'data 0 32)))
 (cons 'to (sis 'out 0 32))
 '(ram we-latch data-latch address-latch)
 (list
  ;;  WE-LATCH. Scan TI to WE-DP-RAM
  (list 'we-latch
        '(we-dp-ram we-dp-ram-)
        'fd1s
        '(we clk ti te))
  ;;  ADDRESS-LATCH.  Scan WE-DP-RAM to (si 'address-dp-ram 3)
  (list 'address-latch
        (sis 'address-dp-ram 0 4)
        (si 'we-reg 4)
        (list* 'clk 'we 'te 'we-dp-ram (sis 'address 0 4)))
  ;;  DATA-LATCH.  Scan (si 'address-dp-ram 3) to (si 'data-dp-ram 31)
  (list 'data-latch
        (sis 'data-dp-ram 0 32)
        (si 'we-reg 32)
        (list* 'clk 'we 'te (si 'address-dp-ram 3) (sis 'data 0 32)))

  ;; Register File Enable Circuit
  '(reg-en-circuit (we-) ram-enable-circuit
                   (clk test-regfile- disable-regfile- we-dp-ram))
  ;;  The RAM.  This is a level-sensitive device.  The surrounding circuitry
  ;;  makes the entire register file work as if it were an edge-triggered
  ;;  device.
  (list 'ram
        (sis 'ramout 0 32)
        'dp-ram-16x32
        (append (sis 'address 0 4)                        ;Read address
                (append (sis 'address-dp-ram 0 4)         ;Write address
                        (cons 'we-                        ;Write enable
                              (sis 'data-dp-ram 0 32))))) ;Data
  ;;  Address comparator.
  (list 'compare
        '(read-equal-write)
        (si 'v-equal 4)
        (append (sis 'address 0 4) (sis 'address-dp-ram 0 4)))
  ;;  Mux control
  (list 'mux-control
        '(s)
        'b-and3
        '(we-dp-ram read-equal-write test-regfile-))
  ;;  Mux
  (list 'mux
        (sis 'out 0 32)
        (si 'tv-if (tree-number (make-tree 32)))
        (cons 's (append (sis 'data-dp-ram 0 32) (sis 'ramout 0 32))))
  ;;  Rename the scan out
  (list 'scanout
        '(to)
        'id
        (list (si 'data-dp-ram 31))))
 :guard t
 )

(defund regfile& (netlist)
  (and (equal (assoc 'regfile netlist)
              (regfile*))
       (let ((netlist (delete-to-eq 'regfile netlist)))
         (and (we-reg& netlist 4)
              (we-reg& netlist 32)
              (v-equal& netlist 4)
              (tv-if& netlist (make-tree 32))))))

(defun regfile$netlist ()
  (cons (regfile*)
        (union$ (we-reg$netlist 4)
                (we-reg$netlist 32)
                (v-equal$netlist 4)
                (tv-if$netlist (make-tree 32))
                :test 'equal)))

(defthm check-regfile$netlist
  (regfile& (regfile$netlist)))

;; ======================================================================

;; 4-Valued Register File Specifications

;; F$READ-REGS

(defun f$read-regs (address regs)
  (let ((regfile      (caar regs))
        (last-we      (caadr regs))
        (last-data    (strip-cars (caddr regs)))
        (last-address (strip-cars (cadddr regs))))
    (fv-if
     (f-and3 (f-buf last-we)
             (f$v-equal address (v-threefix last-address))
             t)
     (v-threefix last-data)
     (dual-port-ram-value
      32 4
      (append address
              (append (v-threefix last-address)
                      (cons (f-nand t (f-buf last-we))
                            (v-threefix last-data))))
      regfile))))

(defthm len-f$read-regs
  (implies (equal (len (caddr mem)) 32)
           (equal (len (f$read-regs address mem)) 32)))

(local
 (defthm nth-len-append-lemma
   (equal (nth (len x) (append x y))
          (car y))))

(defthm f$read-regs=read-regs
  (implies (and (memory-okp 4 32 (caar regs))
                (booleanp (caadr regs))
                (bvp (strip-cars (caddr regs)))
                (equal (len (caddr regs)) 32)
                (bvp (strip-cars (cadddr regs)))
                (equal (len (cadddr regs)) 4)
                (bvp address)
                (equal (len address) 4))
           (equal (f$read-regs address regs)
                  (read-regs address regs)))
  :hints (("Goal"
           :use ((:instance nth-len-append-lemma
                            (x (append (strip-cars (cadddr regs))
                                       (strip-cars (cadddr regs))))
                            (y (cons t (strip-cars (caddr regs)))))
                 (:instance bvp-read-mem-of-memory-okp
                            (v-addr address)
                            (mem (caar regs))
                            (size 32)))
           :in-theory (enable read-regs))))

;; The $VALUE lemma is a little more general than the $STATE lemma.

(defthmd regfile$value
  (implies (and (regfile& netlist)
                (equal test-regfile- t)
                (equal disable-regfile- t)
                (true-listp last-data)
                (equal (len last-data) 32)
                (true-listp address)
                (equal (len address) 4)
                (true-listp last-address)
                (equal (len last-address) 4))
           (equal (cdr (se 'regfile
                           (list* clk te ti we
                                  disable-regfile- test-regfile-
                                  (append address data))
                           (list mem last-we last-data last-address)
                           netlist))
                  (f$read-regs address
                               (list mem last-we last-data last-address))))
  :hints (("Goal"
           :in-theory (e/d (se-rules
                             regfile&
                             regfile*$destructure
                             dp-ram-16x32$structured-value
                             we-reg$value
                             v-equal$value
                             tv-if$value)
                            (tv-disabled-rules
                             dual-port-ram-value
                             (regfile*)
                             (make-tree)
                             (si)
                             (sis))))))

(in-theory (disable f$read-regs))

(defun f$write-regs (we address regs data)
  (let ((regfile      (caar regs))
        (last-we      (caadr regs))
        (last-data    (strip-cars (caddr regs)))
        (last-address (strip-cars (cadddr regs))))
    (list
     (list
      (dual-port-ram-state
       32 4
       (append address
               (append (v-threefix last-address)
                       (cons (f-nand t (f-buf last-we))
                             (v-threefix last-data))))
       regfile))
     (list (3v-fix we))
     (pairlis$ (fv-if we data last-data)
               nil)
     (pairlis$ (fv-if we address last-address)
               nil))))

(defthm len-f$write-regs
  (equal (len (f$write-regs we address regs data))
         4))

(defthm f$write-regs=write-regs
  (implies (and
            (booleanp we)
            (booleanp (caadr regs))
            (bvp (strip-cars (caddr regs))) (equal (len (caddr regs)) 32)
            (bvp (strip-cars (cadddr regs))) (equal (len (cadddr regs)) 4)
            (bvp address) (equal (len address) 4)
            (bvp data) (equal (len data) 32))
           (equal (f$write-regs we address regs data)
                  (write-regs we address regs data)))
  :hints (("Goal"
           :use ((:instance nth-len-append-lemma
                            (x (append address
                                       (strip-cars (cadddr regs))))
                            (y (cons t (strip-cars (caddr regs)))))
                 (:instance nth-len-append-lemma
                            (x (append address
                                       (strip-cars (cadddr regs))))
                            (y (cons nil (strip-cars (caddr regs))))))
           :in-theory (enable write-regs))))

(defthmd regfile$state
  (implies (and (regfile& netlist)
                (equal te nil)
                (equal test-regfile- t)
                (equal disable-regfile- t)
                (true-listp data) (equal (len data) 32)
                (true-listp last-data) (equal (len last-data) 32)
                (true-listp address) (equal (len address) 4)
                (true-listp last-address) (equal (len last-address) 4))
           (equal (de 'regfile
                      (list* clk te ti we disable-regfile- test-regfile-
                             (append address data))
                      (list regfile last-we last-data last-address)
                      netlist)
                  (f$write-regs we address
                                (list regfile last-we last-data last-address)
                                data)))
  :hints (("Goal"
           :in-theory (e/d (de-rules
                             regfile&
                             regfile*$destructure
                             dp-ram-16x32$structured-value
                             dp-ram-16x32$structured-state
                             we-reg$value
                             we-reg$state
                             v-equal$value
                             tv-if$value)
                            (tv-disabled-rules
                             dual-port-ram-state
                             (regfile*)
                             (make-tree)
                             (si)
                             (sis))))))

(in-theory (disable f$write-regs))
