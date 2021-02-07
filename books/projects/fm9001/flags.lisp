;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

(in-package "FM9001")

(include-book "de")
(include-book "fm9001-spec")
(include-book "macros")

(local (include-book "arithmetic/top" :dir :system))

;; ======================================================================

;; The FLAGS register is simply four, individually write-enabled, 1-bit
;; latches.  For simplicity the FLAGS register takes the entire 35-bit ALU bus
;; as an input, even though it only needs 4 of the bits, i.e., the C, V, N, and
;; Z.  Test input = TI.  Test output = C.

(module-generator
 flags* ()
 'flags
 (list* 'clk 'te 'ti (append (sis 'set-flags 0 4) (sis 'cvzbv 0 35)))
 '(z n v c)
 '(z-latch n-latch v-latch c-latch)
 (list
  ;; Z. Scan TI to Z
  (list 'z-latch
        '(z zb)
        'fd1slp
        (list (zb (sis 'cvzbv 0 35)) 'clk (z-set (sis 'set-flags 0 4))
              'ti 'te))
  ;; N. Scan Z to N
  (list 'n-latch
        '(n nb)
        'fd1slp
        (list (si 'cvzbv 34) 'clk (n-set (sis 'set-flags 0 4)) 'z 'te))
  ;; V. Scan N to V
  (list 'v-latch
        '(v vb)
        'fd1slp
        (list (v (sis 'cvzbv 0 35)) 'clk (v-set (sis 'set-flags 0 4))
              'n 'te))
  ;; C. Scan V to C
  (list 'c-latch
        '(c cb)
        'fd1slp
        (list (c (sis 'cvzbv 0 35)) 'clk (c-set (sis 'set-flags 0 4))
              'v 'te)))
 :guard t)

(defund flags& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (equal (assoc 'flags netlist)
         (flags*)))

(defun flags$netlist ()
  (declare (xargs :guard t))
  (list (flags*)))

(defthm check-flags$netlist
  (flags& (flags$netlist)))

(defthmd flags$value
  (implies (and (flags& netlist)
                (true-listp flags) (equal (len flags) 4))
           (equal (se 'flags (list* clk te ti (append set-flags cvzbv))
                      flags netlist)
                  (v-threefix (strip-cars flags))))
  :hints (("Goal"
           :in-theory (e/d (se-rules
                             flags&
                             flags*$destructure)
                            ((flags*)
                             (si)
                             (sis)
                             bvp-is-true-listp
                             bvp-cvzbv
                             tv-disabled-rules)))))

(defun f$update-flags (flags set-flags cvzbv)
  (declare (xargs :guard (and (true-listp flags)
                              (true-listp set-flags)
                              (true-listp cvzbv))))
  (list (f-if (z-set set-flags)
              (zb cvzbv)
              (z-flag flags))
        (f-if (n-set set-flags)
              (n cvzbv)
              (n-flag flags))
        (f-if (v-set set-flags)
              (v cvzbv)
              (v-flag flags))
        (f-if (c-set set-flags)
              (c cvzbv)
              (c-flag flags))))

(defthm len-f$update-flags
  (equal (len (f$update-flags flags set-flags cvzbv))
         4))

(defthm f$update-flags=update-flags
  (implies (and (bvp flags) (equal (len flags) 4)
                (bvp set-flags) (equal (len set-flags) 4)
                (bvp cvzbv) (equal (len cvzbv) 35))
           (equal (f$update-flags flags set-flags cvzbv)
                  (update-flags flags set-flags cvzbv)))
  :hints (("Goal" :in-theory (enable update-flags bvp
                                     zb v c))))

(local
 (defthm flags$state-aux
   (and (equal (car (sis s m n))
               (nth 0 (sis s m n)))
        (equal (cadr (sis s m n))
               (nth 1 (sis s m n)))
        (equal (caddr (sis s m n))
               (nth 2 (sis s m n))))
   :hints (("Goal" :in-theory (enable sis)))))

;; (defthmd flags$state-help
;;   (implies (and (flags& netlist)
;;                 (true-listp flags) (equal (len flags) 4)
;;                 (equal set-flags (list set-z set-n set-v set-c))
;;                 (equal cvzbv (cons c (cons v (cons z bv))))
;;                 (true-listp cvzbv) (equal (len cvzbv) 35)
;;                 (equal te nil))
;;            (equal (de 'flags (list* clk te ti (append set-flags cvzbv))
;;                       flags netlist)
;;                   (pairlis$
;;                    (f$update-flags (strip-cars flags) set-flags cvzbv)
;;                    nil)))
;;   :hints (("Goal"
;;            :use (:instance pairlis$-append
;;                            (x (sis 'set-flags 0 4))
;;                            (y (sis 'cvzbv 0 35))
;;                            (a set-flags)
;;                            (b cvzbv))
;;            :in-theory (e/d (de-rules
;;                              flags&
;;                              flags*$destructure
;;                              c-set v-set n-set z-set
;;                              c-flag v-flag n-flag z-flag
;;                              c v zb n bv
;;                              assoc-eq-value-nth-pairlis$
;;                              v-negp-as-nth)
;;                             ((flags*)
;;                              (si)
;;                              (sis)
;;                              nth
;;                              bvp-is-true-listp
;;                              bvp-cvzbv
;;                              tv-disabled-rules)))))

(defthmd flags$state
  (implies (and (flags& netlist)
                (true-listp flags) (equal (len flags) 4)
                (true-listp set-flags) (equal (len set-flags) 4)
                (true-listp cvzbv) (equal (len cvzbv) 35)
                (equal te nil))
           (equal (de 'flags (list* clk te ti (append set-flags cvzbv))
                      flags netlist)
                  (pairlis$
                   (f$update-flags (strip-cars flags) set-flags cvzbv)
                   nil)))
  :hints (("Goal"
           :in-theory (e/d (de-rules
                             flags&
                             flags*$destructure
                             c-set v-set n-set z-set
                             c-flag v-flag n-flag z-flag
                             c v zb n bv
                             assoc-eq-value-nth-pairlis$
                             v-negp-as-nth)
                            ((flags*)
                             (si)
                             (sis)
                             nth
                             bvp-is-true-listp
                             bvp-cvzbv
                             tv-disabled-rules)))))

(in-theory (disable f$update-flags))

;; (defthmd flags$partial-state-help
;;   (implies (and (flags& netlist)
;;                 (true-listp flags) (equal (len flags) 4)
;;                 (equal set-flags (make-list 4 :initial-element t))
;;                 (equal cvzbv (cons c (cons v (cons z bv))))
;;                 (bvp cvzbv) (equal (len cvzbv) 35)
;;                 (equal te nil))
;;            (equal (de 'flags (list* clk te ti (append set-flags cvzbv))
;;                       flags netlist)
;;                   (pairlis$
;;                    (update-flags (strip-cars flags) set-flags cvzbv)
;;                    nil)))
;;   :hints (("Goal"
;;            :use (:instance pairlis$-append
;;                            (x (sis 'set-flags 0 4))
;;                            (y (sis 'cvzbv 0 35))
;;                            (a set-flags)
;;                            (b cvzbv))
;;            :in-theory (e/d (de-rules
;;                              flags&
;;                              flags*$destructure
;;                              update-flags
;;                              bvp
;;                              c-set v-set n-set z-set
;;                              c-flag v-flag n-flag z-flag
;;                              c v zb n bv
;;                              assoc-eq-value-nth-pairlis$
;;                              v-negp-as-nth)
;;                             ((flags*)
;;                              (si)
;;                              (sis)
;;                              nth
;;                              bvp-is-true-listp
;;                              bvp-cvzbv
;;                              tv-disabled-rules)))))

(defthmd flags$partial-state
  (implies (and (flags& netlist)
                (true-listp flags) (equal (len flags) 4)
                (equal set-flags (make-list 4 :initial-element t))
                (bvp cvzbv) (equal (len cvzbv) 35)
                (equal te nil))
           (equal (de 'flags (list* clk te ti (append set-flags cvzbv))
                      flags netlist)
                  (pairlis$
                   (update-flags (strip-cars flags) set-flags cvzbv)
                   nil)))
  :hints (("Goal"
           :use (:instance pairlis$-append
                           (x (sis 'set-flags 0 4))
                           (y (sis 'cvzbv 0 35))
                           (a set-flags)
                           (b cvzbv))
           :in-theory (e/d (de-rules
                             flags&
                             flags*$destructure
                             update-flags
                             c-set v-set n-set z-set
                             c-flag v-flag n-flag z-flag
                             c v zb n bv
                             assoc-eq-value-nth-pairlis$
                             v-negp-as-nth)
                            ((flags*)
                             (si)
                             (sis)
                             nth
                             bvp-is-true-listp
                             bvp-cvzbv
                             tv-disabled-rules)))))

