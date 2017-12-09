;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; December 2017

(in-package "ADE")

(include-book "constants")
(include-book "link-joint")
(include-book "store-n")
(include-book "vector-module")

(local (in-theory (e/d (f-buf-delete-lemmas-1
                        f-buf-delete-lemmas-2)
                       (nth-of-bvp-is-booleanp
                        take-of-len-free))))

;; ======================================================================

(defconst *queue5$data-ins-len* (+ 2 *data-width*))
(defconst *queue5$go-num* 4)
(defconst *queue5$ins-len* (+ *queue5$data-ins-len*
                              *queue5$go-num*))
(defconst *queue5$st-len* 10)

;; A 5-link queue module: L0 -> L1 -> L2 -> L3 -> L4

(module-generator
 queue5* ()
 'queue5
 (list* 'in-act 'out-act (append (sis 'data-in 0 *data-width*)
                                 (sis 'go 0 *queue5$go-num*)))
 (list* 'ready-in- 'ready-out
        (sis 'data-out 0 *data-width*))
 '(l0 d0 l1 d1 l2 d2 l3 d3 l4 d4)
 (list
  ;; LINKS
  ;; L0
  '(l0 (l0-status) link-cntl (in-act trans1-act))
  (list 'd0
        (sis 'd0-out 0 *data-width*)
        (si 'latch-n *data-width*)
        (list* 'in-act (sis 'data-in 0 *data-width*)))

  ;; L1
  '(l1 (l1-status) link-cntl (trans1-act trans2-act))
  (list 'd1
        (sis 'd1-out 0 *data-width*)
        (si 'latch-n *data-width*)
        (list* 'trans1-act (sis 'd1-in 0 *data-width*)))

  ;; L2
  '(l2 (l2-status) link-cntl (trans2-act trans3-act))
  (list 'd2
        (sis 'd2-out 0 *data-width*)
        (si 'latch-n *data-width*)
        (list* 'trans2-act (sis 'd2-in 0 *data-width*)))

  ;; L3
  '(l3 (l3-status) link-cntl (trans3-act trans4-act))
  (list 'd3
        (sis 'd3-out 0 *data-width*)
        (si 'latch-n *data-width*)
        (list* 'trans3-act (sis 'd3-in 0 *data-width*)))

  ;; L4
  '(l4 (l4-status) link-cntl (trans4-act out-act))
  (list 'd4
        (sis 'data-out 0 *data-width*)
        (si 'latch-n *data-width*)
        (list* 'trans4-act (sis 'd4-in 0 *data-width*)))

  ;; JOINTS
  ;; Transfer data1
  (list 'trans1-cntl
        '(trans1-act)
        'joint-cntl
        (list 'l0-status 'l1-status (si 'go 0)))
  (list 'trans1-op
        (sis 'd1-in 0 *data-width*)
        (si 'v-buf *data-width*)
        (sis 'd0-out 0 *data-width*))

  ;; Transfer data2
  (list 'trans2-cntl
        '(trans2-act)
        'joint-cntl
        (list 'l1-status 'l2-status (si 'go 1)))
  (list 'trans2-op
        (sis 'd2-in 0 *data-width*)
        (si 'v-buf *data-width*)
        (sis 'd1-out 0 *data-width*))

  ;; Transfer data3
  (list 'trans3-cntl
        '(trans3-act)
        'joint-cntl
        (list 'l2-status 'l3-status (si 'go 2)))
  (list 'trans3-op
        (sis 'd3-in 0 *data-width*)
        (si 'v-buf *data-width*)
        (sis 'd2-out 0 *data-width*))

  ;; Transfer data4
  (list 'trans4-cntl
        '(trans4-act)
        'joint-cntl
        (list 'l3-status 'l4-status (si 'go 3)))
  (list 'trans4-op
        (sis 'd4-in 0 *data-width*)
        (si 'v-buf *data-width*)
        (sis 'd3-out 0 *data-width*))

  ;; STATUS
  '(in-status (ready-in-) b-buf (l0-status))
  '(out-status (ready-out) b-buf (l4-status)))

 :guard t)

(defun queue5$netlist ()
  (declare (xargs :guard t))
  (cons (queue5*)
        (union$ (latch-n$netlist *data-width*)
                (v-buf$netlist *data-width*)
                *joint-cntl*
                :test 'equal)))

(defthmd queue5$netlist-okp
  (and (net-syntax-okp (queue5$netlist))
       (net-arity-okp (queue5$netlist))))

(defund queue5& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (and (equal (assoc 'queue5 netlist)
              (queue5*))
       (b* ((netlist (delete-to-eq 'queue5 netlist)))
         (and (joint-cntl& netlist)
              (latch-n& netlist *data-width*)
              (v-buf& netlist *data-width*)))))

(defthm check-queue5$netlist
  (queue5& (queue5$netlist)))

(defconst *queue5$l0* 0)
(defconst *queue5$d0* 1)
(defconst *queue5$l1* 2)
(defconst *queue5$d1* 3)
(defconst *queue5$l2* 4)
(defconst *queue5$d2* 5)
(defconst *queue5$l3* 6)
(defconst *queue5$d3* 7)
(defconst *queue5$l4* 8)
(defconst *queue5$d4* 9)

(defund queue5$valid-st (st)
  (b* ((l0 (get-field *queue5$l0* st))
       (d0 (get-field *queue5$d0* st))
       (l1 (get-field *queue5$l1* st))
       (d1 (get-field *queue5$d1* st))
       (l2 (get-field *queue5$l2* st))
       (d2 (get-field *queue5$d2* st))
       (l3 (get-field *queue5$l3* st))
       (d3 (get-field *queue5$d3* st))
       (l4 (get-field *queue5$l4* st))
       (d4 (get-field *queue5$d4* st)))
    (and (validp l0)
         (len-1-true-listp d0)
         (bvp (strip-cars d0))
         (equal (len d0) *data-width*)
         
         (validp l1)
         (len-1-true-listp d1)
         (bvp (strip-cars d1))
         (equal (len d1) *data-width*)
         
         (validp l2)
         (len-1-true-listp d2)
         (bvp (strip-cars d2))
         (equal (len d2) *data-width*)

         (validp l3)
         (len-1-true-listp d3)
         (bvp (strip-cars d3))
         (equal (len d3) *data-width*)
         
         (validp l4)
         (len-1-true-listp d4)
         (bvp (strip-cars d4))
         (equal (len d4) *data-width*))))

(defun queue5$map-to-links (st)
  (b* ((l0 (get-field *queue5$l0* st))
       (d0 (get-field *queue5$d0* st))
       (l1 (get-field *queue5$l1* st))
       (d1 (get-field *queue5$d1* st))
       (l2 (get-field *queue5$l2* st))
       (d2 (get-field *queue5$d2* st))
       (l3 (get-field *queue5$l3* st))
       (d3 (get-field *queue5$d3* st))
       (l4 (get-field *queue5$l4* st))
       (d4 (get-field *queue5$d4* st)))
    (map-to-links (list (list 'l0 l0 d0)
                        (list 'l1 l1 d1)
                        (list 'l2 l2 d2)
                        (list 'l3 l3 d3)
                        (list 'l4 l4 d4)))))

(defun queue5$map-to-links-list (x)
  (if (atom x)
      nil
    (cons (queue5$map-to-links (car x))
          (queue5$map-to-links-list (cdr x)))))

(defund queue5$sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *queue5$ins-len*)
       ((mv inputs-lst state) (go-vals-gen num-signals n state nil))
       ;;(- (cw "~x0~%" inputs-lst))
       (empty '(nil))
       (invalid-data (make-list *data-width* :initial-element '(x)))
       (st (list empty invalid-data
                 empty invalid-data
                 empty invalid-data
                 empty invalid-data
                 empty invalid-data)))
    (mv (pretty-list
         (remove-dup-neighbors
          (queue5$map-to-links-list
           (de-sim-list 'queue5 inputs-lst st (queue5$netlist))))
         0)
        state)))

(defund queue5$in-act (inputs)
  (nth 0 inputs))

(defund queue5$out-act (inputs)
  (nth 1 inputs))

(defun queue5$get-data-in (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (subseq-list inputs 2 (+ 2 *data-width*)))

(defthm len-queue5$get-data-in
  (equal (len (queue5$get-data-in inputs))
         *data-width*))

(in-theory (disable queue5$get-data-in))

(defund queue5$ready-in- (st)
  (b* ((l0 (get-field *queue5$l0* st)))
    (f-buf (car l0))))

(defthm booleanp-queue5$ready-in-
  (implies (queue5$valid-st st)
           (booleanp (queue5$ready-in- st)))
  :hints (("Goal" :in-theory (enable queue5$valid-st
                                     queue5$ready-in-)))
  :rule-classes :type-prescription)

(defund queue5$ready-out (st)
  (b* ((l4 (get-field *queue5$l4* st)))
    (f-buf (car l4))))

(defthm booleanp-queue5$ready-out
  (implies (queue5$valid-st st)
           (booleanp (queue5$ready-out st)))
  :hints (("Goal" :in-theory (enable queue5$valid-st
                                     queue5$ready-out)))
  :rule-classes :type-prescription)

(defund queue5$data-out (st)
  (strip-cars (get-field *queue5$d4* st)))

(defthm queue5$data-out-props
   (implies (queue5$valid-st st)
            (and (bvp (queue5$data-out st))
                 (equal (len (queue5$data-out st))
                        *data-width*)))
   :hints (("Goal" :in-theory (enable queue5$valid-st
                                      queue5$data-out))))

(defthmd queue5$value
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue5& netlist)
                  (queue5$valid-st st))
             (equal (se 'queue5 inputs st netlist)
                    (list* (queue5$ready-in- st)
                           (queue5$ready-out st)
                           (queue5$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (se-rules
                            get-field
                            len-1-true-listp=>true-listp
                            queue5&
                            queue5*$destructure
                            joint-cntl$value
                            latch-n$value
                            v-buf$value
                            queue5$valid-st
                            queue5$ready-in-
                            queue5$ready-out
                            queue5$data-out)
                           ((queue5*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(defun queue5$state-fn (inputs st)
  (b* ((in-act     (queue5$in-act inputs))
       (out-act    (queue5$out-act inputs))
       (data-in    (queue5$get-data-in inputs))
       (go-signals (nthcdr *queue5$data-ins-len* inputs))

       (go-trans1 (nth 0 go-signals))
       (go-trans2 (nth 1 go-signals))
       (go-trans3 (nth 2 go-signals))
       (go-trans4 (nth 3 go-signals))
       
       (l0 (get-field *queue5$l0* st))
       (d0 (get-field *queue5$d0* st))
       (l1 (get-field *queue5$l1* st))
       (d1 (get-field *queue5$d1* st))
       (l2 (get-field *queue5$l2* st))
       (d2 (get-field *queue5$d2* st))
       (l3 (get-field *queue5$l3* st))
       (d3 (get-field *queue5$d3* st))
       (l4 (get-field *queue5$l4* st))
       (d4 (get-field *queue5$d4* st))

       (trans1-act (joint-act (car l0) (car l1) go-trans1))
       (trans2-act (joint-act (car l1) (car l2) go-trans2))
       (trans3-act (joint-act (car l2) (car l3) go-trans3))
       (trans4-act (joint-act (car l3) (car l4) go-trans4)))
    (list
     (list (f-sr in-act trans1-act (car l0)))
     (pairlis$ (fv-if in-act data-in (strip-cars d0))
               nil)
     
     (list (f-sr trans1-act trans2-act (car l1)))
     (pairlis$ (fv-if trans1-act
                      (fv-if in-act data-in (strip-cars d0))
                      (strip-cars d1))
               nil)

     (list (f-sr trans2-act trans3-act (car l2)))
     (pairlis$ (fv-if trans2-act (strip-cars d1) (strip-cars d2))
               nil)

     (list (f-sr trans3-act trans4-act (car l3)))
     (pairlis$ (fv-if trans3-act (strip-cars d2) (strip-cars d3))
               nil)
     
     (list (f-sr trans4-act out-act (car l4)))
     (pairlis$ (fv-if trans4-act (strip-cars d3) (strip-cars d4))
               nil))))

(defthm len-of-queue5$state-fn
  (equal (len (queue5$state-fn inputs st))
         *queue5$st-len*))

(defthmd queue5$state
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue5& netlist)
                  (true-listp data-in)
                  (equal (len data-in) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue5$go-num*)
                  (queue5$valid-st st))
             (equal (de 'queue5 inputs st netlist)
                    (queue5$state-fn inputs st))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (de-rules
                            get-field
                            len-1-true-listp=>true-listp
                            queue5&
                            queue5*$destructure
                            queue5$valid-st
                            queue5$in-act
                            queue5$out-act
                            queue5$get-data-in
                            joint-cntl$value
                            latch-n$value latch-n$state
                            v-buf$value)
                           ((queue5*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(in-theory (disable queue5$state-fn))

;; ======================================================================

(defund queue5$input-format (inputs st)
  (b* ((in-act     (queue5$in-act inputs))
       (out-act    (queue5$out-act inputs))
       (data-in    (queue5$get-data-in inputs))
       (go-signals (nthcdr *queue5$data-ins-len* inputs))

       (ready-in- (queue5$ready-in- st))
       (ready-out (queue5$ready-out st)))
    (and
     (if ready-in-
         (not in-act)
       (booleanp in-act))
     (if (not ready-out)
         (not out-act)
       (booleanp out-act))
     (bvp data-in)
     (true-listp go-signals)
     (= (len go-signals) *queue5$go-num*)
     (equal inputs
            (list* in-act out-act (append data-in go-signals))))))

(defthm queue5$valid-st-preserved
  (implies (and (queue5$input-format inputs st)
                (queue5$valid-st st))
           (queue5$valid-st (queue5$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue5$input-format
                            queue5$valid-st
                            queue5$state-fn
                            queue5$ready-in-
                            queue5$ready-out
                            f-sr)
                           (if*
                            nth
                            nthcdr
                            acl2::true-listp-append)))))

(defthmd queue5$state-alt
  (implies (and (queue5& netlist)
                (queue5$input-format inputs st)
                (queue5$valid-st st))
           (equal (de 'queue5 inputs st netlist)
                  (queue5$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (enable queue5$input-format)
           :use (:instance queue5$state
                           (in-act     (queue5$in-act inputs))
                           (out-act    (queue5$out-act inputs))
                           (data-in    (queue5$get-data-in inputs))
                           (go-signals (nthcdr *queue5$data-ins-len*
                                               inputs))))))

(state-fn-n-gen queue5)

(input-format-n-with-state-gen queue5)

(defthmd de-sim-n$queue5
  (implies (and (queue5& netlist)
                (queue5$input-format-n inputs-lst st n)
                (queue5$valid-st st))
           (equal (de-sim-n 'queue5 inputs-lst st netlist n)
                  (queue5$state-fn-n inputs-lst st n)))
  :hints (("Goal" :in-theory (enable queue5$state-alt))))

;; ======================================================================

(defund queue5$extract-state (st)
  (b* ((l0 (get-field *queue5$l0* st))
       (d0 (get-field *queue5$d0* st))
       (l1 (get-field *queue5$l1* st))
       (d1 (get-field *queue5$d1* st))
       (l2 (get-field *queue5$l2* st))
       (d2 (get-field *queue5$d2* st))
       (l3 (get-field *queue5$l3* st))
       (d3 (get-field *queue5$d3* st))
       (l4 (get-field *queue5$l4* st))
       (d4 (get-field *queue5$d4* st)))
    (extract-state (list l0 d0 l1 d1 l2 d2 l3 d3 l4 d4))))

(defun queue5$in-seq (inputs-lst st n)
  (declare (ignorable st)
           (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue5$in-act inputs) t)
          (append (queue5$in-seq (cdr inputs-lst)
                                 (queue5$state-fn inputs st)
                                 (1- n))
                  (list (pairlis$ (queue5$get-data-in inputs)
                                  nil)))
        (queue5$in-seq (cdr inputs-lst)
                       (queue5$state-fn inputs st)
                       (1- n))))))

(defun queue5$out-seq (inputs-lst st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst))
         (extracted-st (queue5$extract-state st)))
      (if (equal (queue5$out-act inputs) t)
          (append (queue5$out-seq (cdr inputs-lst)
                                  (queue5$state-fn inputs st)
                                  (1- n))
                  (list (nth (1- (len extracted-st))
                             extracted-st)))
        (queue5$out-seq (cdr inputs-lst)
                        (queue5$state-fn inputs st)
                        (1- n))))))

(defund queue5$in-out-seq-sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *queue5$ins-len*)
       ((mv inputs-lst state)
        (go-vals-gen num-signals n state nil))
       (empty '(nil))
       (invalid-data (make-list *data-width* :initial-element '(x)))
       (st (list empty invalid-data
                 empty invalid-data
                 empty invalid-data
                 empty invalid-data
                 empty invalid-data)))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-flatten-lst
                   (queue5$in-seq inputs-lst st n))))
      (list (cons 'out-seq
                  (v-to-nat-flatten-lst
                   (queue5$out-seq inputs-lst st n)))))
     state)))

(defund queue5$step-spec (inputs st)
  (b* ((data-in (queue5$get-data-in inputs))
       (extracted-st (queue5$extract-state st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue5$out-act inputs) t)
      (cond
       ((equal (queue5$in-act inputs) t)
        (cons (pairlis$ data-in nil)
              (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue5$in-act inputs) t)
          (cons (pairlis$ data-in nil)
                extracted-st))
         (t extracted-st))))))

(defthm queue5$step-spec-correct
  (b* ((next-st (queue5$state-fn inputs st)))
    (implies (and (queue5$input-format inputs st)
                  (queue5$valid-st st))
             (equal (queue5$extract-state next-st)
                    (queue5$step-spec inputs st))))
  :hints (("Goal"
           :in-theory (enable get-field
                              queue5$step-spec
                              queue5$input-format
                              queue5$valid-st
                              queue5$state-fn
                              queue5$ready-in-
                              queue5$ready-out
                              queue5$extract-state))))

(defthm consp-queue5$extract-state
  (implies (and (queue5$input-format inputs st)
                (queue5$valid-st st)
                (queue5$out-act inputs))
           (consp (queue5$extract-state st)))
  :hints (("Goal"
           :in-theory (enable queue5$input-format
                              queue5$valid-st
                              queue5$ready-out
                              queue5$extract-state)))
  :rule-classes :type-prescription)

(encapsulate
  ()

  (local
   (defthm queue5$dataflow-correct-aux
     (implies (equal (append x1 y1)
                     (append (queue5$in-seq inputs-lst st n) y2))
              (equal (append x1 y1 z)
                     (append (queue5$in-seq inputs-lst st n) y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (acl2::associativity-of-append))))))

  (defthmd queue5$dataflow-correct
    (b* ((extracted-st (queue5$extract-state st))
         (final-st (queue5$state-fn-n inputs-lst st n))
         (final-extracted-st (queue5$extract-state final-st)))
      (implies (and (queue5$input-format-n inputs-lst st n)
                    (queue5$valid-st st))
               (equal (append final-extracted-st
                              (queue5$out-seq inputs-lst st n))
                      (append (queue5$in-seq inputs-lst st n)
                              extracted-st))))
    :hints (("Goal"
             :in-theory (e/d (queue5$step-spec)
                             ()))))
  )

