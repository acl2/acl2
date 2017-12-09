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

(defconst *queue4$data-ins-len* (+ 2 *data-width*))
(defconst *queue4$go-num* 3)
(defconst *queue4$ins-len* (+ *queue4$data-ins-len*
                              *queue4$go-num*))
(defconst *queue4$st-len* 8)

;; A 4-link queue module: L0 -> L1 -> L2 -> L3

(module-generator
 queue4* ()
 'queue4
 (list* 'in-act 'out-act (append (sis 'data-in 0 *data-width*)
                                 (sis 'go 0 *queue4$go-num*)))
 (list* 'ready-in- 'ready-out
        (sis 'data-out 0 *data-width*))
 '(l0 d0 l1 d1 l2 d2 l3 d3)
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
  '(l3 (l3-status) link-cntl (trans3-act out-act))
  (list 'd3
        (sis 'data-out 0 *data-width*)
        (si 'latch-n *data-width*)
        (list* 'trans3-act (sis 'd3-in 0 *data-width*)))

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

  ;; STATUS
  '(in-status (ready-in-) b-buf (l0-status))
  '(out-status (ready-out) b-buf (l3-status)))

 :guard t)

(defun queue4$netlist ()
  (declare (xargs :guard t))
  (cons (queue4*)
        (union$ (latch-n$netlist *data-width*)
                (v-buf$netlist *data-width*)
                *joint-cntl*
                :test 'equal)))

(defthmd queue4$netlist-okp
  (and (net-syntax-okp (queue4$netlist))
       (net-arity-okp (queue4$netlist))))

(defund queue4& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (and (equal (assoc 'queue4 netlist)
              (queue4*))
       (b* ((netlist (delete-to-eq 'queue4 netlist)))
         (and (joint-cntl& netlist)
              (latch-n& netlist *data-width*)
              (v-buf& netlist *data-width*)))))

(defthm check-queue4$netlist
  (queue4& (queue4$netlist)))

(defconst *queue4$l0* 0)
(defconst *queue4$d0* 1)
(defconst *queue4$l1* 2)
(defconst *queue4$d1* 3)
(defconst *queue4$l2* 4)
(defconst *queue4$d2* 5)
(defconst *queue4$l3* 6)
(defconst *queue4$d3* 7)

(defund queue4$valid-st (st)
  (b* ((l0 (get-field *queue4$l0* st))
       (d0 (get-field *queue4$d0* st))
       (l1 (get-field *queue4$l1* st))
       (d1 (get-field *queue4$d1* st))
       (l2 (get-field *queue4$l2* st))
       (d2 (get-field *queue4$d2* st))
       (l3 (get-field *queue4$l3* st))
       (d3 (get-field *queue4$d3* st)))
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
         (equal (len d3) *data-width*))))

(defun queue4$map-to-links (st)
  (b* ((l0 (get-field *queue4$l0* st))
       (d0 (get-field *queue4$d0* st))
       (l1 (get-field *queue4$l1* st))
       (d1 (get-field *queue4$d1* st))
       (l2 (get-field *queue4$l2* st))
       (d2 (get-field *queue4$d2* st))
       (l3 (get-field *queue4$l3* st))
       (d3 (get-field *queue4$d3* st)))
    (map-to-links (list (list 'l0 l0 d0)
                        (list 'l1 l1 d1)
                        (list 'l2 l2 d2)
                        (list 'l3 l3 d3)))))

(defun queue4$map-to-links-list (x)
  (if (atom x)
      nil
    (cons (queue4$map-to-links (car x))
          (queue4$map-to-links-list (cdr x)))))

(defund queue4$sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *queue4$ins-len*)
       ((mv inputs-lst state) (go-vals-gen num-signals n state nil))
       ;;(- (cw "~x0~%" inputs-lst))
       (empty '(nil))
       (invalid-data (make-list *data-width* :initial-element '(x)))
       (st (list empty invalid-data
                 empty invalid-data
                 empty invalid-data
                 empty invalid-data)))
    (mv (pretty-list
         (remove-dup-neighbors
          (queue4$map-to-links-list
           (de-sim-list 'queue4 inputs-lst st (queue4$netlist))))
         0)
        state)))

(defund queue4$in-act (inputs)
  (nth 0 inputs))

(defund queue4$out-act (inputs)
  (nth 1 inputs))

(defun queue4$get-data-in (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (subseq-list inputs 2 (+ 2 *data-width*)))

(defthm len-queue4$get-data-in
  (equal (len (queue4$get-data-in inputs))
         *data-width*))

(in-theory (disable queue4$get-data-in))

(defund queue4$ready-in- (st)
  (b* ((l0 (get-field *queue4$l0* st)))
    (f-buf (car l0))))

(defthm booleanp-queue4$ready-in-
  (implies (queue4$valid-st st)
           (booleanp (queue4$ready-in- st)))
  :hints (("Goal" :in-theory (enable queue4$valid-st
                                     queue4$ready-in-)))
  :rule-classes :type-prescription)

(defund queue4$ready-out (st)
  (b* ((l3 (get-field *queue4$l3* st)))
    (f-buf (car l3))))

(defthm booleanp-queue4$ready-out
  (implies (queue4$valid-st st)
           (booleanp (queue4$ready-out st)))
  :hints (("Goal" :in-theory (enable queue4$valid-st
                                     queue4$ready-out)))
  :rule-classes :type-prescription)

(defund queue4$data-out (st)
  (strip-cars (get-field *queue4$d3* st)))

(defthm queue4$data-out-props
   (implies (queue4$valid-st st)
            (and (bvp (queue4$data-out st))
                 (equal (len (queue4$data-out st))
                        *data-width*)))
   :hints (("Goal" :in-theory (enable queue4$valid-st
                                      queue4$data-out))))

(defthmd queue4$value
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue4& netlist)
                  (queue4$valid-st st))
             (equal (se 'queue4 inputs st netlist)
                    (list* (queue4$ready-in- st)
                           (queue4$ready-out st)
                           (queue4$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (se-rules
                            get-field
                            len-1-true-listp=>true-listp
                            queue4&
                            queue4*$destructure
                            joint-cntl$value
                            latch-n$value
                            v-buf$value
                            queue4$valid-st
                            queue4$ready-in-
                            queue4$ready-out
                            queue4$data-out)
                           ((queue4*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(defun queue4$state-fn (inputs st)
  (b* ((in-act     (queue4$in-act inputs))
       (out-act    (queue4$out-act inputs))
       (data-in    (queue4$get-data-in inputs))
       (go-signals (nthcdr *queue4$data-ins-len* inputs))

       (go-trans1 (nth 0 go-signals))
       (go-trans2 (nth 1 go-signals))
       (go-trans3 (nth 2 go-signals))
       
       (l0 (get-field *queue4$l0* st))
       (d0 (get-field *queue4$d0* st))
       (l1 (get-field *queue4$l1* st))
       (d1 (get-field *queue4$d1* st))
       (l2 (get-field *queue4$l2* st))
       (d2 (get-field *queue4$d2* st))
       (l3 (get-field *queue4$l3* st))
       (d3 (get-field *queue4$d3* st))

       (trans1-act (joint-act (car l0) (car l1) go-trans1))
       (trans2-act (joint-act (car l1) (car l2) go-trans2))
       (trans3-act (joint-act (car l2) (car l3) go-trans3)))
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
     
     (list (f-sr trans3-act out-act (car l3)))
     (pairlis$ (fv-if trans3-act (strip-cars d2) (strip-cars d3))
               nil))))

(defthm len-of-queue4$state-fn
  (equal (len (queue4$state-fn inputs st))
         *queue4$st-len*))

(defthmd queue4$state
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue4& netlist)
                  (true-listp data-in)
                  (equal (len data-in) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue4$go-num*)
                  (queue4$valid-st st))
             (equal (de 'queue4 inputs st netlist)
                    (queue4$state-fn inputs st))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (de-rules
                            get-field
                            len-1-true-listp=>true-listp
                            queue4&
                            queue4*$destructure
                            queue4$valid-st
                            queue4$in-act
                            queue4$out-act
                            queue4$get-data-in
                            joint-cntl$value
                            latch-n$value latch-n$state
                            v-buf$value)
                           ((queue4*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(in-theory (disable queue4$state-fn))

;; ======================================================================

(defund queue4$input-format (inputs st)
  (b* ((in-act     (queue4$in-act inputs))
       (out-act    (queue4$out-act inputs))
       (data-in    (queue4$get-data-in inputs))
       (go-signals (nthcdr *queue4$data-ins-len* inputs))

       (ready-in- (queue4$ready-in- st))
       (ready-out (queue4$ready-out st)))
    (and
     (if ready-in-
         (not in-act)
       (booleanp in-act))
     (if (not ready-out)
         (not out-act)
       (booleanp out-act))
     (bvp data-in)
     (true-listp go-signals)
     (= (len go-signals) *queue4$go-num*)
     (equal inputs
            (list* in-act out-act (append data-in go-signals))))))

(defthm queue4$valid-st-preserved
  (implies (and (queue4$input-format inputs st)
                (queue4$valid-st st))
           (queue4$valid-st (queue4$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue4$input-format
                            queue4$valid-st
                            queue4$state-fn
                            queue4$ready-in-
                            queue4$ready-out
                            f-sr)
                           (if*
                            nth
                            nthcdr
                            acl2::true-listp-append)))))

(defthmd queue4$state-alt
  (implies (and (queue4& netlist)
                (queue4$input-format inputs st)
                (queue4$valid-st st))
           (equal (de 'queue4 inputs st netlist)
                  (queue4$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (enable queue4$input-format)
           :use (:instance queue4$state
                           (in-act     (queue4$in-act inputs))
                           (out-act    (queue4$out-act inputs))
                           (data-in    (queue4$get-data-in inputs))
                           (go-signals (nthcdr *queue4$data-ins-len*
                                               inputs))))))

(state-fn-n-gen queue4)

(input-format-n-with-state-gen queue4)

(defthmd de-sim-n$queue4
  (implies (and (queue4& netlist)
                (queue4$input-format-n inputs-lst st n)
                (queue4$valid-st st))
           (equal (de-sim-n 'queue4 inputs-lst st netlist n)
                  (queue4$state-fn-n inputs-lst st n)))
  :hints (("Goal" :in-theory (enable queue4$state-alt))))

;; ======================================================================

(defund queue4$extract-state (st)
  (b* ((l0 (get-field *queue4$l0* st))
       (d0 (get-field *queue4$d0* st))
       (l1 (get-field *queue4$l1* st))
       (d1 (get-field *queue4$d1* st))
       (l2 (get-field *queue4$l2* st))
       (d2 (get-field *queue4$d2* st))
       (l3 (get-field *queue4$l3* st))
       (d3 (get-field *queue4$d3* st)))
    (extract-state (list l0 d0 l1 d1 l2 d2 l3 d3))))

(defun queue4$in-seq (inputs-lst st n)
  (declare (ignorable st)
           (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue4$in-act inputs) t)
          (append (queue4$in-seq (cdr inputs-lst)
                                 (queue4$state-fn inputs st)
                                 (1- n))
                  (list (pairlis$ (queue4$get-data-in inputs)
                                  nil)))
        (queue4$in-seq (cdr inputs-lst)
                       (queue4$state-fn inputs st)
                       (1- n))))))

(defun queue4$out-seq (inputs-lst st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst))
         (extracted-st (queue4$extract-state st)))
      (if (equal (queue4$out-act inputs) t)
          (append (queue4$out-seq (cdr inputs-lst)
                                  (queue4$state-fn inputs st)
                                  (1- n))
                  (list (nth (1- (len extracted-st))
                             extracted-st)))
        (queue4$out-seq (cdr inputs-lst)
                        (queue4$state-fn inputs st)
                        (1- n))))))

(defund queue4$in-out-seq-sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *queue4$ins-len*)
       ((mv inputs-lst state)
        (go-vals-gen num-signals n state nil))
       (empty '(nil))
       (invalid-data (make-list *data-width* :initial-element '(x)))
       (st (list empty invalid-data
                 empty invalid-data
                 empty invalid-data
                 empty invalid-data)))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-flatten-lst
                   (queue4$in-seq inputs-lst st n))))
      (list (cons 'out-seq
                  (v-to-nat-flatten-lst
                   (queue4$out-seq inputs-lst st n)))))
     state)))

(defund queue4$step-spec (inputs st)
  (b* ((data-in (queue4$get-data-in inputs))
       (extracted-st (queue4$extract-state st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue4$out-act inputs) t)
      (cond
       ((equal (queue4$in-act inputs) t)
        (cons (pairlis$ data-in nil)
              (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue4$in-act inputs) t)
          (cons (pairlis$ data-in nil)
                extracted-st))
         (t extracted-st))))))

(defthm queue4$step-spec-correct
  (b* ((next-st (queue4$state-fn inputs st)))
    (implies (and (queue4$input-format inputs st)
                  (queue4$valid-st st))
             (equal (queue4$extract-state next-st)
                    (queue4$step-spec inputs st))))
  :hints (("Goal"
           :in-theory (enable get-field
                              queue4$step-spec
                              queue4$input-format
                              queue4$valid-st
                              queue4$state-fn
                              queue4$ready-in-
                              queue4$ready-out
                              queue4$extract-state))))

(defthm consp-queue4$extract-state
  (implies (and (queue4$input-format inputs st)
                (queue4$valid-st st)
                (queue4$out-act inputs))
           (consp (queue4$extract-state st)))
  :hints (("Goal"
           :in-theory (enable queue4$input-format
                              queue4$valid-st
                              queue4$ready-out
                              queue4$extract-state)))
  :rule-classes :type-prescription)

(encapsulate
  ()

  (local
   (defthm queue4$dataflow-correct-aux
     (implies (equal (append x1 y1)
                     (append (queue4$in-seq inputs-lst st n) y2))
              (equal (append x1 y1 z)
                     (append (queue4$in-seq inputs-lst st n) y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (acl2::associativity-of-append))))))

  (defthmd queue4$dataflow-correct
    (b* ((extracted-st (queue4$extract-state st))
         (final-st (queue4$state-fn-n inputs-lst st n))
         (final-extracted-st (queue4$extract-state final-st)))
      (implies (and (queue4$input-format-n inputs-lst st n)
                    (queue4$valid-st st))
               (equal (append final-extracted-st
                              (queue4$out-seq inputs-lst st n))
                      (append (queue4$in-seq inputs-lst st n)
                              extracted-st))))
    :hints (("Goal"
             :in-theory (e/d (queue4$step-spec)
                             ()))))
  )

