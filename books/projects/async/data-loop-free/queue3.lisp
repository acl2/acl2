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

(defconst *queue3$data-ins-len* (+ 2 *data-width*))
(defconst *queue3$go-num* 4)
(defconst *queue3$ins-len* (+ *queue3$data-ins-len*
                             *queue3$go-num*))
(defconst *queue3$st-len* 6)

;; A 3-link queue module: -> L0 -> L1 -> L2 ->

(module-generator
 queue3* ()
 'queue3
 (list* 'full-in 'full-out- (append (sis 'data-in 0 *data-width*)
                                    (sis 'go 0 *queue3$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 *data-width*))
 '(l0 d0 l1 d1 l2 d2)
 (list
  ;; LINKS
  ;; L0
  '(l0 (l0-status) link-cntl (in-act trans1-act))
  (list 'd0
        (sis 'd0-out 0 *data-width*)
        (si 'latch-n *data-width*)
        (list* 'in-act (sis 'd0-in 0 *data-width*)))

  ;; L1
  '(l1 (l1-status) link-cntl (trans1-act trans2-act))
  (list 'd1
        (sis 'd1-out 0 *data-width*)
        (si 'latch-n *data-width*)
        (list* 'trans1-act (sis 'd1-in 0 *data-width*)))

  ;; L2
  '(l2 (l2-status) link-cntl (trans2-act out-act))
  (list 'd2
        (sis 'd2-out 0 *data-width*)
        (si 'latch-n *data-width*)
        (list* 'trans2-act (sis 'd2-in 0 *data-width*)))

  ;; JOINTS
  ;; In
  (list 'in-cntl
        '(in-act)
        'joint-cntl
        (list 'full-in 'l0-status (si 'go 0)))
  (list 'in-op
        (sis 'd0-in 0 *data-width*)
        (si 'v-buf *data-width*)
        (sis 'data-in 0 *data-width*))

  ;; Transfer data1
  (list 'trans1-cntl
        '(trans1-act)
        'joint-cntl
        (list 'l0-status 'l1-status (si 'go 1)))
  (list 'trans1-op
        (sis 'd1-in 0 *data-width*)
        (si 'v-buf *data-width*)
        (sis 'd0-out 0 *data-width*))

  ;; Transfer data2
  (list 'trans2-cntl
        '(trans2-act)
        'joint-cntl
        (list 'l1-status 'l2-status (si 'go 2)))
  (list 'trans2-op
        (sis 'd2-in 0 *data-width*)
        (si 'v-buf *data-width*)
        (sis 'd1-out 0 *data-width*))

  ;; Out
  (list 'out-cntl
        '(out-act)
        'joint-cntl
        (list 'l2-status 'full-out- (si 'go 3)))
  (list 'out-op
        (sis 'data-out 0 *data-width*)
        (si 'v-buf *data-width*)
        (sis 'd2-out 0 *data-width*)))

 :guard t)

(defun queue3$netlist ()
  (declare (xargs :guard t))
  (cons (queue3*)
        (union$ (latch-n$netlist *data-width*)
                (v-buf$netlist *data-width*)
                *joint-cntl*
                :test 'equal)))

(defthmd queue3$netlist-okp
  (and (net-syntax-okp (queue3$netlist))
       (net-arity-okp (queue3$netlist))))

(defund queue3& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (and (equal (assoc 'queue3 netlist)
              (queue3*))
       (b* ((netlist (delete-to-eq 'queue3 netlist)))
         (and (joint-cntl& netlist)
              (latch-n& netlist *data-width*)
              (v-buf& netlist *data-width*)))))

(defthm check-queue3$netlist
  (queue3& (queue3$netlist)))

(defconst *queue3$l0* 0)
(defconst *queue3$d0* 1)
(defconst *queue3$l1* 2)
(defconst *queue3$d1* 3)
(defconst *queue3$l2* 4)
(defconst *queue3$d2* 5)

(defund queue3$valid-st (st)
  (b* ((l0 (get-field *queue3$l0* st))
       (d0 (get-field *queue3$d0* st))
       (l1 (get-field *queue3$l1* st))
       (d1 (get-field *queue3$d1* st))
       (l2 (get-field *queue3$l2* st))
       (d2 (get-field *queue3$d2* st)))
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
         (equal (len d2) *data-width*))))

(defun queue3$map-to-links (st)
  (b* ((l0 (get-field *queue3$l0* st))
       (d0 (get-field *queue3$d0* st))
       (l1 (get-field *queue3$l1* st))
       (d1 (get-field *queue3$d1* st))
       (l2 (get-field *queue3$l2* st))
       (d2 (get-field *queue3$d2* st)))
    (map-to-links (list (list 'l0 l0 d0)
                        (list 'l1 l1 d1)
                        (list 'l2 l2 d2)))))

(defun queue3$map-to-links-list (x)
  (if (atom x)
      nil
    (cons (queue3$map-to-links (car x))
          (queue3$map-to-links-list (cdr x)))))

(defund queue3$sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *queue3$ins-len*)
       ((mv inputs-lst state) (go-vals-gen num-signals n state nil))
       ;;(- (cw "~x0~%" inputs-lst))
       (empty '(nil))
       (invalid-data (make-list *data-width* :initial-element '(x)))
       (st (list empty invalid-data
                 empty invalid-data
                 empty invalid-data)))
    (mv (pretty-list
         (remove-dup-neighbors
          (queue3$map-to-links-list
           (de-sim-list 'queue3 inputs-lst st (queue3$netlist))))
         0)
        state)))

(defun queue3$get-data-in (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (subseq-list inputs 2 (+ 2 *data-width*)))

(defthm len-queue3$get-data-in
  (equal (len (queue3$get-data-in inputs))
         *data-width*))

(in-theory (disable queue3$get-data-in))

(defund queue3$in-act (inputs st)
  (b* ((full-in (nth 0 inputs))
       (go-signals (nthcdr *queue3$data-ins-len* inputs))
       (go-in (nth 0 go-signals))

       (l0 (get-field *queue3$l0* st)))
    (joint-act full-in (car l0) go-in)))

(defund queue3$out-act (inputs st)
  (b* ((full-out- (nth 1 inputs))
       (go-signals (nthcdr *queue3$data-ins-len* inputs))
       (go-out (nth 3 go-signals))

       (l2 (get-field *queue3$l2* st)))
    (joint-act (car l2) full-out- go-out)))

(defund queue3$data-out (st)
  (strip-cars (get-field *queue3$d2* st)))

(defthm queue3$data-out-props
   (implies (queue3$valid-st st)
            (and (bvp (queue3$data-out st))
                 (equal (len (queue3$data-out st))
                        *data-width*)))
   :hints (("Goal" :in-theory (enable queue3$valid-st
                                      queue3$data-out))))

(defthmd queue3$value
  (b* ((inputs (list* full-in full-out- (append data-in go-signals))))
    (implies (and (queue3& netlist)
                  (equal (len data-in) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue3$go-num*)
                  (queue3$valid-st st))
             (equal (se 'queue3 inputs st netlist)
                    (list* (queue3$in-act inputs st)
                           (queue3$out-act inputs st)
                           (queue3$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (se-rules
                            get-field
                            len-1-true-listp=>true-listp
                            queue3&
                            queue3*$destructure
                            joint-cntl$value
                            latch-n$value
                            v-buf$value
                            queue3$valid-st
                            queue3$in-act
                            queue3$out-act
                            queue3$data-out)
                           ((queue3*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(defun queue3$state-fn (inputs st)
  (b* ((data-in    (queue3$get-data-in inputs))
       (go-signals (nthcdr *queue3$data-ins-len* inputs))

       (go-trans1 (nth 1 go-signals))
       (go-trans2 (nth 2 go-signals))
       
       (l0 (get-field *queue3$l0* st))
       (d0 (get-field *queue3$d0* st))
       (l1 (get-field *queue3$l1* st))
       (d1 (get-field *queue3$d1* st))
       (l2 (get-field *queue3$l2* st))
       (d2 (get-field *queue3$d2* st))

       (in-act (queue3$in-act inputs st))
       (out-act (queue3$out-act inputs st))
       (trans1-act (joint-act (car l0) (car l1) go-trans1))
       (trans2-act (joint-act (car l1) (car l2) go-trans2)))
    (list
     (list (f-sr in-act trans1-act (car l0)))
     (pairlis$ (fv-if in-act data-in (strip-cars d0))
               nil)
     
     (list (f-sr trans1-act trans2-act (car l1)))
     (pairlis$ (fv-if trans1-act (strip-cars d0) (strip-cars d1))
               nil)
     
     (list (f-sr trans2-act out-act (car l2)))
     (pairlis$ (fv-if trans2-act (strip-cars d1) (strip-cars d2))
               nil))))

(defthm len-of-queue3$state-fn
  (equal (len (queue3$state-fn inputs st))
         *queue3$st-len*))

(defthmd queue3$state
  (b* ((inputs (list* full-in full-out- (append data-in go-signals))))
    (implies (and (queue3& netlist)
                  (true-listp data-in)
                  (equal (len data-in) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue3$go-num*)
                  (queue3$valid-st st))
             (equal (de 'queue3 inputs st netlist)
                    (queue3$state-fn inputs st))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (de-rules
                            get-field
                            len-1-true-listp=>true-listp
                            queue3&
                            queue3*$destructure
                            queue3$valid-st
                            queue3$get-data-in
                            queue3$in-act
                            queue3$out-act
                            joint-cntl$value
                            latch-n$value latch-n$state
                            v-buf$value)
                           ((queue3*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(in-theory (disable queue3$state-fn))

;; ======================================================================

(defund queue3$input-format (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((full-in    (nth 0 inputs))
       (full-out-  (nth 1 inputs))
       (data-in    (queue3$get-data-in inputs))
       (go-signals (nthcdr *queue3$data-ins-len* inputs)))
    (and
     (booleanp full-in)
     (booleanp full-out-)
     (bvp data-in)
     (true-listp go-signals)
     (= (len go-signals) *queue3$go-num*)
     (equal inputs
            (list* full-in full-out- (append data-in go-signals))))))

(defthm queue3$valid-st-preserved
  (implies (and (queue3$input-format inputs)
                (queue3$valid-st st))
           (queue3$valid-st (queue3$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue3$input-format
                            queue3$valid-st
                            queue3$state-fn
                            queue3$in-act
                            queue3$out-act
                            f-sr)
                           (if*
                            nth
                            nthcdr
                            acl2::true-listp-append)))))

(defthmd queue3$state-alt
  (implies (and (queue3& netlist)
                (queue3$input-format inputs)
                (queue3$valid-st st))
           (equal (de 'queue3 inputs st netlist)
                  (queue3$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (enable queue3$input-format)
           :use (:instance queue3$state
                           (full-in    (nth 0 inputs))
                           (full-out-  (nth 1 inputs))
                           (data-in    (queue3$get-data-in inputs))
                           (go-signals (nthcdr *queue3$data-ins-len*
                                               inputs))))))

(state-fn-n-gen queue3)

(input-format-n-gen queue3)

(defthmd de-sim-n$queue3
  (implies (and (queue3& netlist)
                (queue3$input-format-n inputs-lst n)
                (queue3$valid-st st))
           (equal (de-sim-n 'queue3 inputs-lst st netlist n)
                  (queue3$state-fn-n inputs-lst st n)))
  :hints (("Goal" :in-theory (enable queue3$state-alt))))

;; ======================================================================

(defund queue3$extract-state (st)
  (b* ((l0 (get-field *queue3$l0* st))
       (d0 (get-field *queue3$d0* st))
       (l1 (get-field *queue3$l1* st))
       (d1 (get-field *queue3$d1* st))
       (l2 (get-field *queue3$l2* st))
       (d2 (get-field *queue3$d2* st)))
    (extract-state (list l0 d0 l1 d1 l2 d2))))

(defun queue3$in-seq (inputs-lst st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue3$in-act inputs st) t)
          (append (queue3$in-seq (cdr inputs-lst)
                                 (queue3$state-fn inputs st)
                                 (1- n))
                  (list (pairlis$ (queue3$get-data-in inputs)
                                  nil)))
        (queue3$in-seq (cdr inputs-lst)
                       (queue3$state-fn inputs st)
                       (1- n))))))

(defun queue3$out-seq (inputs-lst st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst))
         (extracted-st (queue3$extract-state st)))
      (if (equal (queue3$out-act inputs st) t)
          (append (queue3$out-seq (cdr inputs-lst)
                                  (queue3$state-fn inputs st)
                                  (1- n))
                  (list (nth (1- (len extracted-st))
                             extracted-st)))
        (queue3$out-seq (cdr inputs-lst)
                        (queue3$state-fn inputs st)
                        (1- n))))))

(defund queue3$in-out-seq-sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *queue3$ins-len*)
       ((mv inputs-lst state)
        (go-vals-gen num-signals n state nil))
       (empty '(nil))
       (invalid-data (make-list *data-width* :initial-element '(x)))
       (st (list empty invalid-data
                 empty invalid-data
                 empty invalid-data)))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-flatten-lst
                   (queue3$in-seq inputs-lst st n))))
      (list (cons 'out-seq
                  (v-to-nat-flatten-lst
                   (queue3$out-seq inputs-lst st n)))))
     state)))

(defund queue3$step-spec (inputs st)
  (b* ((data-in (queue3$get-data-in inputs))
       (extracted-st (queue3$extract-state st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue3$out-act inputs st) t)
      (cond
       ((equal (queue3$in-act inputs st) t)
        (cons (pairlis$ data-in nil)
              (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue3$in-act inputs st) t)
          (cons (pairlis$ data-in nil)
                extracted-st))
         (t extracted-st))))))

(defthm queue3$step-spec-correct
  (b* ((next-st (queue3$state-fn inputs st)))
    (implies (and (queue3$input-format inputs)
                  (queue3$valid-st st))
             (equal (queue3$extract-state next-st)
                    (queue3$step-spec inputs st))))
  :hints (("Goal"
           :in-theory (enable get-field
                              queue3$step-spec
                              queue3$input-format
                              queue3$valid-st
                              queue3$state-fn
                              queue3$in-act
                              queue3$out-act
                              queue3$extract-state))))

(defthm consp-queue3$extract-state
  (implies (and (queue3$valid-st st)
                (queue3$out-act inputs st))
           (consp (queue3$extract-state st)))
  :hints (("Goal"
           :in-theory (enable queue3$valid-st
                              queue3$extract-state
                              queue3$out-act)))
  :rule-classes :type-prescription)

(encapsulate
  ()

  (local
   (defthm queue3$dataflow-correct-aux
     (implies (equal (append x1 y1)
                     (append (queue3$in-seq inputs-lst st n) y2))
              (equal (append x1 y1 z)
                     (append (queue3$in-seq inputs-lst st n) y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (acl2::associativity-of-append))))))

  (defthmd queue3$dataflow-correct
    (b* ((extracted-st (queue3$extract-state st))
         (final-st (queue3$state-fn-n inputs-lst st n))
         (final-extracted-st (queue3$extract-state final-st)))
      (implies (and (queue3$input-format-n inputs-lst n)
                    (queue3$valid-st st))
               (equal (append final-extracted-st
                              (queue3$out-seq inputs-lst st n))
                      (append (queue3$in-seq inputs-lst st n)
                              extracted-st))))
    :hints (("Goal"
             :in-theory (e/d (queue3$step-spec)
                             ()))))
  )

