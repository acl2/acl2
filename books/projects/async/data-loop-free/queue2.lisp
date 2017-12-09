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

(defconst *queue2$data-ins-len* (+ 2 *data-width*))
(defconst *queue2$go-num* 3)
(defconst *queue2$ins-len* (+ *queue2$data-ins-len*
                             *queue2$go-num*))
(defconst *queue2$st-len* 4)

;; A 2-link queue module: -> L0 -> L1 ->

(module-generator
 queue2* ()
 'queue2
 (list* 'full-in 'full-out- (append (sis 'data-in 0 *data-width*)
                                    (sis 'go 0 *queue2$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 *data-width*))
 '(l0 d0 l1 d1)
 (list
  ;; LINKS
  ;; L0
  '(l0 (l0-status) link-cntl (in-act trans-act))
  (list 'd0
        (sis 'd0-out 0 *data-width*)
        (si 'latch-n *data-width*)
        (list* 'in-act (sis 'd0-in 0 *data-width*)))

  ;; L1
  '(l1 (l1-status) link-cntl (trans-act out-act))
  (list 'd1
        (sis 'd1-out 0 *data-width*)
        (si 'latch-n *data-width*)
        (list* 'trans-act (sis 'd1-in 0 *data-width*)))

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

  ;; Transfer data
  (list 'trans-cntl
        '(trans-act)
        'joint-cntl
        (list 'l0-status 'l1-status (si 'go 1)))
  (list 'trans-op
        (sis 'd1-in 0 *data-width*)
        (si 'v-buf *data-width*)
        (sis 'd0-out 0 *data-width*))

  ;; Out
  (list 'out-cntl
        '(out-act)
        'joint-cntl
        (list 'l1-status 'full-out- (si 'go 2)))
  (list 'out-op
        (sis 'data-out 0 *data-width*)
        (si 'v-buf *data-width*)
        (sis 'd1-out 0 *data-width*)))

 :guard t)

(defun queue2$netlist ()
  (declare (xargs :guard t))
  (cons (queue2*)
        (union$ (latch-n$netlist *data-width*)
                (v-buf$netlist *data-width*)
                *joint-cntl*
                :test 'equal)))

(defthmd queue2$netlist-okp
  (and (net-syntax-okp (queue2$netlist))
       (net-arity-okp (queue2$netlist))))

(defund queue2& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (and (equal (assoc 'queue2 netlist)
              (queue2*))
       (b* ((netlist (delete-to-eq 'queue2 netlist)))
         (and (joint-cntl& netlist)
              (latch-n& netlist *data-width*)
              (v-buf& netlist *data-width*)))))

(defthm check-queue2$netlist
  (queue2& (queue2$netlist)))

(defconst *queue2$l0* 0)
(defconst *queue2$d0* 1)
(defconst *queue2$l1* 2)
(defconst *queue2$d1* 3)

(defund queue2$valid-st (st)
  (b* ((l0 (get-field *queue2$l0* st))
       (d0 (get-field *queue2$d0* st))
       (l1 (get-field *queue2$l1* st))
       (d1 (get-field *queue2$d1* st)))
    (and (validp l0)
         (len-1-true-listp d0)
         (bvp (strip-cars d0))
         (equal (len d0) *data-width*)
         
         (validp l1)
         (len-1-true-listp d1)
         (bvp (strip-cars d1))
         (equal (len d1) *data-width*))))

(defun queue2$map-to-links (st)
  (b* ((l0 (get-field *queue2$l0* st))
       (d0 (get-field *queue2$d0* st))
       (l1 (get-field *queue2$l1* st))
       (d1 (get-field *queue2$d1* st)))
    (map-to-links (list (list 'l0 l0 d0)
                        (list 'l1 l1 d1)))))

(defun queue2$map-to-links-list (x)
  (if (atom x)
      nil
    (cons (queue2$map-to-links (car x))
          (queue2$map-to-links-list (cdr x)))))

(defund queue2$sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *queue2$ins-len*)
       ((mv inputs-lst state) (go-vals-gen num-signals n state nil))
       ;;(- (cw "~x0~%" inputs-lst))
       (empty '(nil))
       (invalid-data (make-list *data-width* :initial-element '(x)))
       (st (list empty invalid-data
                 empty invalid-data)))
    (mv (pretty-list
         (remove-dup-neighbors
          (queue2$map-to-links-list
           (de-sim-list 'queue2 inputs-lst st (queue2$netlist))))
         0)
        state)))

(defun queue2$get-data-in (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (subseq-list inputs 2 (+ 2 *data-width*)))

(defthm len-queue2$get-data-in
  (equal (len (queue2$get-data-in inputs))
         *data-width*))

(in-theory (disable queue2$get-data-in))

(defund queue2$in-act (inputs st)
  (b* ((full-in (nth 0 inputs))
       (go-signals (nthcdr *queue2$data-ins-len* inputs))
       (go-in (nth 0 go-signals))

       (l0 (get-field *queue2$l0* st)))
    (joint-act full-in (car l0) go-in)))

(defund queue2$out-act (inputs st)
  (b* ((full-out- (nth 1 inputs))
       (go-signals (nthcdr *queue2$data-ins-len* inputs))
       (go-out (nth 2 go-signals))

       (l1 (get-field *queue2$l1* st)))
    (joint-act (car l1) full-out- go-out)))

(defund queue2$data-out (st)
  (strip-cars (get-field *queue2$d1* st)))

(defthm queue2$data-out-props
   (implies (queue2$valid-st st)
            (and (bvp (queue2$data-out st))
                 (equal (len (queue2$data-out st))
                        *data-width*)))
   :hints (("Goal" :in-theory (enable queue2$valid-st
                                      queue2$data-out))))

(defthmd queue2$value
  (b* ((inputs (list* full-in full-out- (append data-in go-signals))))
    (implies (and (queue2& netlist)
                  (equal (len data-in) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue2$go-num*)
                  (queue2$valid-st st))
             (equal (se 'queue2 inputs st netlist)
                    (list* (queue2$in-act inputs st)
                           (queue2$out-act inputs st)
                           (queue2$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (se-rules
                            get-field
                            len-1-true-listp=>true-listp
                            queue2&
                            queue2*$destructure
                            joint-cntl$value
                            latch-n$value
                            v-buf$value
                            queue2$valid-st
                            queue2$in-act
                            queue2$out-act
                            queue2$data-out)
                           ((queue2*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(defun queue2$state-fn (inputs st)
  (b* ((data-in    (queue2$get-data-in inputs))
       (go-signals (nthcdr *queue2$data-ins-len* inputs))

       (go-trans (nth 1 go-signals))
       
       (l0 (get-field *queue2$l0* st))
       (d0 (get-field *queue2$d0* st))
       (l1 (get-field *queue2$l1* st))
       (d1 (get-field *queue2$d1* st))

       (in-act (queue2$in-act inputs st))
       (out-act (queue2$out-act inputs st))
       (trans-act (joint-act (car l0) (car l1) go-trans)))
    (list
     (list (f-sr in-act trans-act (car l0)))
     (pairlis$ (fv-if in-act data-in (strip-cars d0))
               nil)
     
     (list (f-sr trans-act out-act (car l1)))
     (pairlis$ (fv-if trans-act (strip-cars d0) (strip-cars d1))
               nil))))

(defthm len-of-queue2$state-fn
  (equal (len (queue2$state-fn inputs st))
         *queue2$st-len*))

(defthmd queue2$state
  (b* ((inputs (list* full-in full-out- (append data-in go-signals))))
    (implies (and (queue2& netlist)
                  (true-listp data-in)
                  (equal (len data-in) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue2$go-num*)
                  (queue2$valid-st st))
             (equal (de 'queue2 inputs st netlist)
                    (queue2$state-fn inputs st))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (de-rules
                            get-field
                            len-1-true-listp=>true-listp
                            queue2&
                            queue2*$destructure
                            queue2$valid-st
                            queue2$get-data-in
                            queue2$in-act
                            queue2$out-act
                            joint-cntl$value
                            latch-n$value latch-n$state
                            v-buf$value)
                           ((queue2*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(in-theory (disable queue2$state-fn))

;; ======================================================================

(defund queue2$input-format (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((full-in    (nth 0 inputs))
       (full-out-  (nth 1 inputs))
       (data-in    (queue2$get-data-in inputs))
       (go-signals (nthcdr *queue2$data-ins-len* inputs)))
    (and
     (booleanp full-in)
     (booleanp full-out-)
     (bvp data-in)
     (true-listp go-signals)
     (= (len go-signals) *queue2$go-num*)
     (equal inputs
            (list* full-in full-out- (append data-in go-signals))))))

(defthm queue2$valid-st-preserved
  (implies (and (queue2$input-format inputs)
                (queue2$valid-st st))
           (queue2$valid-st (queue2$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue2$input-format
                            queue2$valid-st
                            queue2$state-fn
                            queue2$in-act
                            queue2$out-act
                            f-sr)
                           (if*
                            nth
                            nthcdr
                            acl2::true-listp-append)))))

(defthmd queue2$state-alt
  (implies (and (queue2& netlist)
                (queue2$input-format inputs)
                (queue2$valid-st st))
           (equal (de 'queue2 inputs st netlist)
                  (queue2$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (enable queue2$input-format)
           :use (:instance queue2$state
                           (full-in    (nth 0 inputs))
                           (full-out-  (nth 1 inputs))
                           (data-in    (queue2$get-data-in inputs))
                           (go-signals (nthcdr *queue2$data-ins-len*
                                               inputs))))))

(state-fn-n-gen queue2)

(input-format-n-gen queue2)

(defthmd de-sim-n$queue2
  (implies (and (queue2& netlist)
                (queue2$input-format-n inputs-lst n)
                (queue2$valid-st st))
           (equal (de-sim-n 'queue2 inputs-lst st netlist n)
                  (queue2$state-fn-n inputs-lst st n)))
  :hints (("Goal" :in-theory (enable queue2$state-alt))))

;; ======================================================================

(defund queue2$extract-state (st)
  (declare (xargs :guard (true-listp st)))
  (b* ((l0 (get-field *queue2$l0* st))
       (d0 (get-field *queue2$d0* st))
       (l1 (get-field *queue2$l1* st))
       (d1 (get-field *queue2$d1* st)))
    (extract-state (list l0 d0 l1 d1))))

(defun queue2$in-seq (inputs-lst st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue2$in-act inputs st) t)
          (append (queue2$in-seq (cdr inputs-lst)
                                 (queue2$state-fn inputs st)
                                 (1- n))
                  (list (pairlis$ (queue2$get-data-in inputs)
                                  nil)))
        (queue2$in-seq (cdr inputs-lst)
                       (queue2$state-fn inputs st)
                       (1- n))))))

(defun queue2$out-seq (inputs-lst st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst))
         (extracted-st (queue2$extract-state st)))
      (if (equal (queue2$out-act inputs st) t)
          (append (queue2$out-seq (cdr inputs-lst)
                                  (queue2$state-fn inputs st)
                                  (1- n))
                  (list (nth (1- (len extracted-st))
                             extracted-st)))
        (queue2$out-seq (cdr inputs-lst)
                        (queue2$state-fn inputs st)
                        (1- n))))))

(defund queue2$in-out-seq-sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *queue2$ins-len*)
       ((mv inputs-lst state)
        (go-vals-gen num-signals n state nil))
       (empty '(nil))
       (invalid-data (make-list *data-width* :initial-element '(x)))
       (st (list empty invalid-data
                 empty invalid-data)))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-flatten-lst
                   (queue2$in-seq inputs-lst st n))))
      (list (cons 'out-seq
                  (v-to-nat-flatten-lst
                   (queue2$out-seq inputs-lst st n)))))
     state)))

(defund queue2$step-spec (inputs st)
  (b* ((data-in (queue2$get-data-in inputs))
       (extracted-st (queue2$extract-state st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue2$out-act inputs st) t)
      (cond
       ((equal (queue2$in-act inputs st) t)
        (cons (pairlis$ data-in nil)
              (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue2$in-act inputs st) t)
          (cons (pairlis$ data-in nil)
                extracted-st))
         (t extracted-st))))))

(defthm queue2$step-spec-correct
  (b* ((next-st (queue2$state-fn inputs st)))
    (implies (and (queue2$input-format inputs)
                  (queue2$valid-st st))
             (equal (queue2$extract-state next-st)
                    (queue2$step-spec inputs st))))
  :hints (("Goal"
           :in-theory (enable get-field
                              queue2$step-spec
                              queue2$input-format
                              queue2$valid-st
                              queue2$state-fn
                              queue2$in-act
                              queue2$out-act
                              queue2$extract-state))))

(defthm consp-queue2$extract-state
  (implies (and (queue2$valid-st st)
                (queue2$out-act inputs st))
           (consp (queue2$extract-state st)))
  :hints (("Goal"
           :in-theory (enable queue2$valid-st
                              queue2$extract-state
                              queue2$out-act)))
  :rule-classes :type-prescription)

(encapsulate
  ()

  (local
   (defthm queue2$dataflow-correct-aux
     (implies (equal (append x1 y1)
                     (append (queue2$in-seq inputs-lst st n) y2))
              (equal (append x1 y1 z)
                     (append (queue2$in-seq inputs-lst st n) y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (acl2::associativity-of-append))))))

  (defthmd queue2$dataflow-correct
    (b* ((extracted-st (queue2$extract-state st))
         (final-st (queue2$state-fn-n inputs-lst st n))
         (final-extracted-st (queue2$extract-state final-st)))
      (implies (and (queue2$input-format-n inputs-lst n)
                    (queue2$valid-st st))
               (equal (append final-extracted-st
                              (queue2$out-seq inputs-lst st n))
                      (append (queue2$in-seq inputs-lst st n)
                              extracted-st))))
    :hints (("Goal"
             :in-theory (e/d (queue2$step-spec)
                             ()))))
  )

