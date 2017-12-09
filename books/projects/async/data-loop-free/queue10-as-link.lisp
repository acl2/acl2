;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; December 2017

(in-package "ADE")

(include-book "queue5-as-link")

(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (e/d (f-buf-delete-lemmas-1
                        f-buf-delete-lemmas-2)
                       (nth-of-bvp-is-booleanp
                        take-of-len-free))))

;; ======================================================================

(defconst *queue10$data-ins-len* (+ 2 *data-width*))
(defconst *queue10$prim-go-num* 1)
(defconst *queue10$go-num* (+ *queue10$prim-go-num*
                             (* 2 *queue5$go-num*)))
(defconst *queue10$ins-len* (+ *queue10$data-ins-len*
                              *queue10$go-num*))
(defconst *queue10$st-len* 2)

;; A 10-link queue module: Q5 -> Q5

(module-generator
 queue10* ()
 'queue10
 (list* 'in-act 'out-act (append (sis 'data-in 0 *data-width*)
                                 (sis 'go 0 *queue10$go-num*)))
 (list* 'ready-in- 'ready-out
        (sis 'data-out 0 *data-width*))
 '(q5-0 q5-1)
 (list
  ;; LINKS
  ;; 5-link queue Q5-0
  (list 'q5-0
        (list* 'ready-in- 'q5-0-ready-out
               (sis 'q5-0-data-out 0 *data-width*))
        'queue5
        (list* 'in-act 'trans-act
               (append (sis 'data-in 0 *data-width*)
                       (sis 'go
                            *queue10$prim-go-num*
                            *queue5$go-num*))))

  ;; 5-link queue Q5-1
  (list 'q5-1
        (list* 'q5-1-ready-in- 'ready-out
               (sis 'data-out 0 *data-width*))
        'queue5
        (list* 'trans-act 'out-act
               (append (sis 'q5-1-data-in 0 *data-width*)
                       (sis 'go
                            (+ *queue10$prim-go-num*
                               *queue5$go-num*)
                            *queue5$go-num*))))

  ;; JOINT
  ;; Transfer data from Q5-0 to Q5-1
  (list 'trans-cntl
        '(trans-act)
        'joint-cntl
        (list 'q5-0-ready-out 'q5-1-ready-in- (si 'go 0)))
  (list 'trans-op
        (sis 'q5-1-data-in 0 *data-width*)
        (si 'v-buf *data-width*)
        (sis 'q5-0-data-out 0 *data-width*)))

 :guard t)

(defun queue10$netlist ()
  (declare (xargs :guard t))
  (cons (queue10*)
        (union$ (queue5$netlist)
                :test 'equal)))

(defthmd queue10$netlist-okp
  (and (net-syntax-okp (queue10$netlist))
       (net-arity-okp (queue10$netlist))))

(defund queue10& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (and (equal (assoc 'queue10 netlist)
              (queue10*))
       (b* ((netlist (delete-to-eq 'queue10 netlist)))
         (and (joint-cntl& netlist)
              (v-buf& netlist *data-width*)
              (queue5& netlist)))))

(defthm check-queue10$netlist
  (queue10& (queue10$netlist)))

(defconst *queue10$q5-0* 0)
(defconst *queue10$q5-1* 1)

(defund queue10$valid-st (st)
  (b* ((q5-0 (get-field *queue10$q5-0* st))
       (q5-1 (get-field *queue10$q5-1* st)))
    (and (queue5$valid-st q5-0)
         (queue5$valid-st q5-1))))

(defun queue10$map-to-links (st)
  (b* ((q5-0 (get-field *queue10$q5-0* st))
       (q5-1 (get-field *queue10$q5-1* st)))
    (append (list (cons 'Q5-0 (queue5$map-to-links q5-0)))
            (list (cons 'Q5-1 (queue5$map-to-links q5-1))))))

(defun queue10$map-to-links-list (x)
  (if (atom x)
      nil
    (cons (queue10$map-to-links (car x))
          (queue10$map-to-links-list (cdr x)))))

(defund queue10$sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *queue10$ins-len*)
       ((mv inputs-lst state) (go-vals-gen num-signals n state nil))
       ;;(- (cw "~x0~%" inputs-lst))
       (empty '(nil))
       (invalid-data (make-list *data-width* :initial-element '(x)))
       (q5-0 (list empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data))
       (q5-1 (list empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data))
       (st (list q5-0 q5-1)))
    (mv (pretty-list
         (remove-dup-neighbors
          (queue10$map-to-links-list
           (de-sim-list 'queue10 inputs-lst st (queue10$netlist))))
         0)
        state)))

(defund queue10$in-act (inputs)
  (nth 0 inputs))

(defund queue10$out-act (inputs)
  (nth 1 inputs))

(defun queue10$get-data-in (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (subseq-list inputs 2 (+ 2 *data-width*)))

(defthm len-queue10$get-data-in
  (equal (len (queue10$get-data-in inputs))
         *data-width*))

(in-theory (disable queue10$get-data-in))

(defund queue10$q5-0-inputs (inputs st)
  (b* ((in-act (queue10$in-act inputs))
       (data-in (queue10$get-data-in inputs))
       (go-signals (nthcdr *queue10$data-ins-len* inputs))

       (go-trans (nth 0 go-signals))
       (q5-0-go-signals (take *queue5$go-num*
                              (nthcdr *queue10$prim-go-num* go-signals)))

       (q5-0 (get-field *queue10$q5-0* st))
       (q5-1 (get-field *queue10$q5-1* st))

       (trans-act (joint-act (queue5$ready-out q5-0)
                             (queue5$ready-in- q5-1)
                             go-trans)))
    
    (list* in-act trans-act
           (append data-in q5-0-go-signals))))

(defund queue10$q5-1-inputs (inputs st)
  (b* ((out-act (queue10$out-act inputs))
       (go-signals (nthcdr *queue10$data-ins-len* inputs))

       (go-trans (nth 0 go-signals))
       (q5-1-go-signals (take *queue5$go-num*
                              (nthcdr (+ *queue10$prim-go-num*
                                         *queue5$go-num*)
                                      go-signals)))

       (q5-0 (get-field *queue10$q5-0* st))
       (q5-1 (get-field *queue10$q5-1* st))

       (trans-act (joint-act (queue5$ready-out q5-0)
                             (queue5$ready-in- q5-1)
                             go-trans)))
    
    (list* trans-act out-act
           (append (queue5$data-out q5-0)
                   q5-1-go-signals))))

(defund queue10$ready-in- (st)
  (b* ((q5-0 (get-field *queue10$q5-0* st)))
    (queue5$ready-in- q5-0)))

(defthm booleanp-queue10$ready-in-
  (implies (queue10$valid-st st)
           (booleanp (queue10$ready-in- st)))
  :hints (("Goal" :in-theory (enable queue10$valid-st
                                     queue10$ready-in-)))
  :rule-classes :type-prescription)

(defund queue10$ready-out (st)
  (b* ((q5-1 (get-field *queue10$q5-1* st)))
    (queue5$ready-out q5-1)))

(defthm booleanp-queue10$ready-out
  (implies (queue10$valid-st st)
           (booleanp (queue10$ready-out st)))
  :hints (("Goal" :in-theory (enable queue10$valid-st
                                     queue10$ready-out)))
  :rule-classes :type-prescription)

(defund queue10$data-out (st)
  (b* ((q5-1 (get-field *queue10$q5-1* st)))
    (queue5$data-out q5-1)))

(defthm queue10$data-out-props
   (implies (queue10$valid-st st)
            (and (bvp (queue10$data-out st))
                 (equal (len (queue10$data-out st))
                        *data-width*)))
   :hints (("Goal" :in-theory (enable queue10$valid-st
                                      queue10$data-out))))

(defthmd queue10$value
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue10& netlist)
                  (queue10$valid-st st))
             (equal (se 'queue10 inputs st netlist)
                    (list* (queue10$ready-in- st)
                           (queue10$ready-out st)
                           (queue10$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (se-rules
                            get-field
                            open-nth
                            len-1-true-listp=>true-listp
                            queue10&
                            queue10*$destructure
                            joint-cntl$value
                            v-buf$value
                            queue5$value
                            queue10$valid-st
                            queue10$ready-in-
                            queue10$ready-out
                            queue10$data-out)
                           ((queue10*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(defun queue10$state-fn (inputs st)
  (b* ((q5-0 (get-field *queue10$q5-0* st))
       (q5-1 (get-field *queue10$q5-1* st))

       (q5-0-inputs (queue10$q5-0-inputs inputs st))
       (q5-1-inputs (queue10$q5-1-inputs inputs st)))
    (list
     (queue5$state-fn q5-0-inputs q5-0)
     (queue5$state-fn q5-1-inputs q5-1))))

(defthm len-of-queue10$state-fn
  (equal (len (queue10$state-fn inputs st))
         *queue10$st-len*))

(defthmd queue10$state
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue10& netlist)
                  (true-listp data-in)
                  (equal (len data-in) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue10$go-num*)
                  (queue10$valid-st st))
             (equal (de 'queue10 inputs st netlist)
                    (queue10$state-fn inputs st))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (de-rules
                            get-field
                            open-nth
                            len-1-true-listp=>true-listp
                            queue10&
                            queue10*$destructure
                            queue10$valid-st
                            queue10$in-act
                            queue10$out-act
                            queue10$get-data-in
                            queue10$q5-0-inputs
                            queue10$q5-1-inputs
                            joint-cntl$value
                            v-buf$value
                            queue5$value queue5$state)
                           ((queue10*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(in-theory (disable queue10$state-fn))

;; ======================================================================

(defund queue10$input-format (inputs st)
  (b* ((in-act     (queue10$in-act inputs))
       (out-act    (queue10$out-act inputs))
       (data-in    (queue10$get-data-in inputs))
       (go-signals (nthcdr *queue10$data-ins-len* inputs))

       (ready-in- (queue10$ready-in- st))
       (ready-out (queue10$ready-out st)))
    (and
     (if ready-in-
         (not in-act)
       (booleanp in-act))
     (if (not ready-out)
         (not out-act)
       (booleanp out-act))
     (bvp data-in)
     (true-listp go-signals)
     (= (len go-signals) *queue10$go-num*)
     (equal inputs
            (list* in-act out-act (append data-in go-signals))))))

(local
 (defthm queue10$input-format=>q5-0$input-format
   (implies (and (queue10$input-format inputs st)
                 (queue10$valid-st st))
            (queue5$input-format
             (queue10$q5-0-inputs inputs st)
             (nth *queue10$q5-0* st)))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             queue5$input-format
                             queue5$in-act
                             queue5$out-act
                             queue5$get-data-in
                             queue10$input-format
                             queue10$valid-st
                             queue10$ready-in-
                             queue10$q5-0-inputs)
                            (nth
                             nthcdr
                             take-of-too-many
                             take-of-len-is-itself))))))

(local
 (defthm queue10$input-format=>q5-1$input-format
   (implies (and (queue10$input-format inputs st)
                 (queue10$valid-st st))
            (queue5$input-format
             (queue10$q5-1-inputs inputs st)
             (nth *queue10$q5-1* st)))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             queue5$input-format
                             queue5$in-act
                             queue5$out-act
                             queue5$get-data-in
                             queue10$input-format
                             queue10$valid-st
                             queue10$ready-out
                             queue10$q5-1-inputs)
                            (nth
                             nthcdr
                             take-of-too-many
                             take-of-len-is-itself))))))

(defthm queue10$valid-st-preserved
  (implies (and (queue10$input-format inputs st)
                (queue10$valid-st st))
           (queue10$valid-st (queue10$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue10$valid-st
                            queue10$state-fn)
                           (nth)))))

(defthmd queue10$state-alt
  (implies (and (queue10& netlist)
                (queue10$input-format inputs st)
                (queue10$valid-st st))
           (equal (de 'queue10 inputs st netlist)
                  (queue10$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (enable queue10$input-format)
           :use (:instance queue10$state
                           (in-act     (queue10$in-act inputs))
                           (out-act    (queue10$out-act inputs))
                           (data-in    (queue10$get-data-in inputs))
                           (go-signals (nthcdr *queue10$data-ins-len*
                                               inputs))))))

(state-fn-n-gen queue10)

(input-format-n-with-state-gen queue10)

(defthmd de-sim-n$queue10
  (implies (and (queue10& netlist)
                (queue10$input-format-n inputs-lst st n)
                (queue10$valid-st st))
           (equal (de-sim-n 'queue10 inputs-lst st netlist n)
                  (queue10$state-fn-n inputs-lst st n)))
  :hints (("Goal" :in-theory (enable queue10$state-alt))))

;; ======================================================================

(defund queue10$extract-state (st)
  (b* ((q5-0 (get-field *queue10$q5-0* st))
       (q5-1 (get-field *queue10$q5-1* st)))
    (append (queue5$extract-state q5-0)
            (queue5$extract-state q5-1))))

(defun queue10$in-seq (inputs-lst st n)
  (declare (ignorable st)
           (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue10$in-act inputs) t)
          (append (queue10$in-seq (cdr inputs-lst)
                                 (queue10$state-fn inputs st)
                                 (1- n))
                  (list (pairlis$ (queue10$get-data-in inputs)
                                  nil)))
        (queue10$in-seq (cdr inputs-lst)
                       (queue10$state-fn inputs st)
                       (1- n))))))

(defun queue10$out-seq (inputs-lst st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst))
         (extracted-st (queue10$extract-state st)))
      (if (equal (queue10$out-act inputs) t)
          (append (queue10$out-seq (cdr inputs-lst)
                                  (queue10$state-fn inputs st)
                                  (1- n))
                  (list (nth (1- (len extracted-st))
                             extracted-st)))
        (queue10$out-seq (cdr inputs-lst)
                        (queue10$state-fn inputs st)
                        (1- n))))))

(defund queue10$in-out-seq-sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *queue10$ins-len*)
       ((mv inputs-lst state)
        (go-vals-gen num-signals n state nil))
       (empty '(nil))
       (invalid-data (make-list *data-width* :initial-element '(x)))
       (q5-0 (list empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data))
       (q5-1 (list empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data))
       (st (list q5-0 q5-1)))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-flatten-lst
                   (queue10$in-seq inputs-lst st n))))
      (list (cons 'out-seq
                  (v-to-nat-flatten-lst
                   (queue10$out-seq inputs-lst st n)))))
     state)))

(defund queue10$step-spec (inputs st)
  (b* ((data-in (queue10$get-data-in inputs))
       (extracted-st (queue10$extract-state st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue10$out-act inputs) t)
      (cond
       ((equal (queue10$in-act inputs) t)
        (cons (pairlis$ data-in nil)
              (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue10$in-act inputs) t)
          (cons (pairlis$ data-in nil)
                extracted-st))
         (t extracted-st))))))

(local
 (defthm queue5$ready-out-lemma
   (implies (and (queue5$valid-st st)
                 (equal (len (queue5$extract-state st)) 0))
            (not (queue5$ready-out st)))
   :hints (("Goal" :in-theory (enable queue5$valid-st
                                      queue5$extract-state
                                      queue5$ready-out)))))

(encapsulate
  ()

  (local
   (defthm queue10$q5-0-get-data-in-rewrite
     (equal (queue5$get-data-in
             (queue10$q5-0-inputs inputs st))
            (queue10$get-data-in inputs))
     :hints (("Goal"
              :in-theory (enable queue5$get-data-in
                                 queue10$q5-0-inputs)))))

  (local
   (defthm queue10$q5-1-get-data-in-rewrite
     (b* ((q5-0 (nth *queue10$q5-0* st)))
       (implies (queue5$valid-st q5-0)
                (equal (queue5$get-data-in
                        (queue10$q5-1-inputs inputs st))
                       (queue5$data-out q5-0))))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue5$get-data-in
                                 queue10$q5-1-inputs)))))

  (local
   (defthm queue10$q5-1-in-act-=-q5-0-out-act
     (equal (queue5$in-act (queue10$q5-1-inputs inputs st))
            (queue5$out-act (queue10$q5-0-inputs inputs st)))
     :hints (("Goal" :in-theory (enable queue5$in-act
                                        queue5$out-act
                                        queue10$q5-0-inputs
                                        queue10$q5-1-inputs)))))

  (local
   (defthm queue10$q5-0-in-act-rewrite
     (equal (queue5$in-act (queue10$q5-0-inputs inputs st))
            (queue10$in-act inputs))
     :hints (("Goal" :in-theory (enable queue5$in-act
                                        queue10$in-act
                                        queue10$q5-0-inputs)))))

  (local
   (defthm queue10$q5-1-out-act-rewrite
     (equal (queue5$out-act (queue10$q5-1-inputs inputs st))
            (queue10$out-act inputs))
     :hints (("Goal" :in-theory (enable queue5$out-act
                                        queue10$out-act
                                        queue10$q5-1-inputs)))))

  (local
   (defthm queue5$extract-state-lemma
     (implies (and (queue5$input-format inputs st)
                   (queue5$valid-st st)
                   (equal n (1- (len (queue5$extract-state st))))
                   (queue5$out-act inputs))
              (equal (append
                      (take n (queue5$extract-state st))
                      (list (pairlis$ (queue5$data-out st) nil)))
                     (queue5$extract-state st)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue5$input-format
                                 queue5$valid-st
                                 queue5$extract-state
                                 queue5$ready-in-
                                 queue5$ready-out
                                 queue5$data-out)))))

  (local
   (defthm queue10$step-spec-correct-aux-1
     (equal (append x (cons e (queue5$extract-state st)))
            (append (append x (list e))
                    (queue5$extract-state st)))))

  (local
   (defthm queue10$step-spec-correct-aux-2
     (equal (append x (cons e (take n (queue5$extract-state st))))
            (append (append x (list e))
                    (take n (queue5$extract-state st))))))

  (defthm queue10$step-spec-correct
    (b* ((next-st (queue10$state-fn inputs st)))
      (implies (and (queue10$input-format inputs st)
                    (queue10$valid-st st))
               (equal (queue10$extract-state next-st)
                      (queue10$step-spec inputs st))))
    :hints (("Goal"
             :use queue10$input-format=>q5-0$input-format
             :in-theory (e/d (get-field
                              queue5$step-spec
                              queue10$step-spec
                              queue10$input-format
                              queue10$valid-st
                              queue10$state-fn
                              queue10$in-act
                              queue10$out-act
                              queue10$ready-in-
                              queue10$ready-out
                              queue10$extract-state)
                             (queue10$input-format=>q5-0$input-format
                              acl2::associativity-of-append
                              nth
                              nthcdr
                              len-nthcdr
                              pairlis$
                              strip-cars)))))
  )

(defthm consp-queue10$extract-state
  (implies (and (queue10$input-format inputs st)
                (queue10$valid-st st)
                (queue10$out-act inputs))
           (consp (queue10$extract-state st)))
  :hints (("Goal"
           :in-theory (enable queue10$input-format
                              queue10$valid-st
                              queue10$ready-out
                              queue10$extract-state)))
  :rule-classes :type-prescription)

(encapsulate
  ()

  (local
   (defthm queue10$dataflow-correct-aux
     (implies (equal (append x1 y1)
                     (append (queue10$in-seq inputs-lst st n) y2))
              (equal (append x1 y1 z)
                     (append (queue10$in-seq inputs-lst st n) y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (acl2::associativity-of-append))))))

  (defthmd queue10$dataflow-correct
    (b* ((extracted-st (queue10$extract-state st))
         (final-st (queue10$state-fn-n inputs-lst st n))
         (final-extracted-st (queue10$extract-state final-st)))
      (implies (and (queue10$input-format-n inputs-lst st n)
                    (queue10$valid-st st))
               (equal (append final-extracted-st
                              (queue10$out-seq inputs-lst st n))
                      (append (queue10$in-seq inputs-lst st n)
                              extracted-st))))
    :hints (("Goal"
             :in-theory (e/d (queue10$step-spec)
                             ()))))
  )

