;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; December 2017

(in-package "ADE")

(include-book "queue4-as-link")

(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (e/d (f-buf-delete-lemmas-1
                        f-buf-delete-lemmas-2)
                       (nth-of-bvp-is-booleanp
                        take-of-len-free))))

;; ======================================================================

(defconst *queue8$data-ins-len* (+ 2 *data-width*))
(defconst *queue8$prim-go-num* 1)
(defconst *queue8$go-num* (+ *queue8$prim-go-num*
                             (* 2 *queue4$go-num*)))
(defconst *queue8$ins-len* (+ *queue8$data-ins-len*
                              *queue8$go-num*))
(defconst *queue8$st-len* 2)

;; An 8-link queue module: Q4 -> Q4

(module-generator
 queue8* ()
 'queue8
 (list* 'in-act 'out-act (append (sis 'data-in 0 *data-width*)
                                 (sis 'go 0 *queue8$go-num*)))
 (list* 'ready-in- 'ready-out
        (sis 'data-out 0 *data-width*))
 '(q4-0 q4-1)
 (list
  ;; LINKS
  ;; 4-link queue Q4-0
  (list 'q4-0
        (list* 'ready-in- 'q4-0-ready-out
               (sis 'q4-0-data-out 0 *data-width*))
        'queue4
        (list* 'in-act 'trans-act
               (append (sis 'data-in 0 *data-width*)
                       (sis 'go
                            *queue8$prim-go-num*
                            *queue4$go-num*))))

  ;; 4-link queue Q4-1
  (list 'q4-1
        (list* 'q4-1-ready-in- 'ready-out
               (sis 'data-out 0 *data-width*))
        'queue4
        (list* 'trans-act 'out-act
               (append (sis 'q4-1-data-in 0 *data-width*)
                       (sis 'go
                            (+ *queue8$prim-go-num*
                               *queue4$go-num*)
                            *queue4$go-num*))))

  ;; JOINT
  ;; Transfer data from Q4-0 to Q4-1
  (list 'trans-cntl
        '(trans-act)
        'joint-cntl
        (list 'q4-0-ready-out 'q4-1-ready-in- (si 'go 0)))
  (list 'trans-op
        (sis 'q4-1-data-in 0 *data-width*)
        (si 'v-buf *data-width*)
        (sis 'q4-0-data-out 0 *data-width*)))

 :guard t)

(defun queue8$netlist ()
  (declare (xargs :guard t))
  (cons (queue8*)
        (union$ (queue4$netlist)
                :test 'equal)))

(defthmd queue8$netlist-okp
  (and (net-syntax-okp (queue8$netlist))
       (net-arity-okp (queue8$netlist))))

(defund queue8& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (and (equal (assoc 'queue8 netlist)
              (queue8*))
       (b* ((netlist (delete-to-eq 'queue8 netlist)))
         (and (joint-cntl& netlist)
              (v-buf& netlist *data-width*)
              (queue4& netlist)))))

(defthm check-queue8$netlist
  (queue8& (queue8$netlist)))

(defconst *queue8$q4-0* 0)
(defconst *queue8$q4-1* 1)

(defund queue8$valid-st (st)
  (b* ((q4-0 (get-field *queue8$q4-0* st))
       (q4-1 (get-field *queue8$q4-1* st)))
    (and (queue4$valid-st q4-0)
         (queue4$valid-st q4-1))))

(defun queue8$map-to-links (st)
  (b* ((q4-0 (get-field *queue8$q4-0* st))
       (q4-1 (get-field *queue8$q4-1* st)))
    (append (list (cons 'Q4-0 (queue4$map-to-links q4-0)))
            (list (cons 'Q4-1 (queue4$map-to-links q4-1))))))

(defun queue8$map-to-links-list (x)
  (if (atom x)
      nil
    (cons (queue8$map-to-links (car x))
          (queue8$map-to-links-list (cdr x)))))

(defund queue8$sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *queue8$ins-len*)
       ((mv inputs-lst state) (go-vals-gen num-signals n state nil))
       ;;(- (cw "~x0~%" inputs-lst))
       (empty '(nil))
       (invalid-data (make-list *data-width* :initial-element '(x)))
       (q4-0 (list empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data))
       (q4-1 (list empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data))
       (st (list q4-0 q4-1)))
    (mv (pretty-list
         (remove-dup-neighbors
          (queue8$map-to-links-list
           (de-sim-list 'queue8 inputs-lst st (queue8$netlist))))
         0)
        state)))

(defund queue8$in-act (inputs)
  (nth 0 inputs))

(defund queue8$out-act (inputs)
  (nth 1 inputs))

(defun queue8$get-data-in (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (subseq-list inputs 2 (+ 2 *data-width*)))

(defthm len-queue8$get-data-in
  (equal (len (queue8$get-data-in inputs))
         *data-width*))

(in-theory (disable queue8$get-data-in))

(defund queue8$q4-0-inputs (inputs st)
  (b* ((in-act (queue8$in-act inputs))
       (data-in (queue8$get-data-in inputs))
       (go-signals (nthcdr *queue8$data-ins-len* inputs))

       (go-trans (nth 0 go-signals))
       (q4-0-go-signals (take *queue4$go-num*
                              (nthcdr *queue8$prim-go-num* go-signals)))

       (q4-0 (get-field *queue8$q4-0* st))
       (q4-1 (get-field *queue8$q4-1* st))

       (trans-act (joint-act (queue4$ready-out q4-0)
                             (queue4$ready-in- q4-1)
                             go-trans)))
    
    (list* in-act trans-act
           (append data-in q4-0-go-signals))))

(defund queue8$q4-1-inputs (inputs st)
  (b* ((out-act (queue8$out-act inputs))
       (go-signals (nthcdr *queue8$data-ins-len* inputs))

       (go-trans (nth 0 go-signals))
       (q4-1-go-signals (take *queue4$go-num*
                              (nthcdr (+ *queue8$prim-go-num*
                                         *queue4$go-num*)
                                      go-signals)))

       (q4-0 (get-field *queue8$q4-0* st))
       (q4-1 (get-field *queue8$q4-1* st))

       (trans-act (joint-act (queue4$ready-out q4-0)
                             (queue4$ready-in- q4-1)
                             go-trans)))
    
    (list* trans-act out-act
           (append (queue4$data-out q4-0)
                   q4-1-go-signals))))

(defund queue8$ready-in- (st)
  (b* ((q4-0 (get-field *queue8$q4-0* st)))
    (queue4$ready-in- q4-0)))

(defthm booleanp-queue8$ready-in-
  (implies (queue8$valid-st st)
           (booleanp (queue8$ready-in- st)))
  :hints (("Goal" :in-theory (enable queue8$valid-st
                                     queue8$ready-in-)))
  :rule-classes :type-prescription)

(defund queue8$ready-out (st)
  (b* ((q4-1 (get-field *queue8$q4-1* st)))
    (queue4$ready-out q4-1)))

(defthm booleanp-queue8$ready-out
  (implies (queue8$valid-st st)
           (booleanp (queue8$ready-out st)))
  :hints (("Goal" :in-theory (enable queue8$valid-st
                                     queue8$ready-out)))
  :rule-classes :type-prescription)

(defund queue8$data-out (st)
  (b* ((q4-1 (get-field *queue8$q4-1* st)))
    (queue4$data-out q4-1)))

(defthm queue8$data-out-props
   (implies (queue8$valid-st st)
            (and (bvp (queue8$data-out st))
                 (equal (len (queue8$data-out st))
                        *data-width*)))
   :hints (("Goal" :in-theory (enable queue8$valid-st
                                      queue8$data-out))))

(defthmd queue8$value
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue8& netlist)
                  (queue8$valid-st st))
             (equal (se 'queue8 inputs st netlist)
                    (list* (queue8$ready-in- st)
                           (queue8$ready-out st)
                           (queue8$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (se-rules
                            get-field
                            open-nth
                            len-1-true-listp=>true-listp
                            queue8&
                            queue8*$destructure
                            joint-cntl$value
                            v-buf$value
                            queue4$value
                            queue8$valid-st
                            queue8$ready-in-
                            queue8$ready-out
                            queue8$data-out)
                           ((queue8*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(defun queue8$state-fn (inputs st)
  (b* ((q4-0 (get-field *queue8$q4-0* st))
       (q4-1 (get-field *queue8$q4-1* st))

       (q4-0-inputs (queue8$q4-0-inputs inputs st))
       (q4-1-inputs (queue8$q4-1-inputs inputs st)))
    (list
     (queue4$state-fn q4-0-inputs q4-0)
     (queue4$state-fn q4-1-inputs q4-1))))

(defthm len-of-queue8$state-fn
  (equal (len (queue8$state-fn inputs st))
         *queue8$st-len*))

(defthmd queue8$state
  (b* ((inputs (list* in-act out-act (append data-in go-signals))))
    (implies (and (queue8& netlist)
                  (true-listp data-in)
                  (equal (len data-in) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *queue8$go-num*)
                  (queue8$valid-st st))
             (equal (de 'queue8 inputs st netlist)
                    (queue8$state-fn inputs st))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (de-rules
                            get-field
                            open-nth
                            len-1-true-listp=>true-listp
                            queue8&
                            queue8*$destructure
                            queue8$valid-st
                            queue8$in-act
                            queue8$out-act
                            queue8$get-data-in
                            queue8$q4-0-inputs
                            queue8$q4-1-inputs
                            joint-cntl$value
                            v-buf$value
                            queue4$value queue4$state)
                           ((queue8*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(in-theory (disable queue8$state-fn))

;; ======================================================================

(defund queue8$input-format (inputs st)
  (b* ((in-act     (queue8$in-act inputs))
       (out-act    (queue8$out-act inputs))
       (data-in    (queue8$get-data-in inputs))
       (go-signals (nthcdr *queue8$data-ins-len* inputs))

       (ready-in- (queue8$ready-in- st))
       (ready-out (queue8$ready-out st)))
    (and
     (if ready-in-
         (not in-act)
       (booleanp in-act))
     (if (not ready-out)
         (not out-act)
       (booleanp out-act))
     (bvp data-in)
     (true-listp go-signals)
     (= (len go-signals) *queue8$go-num*)
     (equal inputs
            (list* in-act out-act (append data-in go-signals))))))

(local
 (defthm queue8$input-format=>q4-0$input-format
   (implies (and (queue8$input-format inputs st)
                 (queue8$valid-st st))
            (queue4$input-format
             (queue8$q4-0-inputs inputs st)
             (nth *queue8$q4-0* st)))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             queue4$input-format
                             queue4$in-act
                             queue4$out-act
                             queue4$get-data-in
                             queue8$input-format
                             queue8$valid-st
                             queue8$ready-in-
                             queue8$q4-0-inputs)
                            (nth
                             nthcdr
                             take-of-too-many
                             take-of-len-is-itself))))))

(local
 (defthm queue8$input-format=>q4-1$input-format
   (implies (and (queue8$input-format inputs st)
                 (queue8$valid-st st))
            (queue4$input-format
             (queue8$q4-1-inputs inputs st)
             (nth *queue8$q4-1* st)))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             queue4$input-format
                             queue4$in-act
                             queue4$out-act
                             queue4$get-data-in
                             queue8$input-format
                             queue8$valid-st
                             queue8$ready-out
                             queue8$q4-1-inputs)
                            (nth
                             nthcdr
                             take-of-too-many
                             take-of-len-is-itself))))))

(defthm queue8$valid-st-preserved
  (implies (and (queue8$input-format inputs st)
                (queue8$valid-st st))
           (queue8$valid-st (queue8$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue8$valid-st
                            queue8$state-fn)
                           (nth)))))

(defthmd queue8$state-alt
  (implies (and (queue8& netlist)
                (queue8$input-format inputs st)
                (queue8$valid-st st))
           (equal (de 'queue8 inputs st netlist)
                  (queue8$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (enable queue8$input-format)
           :use (:instance queue8$state
                           (in-act     (queue8$in-act inputs))
                           (out-act    (queue8$out-act inputs))
                           (data-in    (queue8$get-data-in inputs))
                           (go-signals (nthcdr *queue8$data-ins-len*
                                               inputs))))))

(state-fn-n-gen queue8)

(input-format-n-with-state-gen queue8)

(defthmd de-sim-n$queue8
  (implies (and (queue8& netlist)
                (queue8$input-format-n inputs-lst st n)
                (queue8$valid-st st))
           (equal (de-sim-n 'queue8 inputs-lst st netlist n)
                  (queue8$state-fn-n inputs-lst st n)))
  :hints (("Goal" :in-theory (enable queue8$state-alt))))

;; ======================================================================

(defund queue8$extract-state (st)
  (b* ((q4-0 (get-field *queue8$q4-0* st))
       (q4-1 (get-field *queue8$q4-1* st)))
    (append (queue4$extract-state q4-0)
            (queue4$extract-state q4-1))))

(defun queue8$in-seq (inputs-lst st n)
  (declare (ignorable st)
           (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue8$in-act inputs) t)
          (append (queue8$in-seq (cdr inputs-lst)
                                 (queue8$state-fn inputs st)
                                 (1- n))
                  (list (pairlis$ (queue8$get-data-in inputs)
                                  nil)))
        (queue8$in-seq (cdr inputs-lst)
                       (queue8$state-fn inputs st)
                       (1- n))))))

(defun queue8$out-seq (inputs-lst st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst))
         (extracted-st (queue8$extract-state st)))
      (if (equal (queue8$out-act inputs) t)
          (append (queue8$out-seq (cdr inputs-lst)
                                  (queue8$state-fn inputs st)
                                  (1- n))
                  (list (nth (1- (len extracted-st))
                             extracted-st)))
        (queue8$out-seq (cdr inputs-lst)
                        (queue8$state-fn inputs st)
                        (1- n))))))

(defund queue8$in-out-seq-sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *queue8$ins-len*)
       ((mv inputs-lst state)
        (go-vals-gen num-signals n state nil))
       (empty '(nil))
       (invalid-data (make-list *data-width* :initial-element '(x)))
       (q4-0 (list empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data))
       (q4-1 (list empty invalid-data
                   empty invalid-data
                   empty invalid-data
                   empty invalid-data))
       (st (list q4-0 q4-1)))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-flatten-lst
                   (queue8$in-seq inputs-lst st n))))
      (list (cons 'out-seq
                  (v-to-nat-flatten-lst
                   (queue8$out-seq inputs-lst st n)))))
     state)))

(defund queue8$step-spec (inputs st)
  (b* ((data-in (queue8$get-data-in inputs))
       (extracted-st (queue8$extract-state st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue8$out-act inputs) t)
      (cond
       ((equal (queue8$in-act inputs) t)
        (cons (pairlis$ data-in nil)
              (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue8$in-act inputs) t)
          (cons (pairlis$ data-in nil)
                extracted-st))
         (t extracted-st))))))

(local
 (defthm queue4$ready-out-lemma
   (implies (and (queue4$valid-st st)
                 (equal (len (queue4$extract-state st)) 0))
            (not (queue4$ready-out st)))
   :hints (("Goal" :in-theory (enable queue4$valid-st
                                      queue4$extract-state
                                      queue4$ready-out)))))

(encapsulate
  ()

  (local
   (defthm queue8$q4-0-get-data-in-rewrite
     (equal (queue4$get-data-in
             (queue8$q4-0-inputs inputs st))
            (queue8$get-data-in inputs))
     :hints (("Goal"
              :in-theory (enable queue4$get-data-in
                                 queue8$q4-0-inputs)))))

  (local
   (defthm queue8$q4-1-get-data-in-rewrite
     (b* ((q4-0 (nth *queue8$q4-0* st)))
       (implies (queue4$valid-st q4-0)
                (equal (queue4$get-data-in
                        (queue8$q4-1-inputs inputs st))
                       (queue4$data-out q4-0))))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue4$get-data-in
                                 queue8$q4-1-inputs)))))

  (local
   (defthm queue8$q4-1-in-act-=-q4-0-out-act
     (equal (queue4$in-act (queue8$q4-1-inputs inputs st))
            (queue4$out-act (queue8$q4-0-inputs inputs st)))
     :hints (("Goal" :in-theory (enable queue4$in-act
                                        queue4$out-act
                                        queue8$q4-0-inputs
                                        queue8$q4-1-inputs)))))

  (local
   (defthm queue8$q4-0-in-act-rewrite
     (equal (queue4$in-act (queue8$q4-0-inputs inputs st))
            (queue8$in-act inputs))
     :hints (("Goal" :in-theory (enable queue4$in-act
                                        queue8$in-act
                                        queue8$q4-0-inputs)))))

  (local
   (defthm queue8$q4-1-out-act-rewrite
     (equal (queue4$out-act (queue8$q4-1-inputs inputs st))
            (queue8$out-act inputs))
     :hints (("Goal" :in-theory (enable queue4$out-act
                                        queue8$out-act
                                        queue8$q4-1-inputs)))))

  (local
   (defthm queue4$extract-state-lemma
     (implies (and (queue4$input-format inputs st)
                   (queue4$valid-st st)
                   (equal n (1- (len (queue4$extract-state st))))
                   (queue4$out-act inputs))
              (equal (append
                      (take n (queue4$extract-state st))
                      (list (pairlis$ (queue4$data-out st) nil)))
                     (queue4$extract-state st)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue4$input-format
                                 queue4$valid-st
                                 queue4$extract-state
                                 queue4$ready-in-
                                 queue4$ready-out
                                 queue4$data-out)))))

  (local
   (defthm queue8$step-spec-correct-aux-1
     (equal (append x (cons e (queue4$extract-state st)))
            (append (append x (list e))
                    (queue4$extract-state st)))))

  (local
   (defthm queue8$step-spec-correct-aux-2
     (equal (append x (cons e (take n (queue4$extract-state st))))
            (append (append x (list e))
                    (take n (queue4$extract-state st))))))

  (defthm queue8$step-spec-correct
    (b* ((next-st (queue8$state-fn inputs st)))
      (implies (and (queue8$input-format inputs st)
                    (queue8$valid-st st))
               (equal (queue8$extract-state next-st)
                      (queue8$step-spec inputs st))))
    :hints (("Goal"
             :use queue8$input-format=>q4-0$input-format
             :in-theory (e/d (get-field
                              queue4$step-spec
                              queue8$step-spec
                              queue8$input-format
                              queue8$valid-st
                              queue8$state-fn
                              queue8$in-act
                              queue8$out-act
                              queue8$ready-in-
                              queue8$ready-out
                              queue8$extract-state)
                             (queue8$input-format=>q4-0$input-format
                              acl2::associativity-of-append
                              nth
                              nthcdr
                              len-nthcdr
                              pairlis$
                              strip-cars)))))
  )

(defthm consp-queue8$extract-state
  (implies (and (queue8$input-format inputs st)
                (queue8$valid-st st)
                (queue8$out-act inputs))
           (consp (queue8$extract-state st)))
  :hints (("Goal"
           :in-theory (enable queue8$input-format
                              queue8$valid-st
                              queue8$ready-out
                              queue8$extract-state)))
  :rule-classes :type-prescription)

(encapsulate
  ()

  (local
   (defthm queue8$dataflow-correct-aux
     (implies (equal (append x1 y1)
                     (append (queue8$in-seq inputs-lst st n) y2))
              (equal (append x1 y1 z)
                     (append (queue8$in-seq inputs-lst st n) y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (acl2::associativity-of-append))))))

  (defthmd queue8$dataflow-correct
    (b* ((extracted-st (queue8$extract-state st))
         (final-st (queue8$state-fn-n inputs-lst st n))
         (final-extracted-st (queue8$extract-state final-st)))
      (implies (and (queue8$input-format-n inputs-lst st n)
                    (queue8$valid-st st))
               (equal (append final-extracted-st
                              (queue8$out-seq inputs-lst st n))
                      (append (queue8$in-seq inputs-lst st n)
                              extracted-st))))
    :hints (("Goal"
             :in-theory (e/d (queue8$step-spec)
                             ()))))
  )

