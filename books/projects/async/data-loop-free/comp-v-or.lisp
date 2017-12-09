;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; December 2017

(in-package "ADE")

(include-book "queue2")
(include-book "queue3")

(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (e/d (f-buf-delete-lemmas-1
                        f-buf-delete-lemmas-2)
                       (nth-of-bvp-is-booleanp
                        take-of-len-free))))

;; ======================================================================

(defconst *comp-v-or$data-ins-len* (+ 2 (* 2 *data-width*)))
(defconst *comp-v-or$prim-go-num* 2)
(defconst *comp-v-or$go-num* (+ *comp-v-or$prim-go-num*
                                  *queue2$go-num*
                                  *queue3$go-num*))
(defconst *comp-v-or$ins-len* (+ *comp-v-or$data-ins-len*
                                   *comp-v-or$go-num*))
(defconst *comp-v-or$st-len* 10)

;;   -> A0 -Q2-> A1 -
;; -|                |->
;;   -> B0 -Q3-> B1 -

(module-generator
 comp-v-or* ()
 'comp-v-or
 (list* 'full-in 'full-out-
        (append (sis 'a 0 *data-width*)
                (sis 'b 0 *data-width*)
                (sis 'go 0 *comp-v-or$go-num*)))
 (list* 'in-act 'out-act
        (sis 's 0 *data-width*))
 '(la0 a0 lb0 b0 la1 a1 lb1 b1 q2 q3)
 (list
  ;; LINKS
  ;; A0
  '(la0 (a0-status) link-cntl (in-act q2-in-act))
  (list 'a0
        (sis 'a0-out 0 *data-width*)
        (si 'latch-n *data-width*)
        (list* 'in-act (sis 'a0-in 0 *data-width*)))

  ;; B0
  '(lb0 (b0-status) link-cntl (in-act q3-in-act))
  (list 'b0
        (sis 'b0-out 0 *data-width*)
        (si 'latch-n *data-width*)
        (list* 'in-act (sis 'b0-in 0 *data-width*)))
  
  ;; A1
  '(la1 (a1-status) link-cntl (q2-out-act out-act))
  (list 'a1
        (sis 'a1-out 0 *data-width*)
        (si 'latch-n *data-width*)
        (list* 'q2-out-act (sis 'q2-data-out 0 *data-width*)))

  ;; B1
  '(lb1 (b1-status) link-cntl (q3-out-act out-act))
  (list 'b1
        (sis 'b1-out 0 *data-width*)
        (si 'latch-n *data-width*)
        (list* 'q3-out-act (sis 'q3-data-out 0 *data-width*)))

  ;; STATUS
  '(in-status (ready-in-) b-or (a0-status b0-status))
  '(out-status (ready-out) b-and (a1-status b1-status))

  ;; JOINTS
  ;; 2-link queue Q2
  (list 'q2
        (list* 'q2-in-act 'q2-out-act
               (sis 'q2-data-out 0 *data-width*))
        'queue2
        (list* 'a0-status 'a1-status
               (append (sis 'a0-out 0 *data-width*)
                       (sis 'go
                            *comp-v-or$prim-go-num*
                            *queue2$go-num*))))

  ;; 3-link queue Q3
  (list 'q3
        (list* 'q3-in-act 'q3-out-act
               (sis 'q3-data-out 0 *data-width*))
        'queue3
        (list* 'b0-status 'b1-status
               (append (sis 'b0-out 0 *data-width*)
                       (sis 'go
                            (+ *comp-v-or$prim-go-num*
                               *queue2$go-num*)
                            *queue3$go-num*))))

  ;; In
  (list 'in-cntl
        '(in-act)
        'joint-cntl
        (list 'full-in 'ready-in- (si 'go 0)))
  (list 'in-op0
        (sis 'a0-in 0 *data-width*)
        (si 'v-buf *data-width*)
        (sis 'a 0 *data-width*))
  (list 'in-op1
        (sis 'b0-in 0 *data-width*)
        (si 'v-buf *data-width*)
        (sis 'b 0 *data-width*))

  ;; Out
  (list 'out-cntl
        '(out-act)
        'joint-cntl
        (list 'ready-out 'full-out- (si 'go 1)))
  (list 'out-op
        (sis 's 0 *data-width*)
        (si 'v-or *data-width*)
        (append (sis 'a1-out 0 *data-width*)
                (sis 'b1-out 0 *data-width*))))

 :guard t)

(defun comp-v-or$netlist ()
  (declare (xargs :guard t))
  (cons (comp-v-or*)
        (union$ (queue2$netlist)
                (queue3$netlist)
                (v-or$netlist *data-width*)
                :test 'equal)))

(defthmd comp-v-or$netlist-okp
  (and (net-syntax-okp (comp-v-or$netlist))
       (net-arity-okp (comp-v-or$netlist))))

(defund comp-v-or& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (and (equal (assoc 'comp-v-or netlist)
              (comp-v-or*))
       (b* ((netlist (delete-to-eq 'comp-v-or netlist)))
         (and (joint-cntl& netlist)
              (latch-n& netlist *data-width*)
              (v-buf& netlist *data-width*)
              (v-or& netlist *data-width*)
              (queue2& netlist)
              (queue3& netlist)))))

(defthm check-comp-v-or$netlist
  (comp-v-or& (comp-v-or$netlist)))

(defconst *comp-v-or$la0* 0)
(defconst *comp-v-or$a0*  1)
(defconst *comp-v-or$lb0* 2)
(defconst *comp-v-or$b0*  3)
(defconst *comp-v-or$la1* 4)
(defconst *comp-v-or$a1*  5)
(defconst *comp-v-or$lb1* 6)
(defconst *comp-v-or$b1*  7)
(defconst *comp-v-or$q2*  8)
(defconst *comp-v-or$q3*  9)

(defund comp-v-or$valid-st (st)
  (b* ((la0 (get-field *comp-v-or$la0* st))
       (a0  (get-field *comp-v-or$a0* st))
       (lb0 (get-field *comp-v-or$lb0* st))
       (b0  (get-field *comp-v-or$b0* st))
       (la1 (get-field *comp-v-or$la1* st))
       (a1  (get-field *comp-v-or$a1* st))
       (lb1 (get-field *comp-v-or$lb1* st))
       (b1  (get-field *comp-v-or$b1* st))
       (q2  (get-field *comp-v-or$q2* st))
       (q3  (get-field *comp-v-or$q3* st)))
    (and (validp la0)
         (len-1-true-listp a0)
         (bvp (strip-cars a0))
         (equal (len a0) *data-width*)

         (validp lb0)
         (len-1-true-listp b0)
         (bvp (strip-cars b0))
         (equal (len b0) *data-width*)

         (validp la1)
         (len-1-true-listp a1)
         (bvp (strip-cars a1))
         (equal (len a1) *data-width*)

         (validp lb1)
         (len-1-true-listp b1)
         (bvp (strip-cars b1))
         (equal (len b1) *data-width*)

         (queue2$valid-st q2)
         (queue3$valid-st q3))))

(defun comp-v-or$map-to-links (st)
  (b* ((la0 (get-field *comp-v-or$la0* st))
       (a0  (get-field *comp-v-or$a0* st))
       (lb0 (get-field *comp-v-or$lb0* st))
       (b0  (get-field *comp-v-or$b0* st))
       (la1 (get-field *comp-v-or$la1* st))
       (a1  (get-field *comp-v-or$a1* st))
       (lb1 (get-field *comp-v-or$lb1* st))
       (b1  (get-field *comp-v-or$b1* st))
       (q2  (get-field *comp-v-or$q2* st))
       (q3  (get-field *comp-v-or$q3* st)))
    (append (map-to-links (list (list 'a0 la0 a0)
                                (list 'b0 lb0 b0)))
            (cons (cons 'Q2 (queue2$map-to-links q2))
                  (cons (cons 'Q3 (queue3$map-to-links q3))
                        (map-to-links (list (list 'a1 la1 a1)
                                            (list 'b1 lb1 b1))))))))

(defun comp-v-or$map-to-links-list (x)
  (if (atom x)
      nil
    (cons (comp-v-or$map-to-links (car x))
          (comp-v-or$map-to-links-list (cdr x)))))

(defund comp-v-or$sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *comp-v-or$ins-len*)
       ((mv inputs-lst state) (go-vals-gen num-signals n state nil))
       ;;(- (cw "~x0~%" inputs-lst))
       (empty '(nil))
       (invalid-data (make-list *data-width* :initial-element '(x)))
       (la0 empty)
       (a0 invalid-data)
       (lb0 empty)
       (b0 invalid-data)
       (la1 empty)
       (a1 invalid-data)
       (lb1 empty)
       (b1 invalid-data)
       (q2 (list empty invalid-data
                 empty invalid-data))
       (q3 (list empty invalid-data
                 empty invalid-data
                 empty invalid-data))
       (st (list la0 a0 lb0 b0 la1 a1 lb1 b1 q2 q3)))
    (mv (pretty-list
         (remove-dup-neighbors
          (comp-v-or$map-to-links-list
           (de-sim-list 'comp-v-or inputs-lst st (comp-v-or$netlist))))
         0)
        state)))

(defun comp-v-or$get-a (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (subseq-list inputs 2 (+ 2 *data-width*)))

(defthm len-comp-v-or$get-a
  (equal (len (comp-v-or$get-a inputs))
         *data-width*))

(in-theory (disable comp-v-or$get-a))

(defun comp-v-or$get-b (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (subseq-list inputs
               (+ 2 *data-width*)
               (+ 2 (* 2 *data-width*))))

(defthm len-comp-v-or$get-b
  (equal (len (comp-v-or$get-b inputs))
         *data-width*))

(in-theory (disable comp-v-or$get-b))

(defund comp-v-or$q2-inputs (inputs st)
  (b* ((go-signals (nthcdr *comp-v-or$data-ins-len* inputs))

       (q2-go-signals (take *queue2$go-num*
                            (nthcdr *comp-v-or$prim-go-num*
                                    go-signals)))

       (la0 (get-field *comp-v-or$la0* st))
       (a0  (get-field *comp-v-or$a0* st))
       (la1 (get-field *comp-v-or$la1* st)))
    
    (list* (f-buf (car la0)) (f-buf (car la1))
           (append (v-threefix (strip-cars a0))
                   q2-go-signals))))

(defund comp-v-or$q3-inputs (inputs st)
  (b* ((go-signals (nthcdr *comp-v-or$data-ins-len* inputs))

       (q3-go-signals (take *queue3$go-num*
                            (nthcdr (+ *comp-v-or$prim-go-num*
                                       *queue2$go-num*)
                                    go-signals)))

       (lb0 (get-field *comp-v-or$lb0* st))
       (b0  (get-field *comp-v-or$b0* st))
       (lb1 (get-field *comp-v-or$lb1* st)))
    
    (list* (f-buf (car lb0)) (f-buf (car lb1))
           (append (v-threefix (strip-cars b0))
                   q3-go-signals))))

(defund comp-v-or$in-act (inputs st)
  (b* ((full-in (nth 0 inputs))
       (go-signals (nthcdr *comp-v-or$data-ins-len* inputs))
       (go-in (nth 0 go-signals))
       (la0 (get-field *comp-v-or$la0* st))
       (lb0 (get-field *comp-v-or$lb0* st)))
    (joint-act full-in
               (f-or (car la0) (car lb0))
               go-in)))

(defund comp-v-or$out-act (inputs st)
  (b* ((full-out-  (nth 1 inputs))
       (go-signals (nthcdr *comp-v-or$data-ins-len* inputs))
       (go-out (nth 1 go-signals))

       (la1 (get-field *comp-v-or$la1* st))
       (lb1 (get-field *comp-v-or$lb1* st)))
    (joint-act (f-and (car la1) (car lb1))
               full-out-
               go-out)))

(defund comp-v-or$data-out (st)
  (v-or (strip-cars (get-field *comp-v-or$a1* st))
        (strip-cars (get-field *comp-v-or$b1* st))))

(defthm comp-v-or$data-out-props
   (implies (comp-v-or$valid-st st)
            (and (bvp (comp-v-or$data-out st))
                 (equal (len (comp-v-or$data-out st))
                        *data-width*)))
   :hints (("Goal" :in-theory (enable comp-v-or$valid-st
                                      comp-v-or$data-out))))

(defthmd comp-v-or$value
  (b* ((inputs (list* full-in full-out- (append a b go-signals))))
    (implies (and (comp-v-or& netlist)
                  (equal (len a) *data-width*)
                  (equal (len b) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-v-or$go-num*)
                  (comp-v-or$valid-st st))
             (equal (se 'comp-v-or inputs st netlist)
                    (list* (comp-v-or$in-act inputs st)
                           (comp-v-or$out-act inputs st)
                           (comp-v-or$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (se-rules
                            get-field
                            len-1-true-listp=>true-listp
                            open-nth
                            comp-v-or&
                            comp-v-or*$destructure
                            queue2$value
                            queue3$value
                            joint-cntl$value
                            latch-n$value
                            v-buf$value
                            v-or$value
                            comp-v-or$valid-st
                            comp-v-or$in-act
                            comp-v-or$out-act
                            comp-v-or$data-out)
                           ((comp-v-or*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(defun comp-v-or$state-fn (inputs st)
  (b* ((a (comp-v-or$get-a inputs))
       (b (comp-v-or$get-b inputs))
       
       (la0 (get-field *comp-v-or$la0* st))
       (a0  (get-field *comp-v-or$a0* st))
       (lb0 (get-field *comp-v-or$lb0* st))
       (b0  (get-field *comp-v-or$b0* st))
       (la1 (get-field *comp-v-or$la1* st))
       (a1  (get-field *comp-v-or$a1* st))
       (lb1 (get-field *comp-v-or$lb1* st))
       (b1  (get-field *comp-v-or$b1* st))
       (q2  (get-field *comp-v-or$q2* st))
       (q3  (get-field *comp-v-or$q3* st))

       (q2-inputs (comp-v-or$q2-inputs inputs st))
       (q2-in-act (queue2$in-act q2-inputs q2))
       (q2-out-act (queue2$out-act q2-inputs q2))
       (q2-data-out (queue2$data-out q2))
       
       (q3-inputs (comp-v-or$q3-inputs inputs st))
       (q3-in-act (queue3$in-act q3-inputs q3))
       (q3-out-act (queue3$out-act q3-inputs q3))
       (q3-data-out (queue3$data-out q3))

       (in-act (comp-v-or$in-act inputs st))
       (out-act (comp-v-or$out-act inputs st)))
    
    (list
     (list (f-sr in-act q2-in-act (car la0)))
     (pairlis$ (fv-if in-act a (strip-cars a0))
               nil)

     (list (f-sr in-act q3-in-act (car lb0)))
     (pairlis$ (fv-if in-act b (strip-cars b0))
               nil)

     (list (f-sr q2-out-act out-act (car la1)))
     (pairlis$ (fv-if q2-out-act q2-data-out (strip-cars a1))
               nil)

     (list (f-sr q3-out-act out-act (car lb1)))
     (pairlis$ (fv-if q3-out-act q3-data-out (strip-cars b1))
               nil)

     (queue2$state-fn q2-inputs q2)
     (queue3$state-fn q3-inputs q3))))

(defthm len-of-comp-v-or$state-fn
  (equal (len (comp-v-or$state-fn inputs st))
         *comp-v-or$st-len*))

(defthmd comp-v-or$state
  (b* ((inputs (list* full-in full-out- (append a b go-signals))))
    (implies (and (comp-v-or& netlist)
                  (true-listp a)
                  (equal (len a) *data-width*)
                  (true-listp b)
                  (equal (len b) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *comp-v-or$go-num*)
                  (comp-v-or$valid-st st))
             (equal (de 'comp-v-or inputs st netlist)
                    (comp-v-or$state-fn inputs st))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (de-rules
                            get-field
                            open-nth
                            len-1-true-listp=>true-listp
                            comp-v-or&
                            comp-v-or*$destructure
                            comp-v-or$valid-st
                            comp-v-or$get-a
                            comp-v-or$get-b
                            comp-v-or$in-act
                            comp-v-or$out-act
                            comp-v-or$q2-inputs
                            comp-v-or$q3-inputs
                            queue2$value queue2$state
                            queue3$value queue3$state
                            joint-cntl$value
                            latch-n$value latch-n$state
                            v-buf$value
                            v-or$value)
                           ((comp-v-or*)
                            (si)
                            (sis)
                            default-car
                            default-cdr
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(in-theory (disable comp-v-or$state-fn))

;; ======================================================================

(defund comp-v-or$input-format (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((full-in    (nth 0 inputs))
       (full-out-  (nth 1 inputs))
       (a    (comp-v-or$get-a inputs))
       (b    (comp-v-or$get-b inputs))
       (go-signals (nthcdr *comp-v-or$data-ins-len* inputs)))
    (and
     (booleanp full-in)
     (booleanp full-out-)
     (bvp a)
     (bvp b)
     (true-listp go-signals)
     (= (len go-signals) *comp-v-or$go-num*)
     (equal inputs
            (list* full-in full-out- (append a b go-signals))))))

(local
 (defthm comp-v-or$input-format=>q2$input-format
   (implies (and (comp-v-or$input-format inputs)
                 (comp-v-or$valid-st st))
            (queue2$input-format
             (comp-v-or$q2-inputs inputs st)))
   :hints (("Goal"
            :in-theory (e/d (comp-v-or$input-format
                             queue2$input-format
                             queue2$get-data-in
                             comp-v-or$valid-st
                             comp-v-or$q2-inputs)
                            (nth
                             nthcdr
                             len
                             take-of-too-many
                             take-of-len-is-itself))))))

(local
 (defthm comp-v-or$input-format=>q3$input-format
   (implies (and (comp-v-or$input-format inputs)
                 (comp-v-or$valid-st st))
            (queue3$input-format
             (comp-v-or$q3-inputs inputs st)))
   :hints (("Goal"
            :in-theory (e/d (comp-v-or$input-format
                             queue3$input-format
                             queue3$get-data-in
                             comp-v-or$valid-st
                             comp-v-or$q3-inputs)
                            (nth
                             nthcdr
                             len
                             take-of-too-many
                             take-of-len-is-itself))))))

(local
 (defthm booleanp-comp-v-or$q2-in-act
   (implies (and (or (equal (nth *comp-v-or$la0* st) '(t))
                     (equal (nth *comp-v-or$la0* st) '(nil)))
                 (queue2$valid-st (nth *comp-v-or$q2* st)))
            (booleanp (queue2$in-act (comp-v-or$q2-inputs inputs st)
                                     (nth *comp-v-or$q2* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               comp-v-or$q2-inputs
                               queue2$valid-st
                               queue2$in-act)))
   :rule-classes :type-prescription))

(local
 (defthm booleanp-comp-v-or$q3-in-act
   (implies (and (or (equal (nth *comp-v-or$lb0* st) '(t))
                     (equal (nth *comp-v-or$lb0* st) '(nil)))
                 (queue3$valid-st (nth *comp-v-or$q3* st)))
            (booleanp (queue3$in-act (comp-v-or$q3-inputs inputs st)
                                     (nth *comp-v-or$q3* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               comp-v-or$q3-inputs
                               queue3$valid-st
                               queue3$in-act)))
   :rule-classes :type-prescription))

(local
 (defthm comp-v-or$q2-in-act-nil
   (implies (equal (nth *comp-v-or$la0* st) '(nil))
            (not (queue2$in-act (comp-v-or$q2-inputs inputs st)
                                (nth *comp-v-or$q2* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               comp-v-or$q2-inputs
                               queue2$in-act)))))

(local
 (defthm comp-v-or$q3-in-act-nil
   (implies (equal (nth *comp-v-or$lb0* st) '(nil))
            (not (queue3$in-act (comp-v-or$q3-inputs inputs st)
                                (nth *comp-v-or$q3* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               comp-v-or$q3-inputs
                               queue3$in-act)))))

(local
 (defthm booleanp-comp-v-or$q2-out-act
   (implies (and (or (equal (nth *comp-v-or$la1* st) '(t))
                     (equal (nth *comp-v-or$la1* st) '(nil)))
                 (queue2$valid-st (nth *comp-v-or$q2* st)))
            (booleanp (queue2$out-act (comp-v-or$q2-inputs inputs st)
                                      (nth *comp-v-or$q2* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               comp-v-or$q2-inputs
                               queue2$valid-st
                               queue2$out-act)))
   :rule-classes :type-prescription))

(local
 (defthm booleanp-comp-v-or$q3-out-act
   (implies (and (or (equal (nth *comp-v-or$lb1* st) '(t))
                     (equal (nth *comp-v-or$lb1* st) '(nil)))
                 (queue3$valid-st (nth *comp-v-or$q3* st)))
            (booleanp (queue3$out-act (comp-v-or$q3-inputs inputs st)
                                      (nth *comp-v-or$q3* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               comp-v-or$q3-inputs
                               queue3$valid-st
                               queue3$out-act)))
   :rule-classes :type-prescription))

(local
 (defthm comp-v-or$q2-out-act-nil
   (implies (equal (nth *comp-v-or$la1* st) '(t))
            (not (queue2$out-act (comp-v-or$q2-inputs inputs st)
                                 (nth *comp-v-or$q2* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               comp-v-or$q2-inputs
                               queue2$out-act)))))

(local
 (defthm comp-v-or$q3-out-act-nil
   (implies (equal (nth *comp-v-or$lb1* st) '(t))
            (not (queue3$out-act (comp-v-or$q3-inputs inputs st)
                                 (nth *comp-v-or$q3* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               comp-v-or$q3-inputs
                               queue3$out-act)))))

(defthm comp-v-or$valid-st-preserved
  (implies (and (comp-v-or$input-format inputs)
                (comp-v-or$valid-st st))
           (comp-v-or$valid-st (comp-v-or$state-fn inputs st)))
  :hints (("Goal"
           :use ((:instance queue2$valid-st-preserved
                            (inputs (comp-v-or$q2-inputs inputs st))
                            (st (get-field *comp-v-or$q2* st)))
                 (:instance queue3$valid-st-preserved
                            (inputs (comp-v-or$q3-inputs inputs st))
                            (st (get-field *comp-v-or$q3* st))))
           :in-theory (e/d (get-field
                            comp-v-or$input-format
                            comp-v-or$valid-st
                            comp-v-or$state-fn
                            comp-v-or$in-act
                            comp-v-or$out-act
                            f-sr)
                           (queue2$valid-st-preserved
                            queue3$valid-st-preserved
                            if*
                            nth
                            nthcdr
                            take-of-too-many
                            take-of-len-is-itself
                            open-v-threefix)))))

(defthmd comp-v-or$state-alt
  (implies (and (comp-v-or& netlist)
                (comp-v-or$input-format inputs)
                (comp-v-or$valid-st st))
           (equal (de 'comp-v-or inputs st netlist)
                  (comp-v-or$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (enable comp-v-or$input-format)
           :use (:instance comp-v-or$state
                           (full-in    (nth 0 inputs))
                           (full-out-  (nth 1 inputs))
                           (a       (comp-v-or$get-a inputs))
                           (b       (comp-v-or$get-b inputs))
                           (go-signals (nthcdr *comp-v-or$data-ins-len*
                                               inputs))))))

(state-fn-n-gen comp-v-or)

(input-format-n-gen comp-v-or)

(defthmd de-sim-n$comp-v-or
  (implies (and (comp-v-or& netlist)
                (comp-v-or$input-format-n inputs-lst n)
                (comp-v-or$valid-st st))
           (equal (de-sim-n 'comp-v-or inputs-lst st netlist n)
                  (comp-v-or$state-fn-n inputs-lst st n)))
  :hints (("Goal" :in-theory (enable comp-v-or$state-alt))))

;; ======================================================================

(defun comp-v-or$op (in-seq)
  (if (atom in-seq)
      nil
    (cons (pairlis$ (v-or (strip-cars (caar in-seq))
                          (strip-cars (cdar in-seq)))
                    nil)
          (comp-v-or$op (cdr in-seq)))))

(defthm len-of-comp-v-or$op
  (equal (len (comp-v-or$op x))
         (len x)))

(defthm comp-v-or$op-of-append
  (equal (comp-v-or$op (append x y))
         (append (comp-v-or$op x) (comp-v-or$op y))))

(defund comp-v-or$extract-state (st)
  (b* ((la0 (get-field *comp-v-or$la0* st))
       (a0  (get-field *comp-v-or$a0* st))
       (lb0 (get-field *comp-v-or$lb0* st))
       (b0  (get-field *comp-v-or$b0* st))
       (la1 (get-field *comp-v-or$la1* st))
       (a1  (get-field *comp-v-or$a1* st))
       (lb1 (get-field *comp-v-or$lb1* st))
       (b1  (get-field *comp-v-or$b1* st))
       (q2  (get-field *comp-v-or$q2* st))
       (q3  (get-field *comp-v-or$q3* st))

       (a-seq (append (extract-state (list la0 a0))
                      (queue2$extract-state q2)
                      (extract-state (list la1 a1))))
       (b-seq (append (extract-state (list lb0 b0))
                      (queue3$extract-state q3)
                      (extract-state (list lb1 b1)))))
    (comp-v-or$op (pairlis$ a-seq b-seq))))

(defund comp-v-or$inv (st)
  (b* ((la0 (get-field *comp-v-or$la0* st))
       (a0  (get-field *comp-v-or$a0* st))
       (lb0 (get-field *comp-v-or$lb0* st))
       (b0  (get-field *comp-v-or$b0* st))
       (la1 (get-field *comp-v-or$la1* st))
       (a1  (get-field *comp-v-or$a1* st))
       (lb1 (get-field *comp-v-or$lb1* st))
       (b1  (get-field *comp-v-or$b1* st))
       (q2  (get-field *comp-v-or$q2* st))
       (q3  (get-field *comp-v-or$q3* st))

       (a-seq (append (extract-state (list la0 a0))
                      (queue2$extract-state q2)
                      (extract-state (list la1 a1))))
       (b-seq (append (extract-state (list lb0 b0))
                      (queue3$extract-state q3)
                      (extract-state (list lb1 b1)))))
    (equal (len a-seq) (len b-seq))))

(local
 (defthm nfix-of-natp
   (implies (natp x)
            (equal (nfix x) x))))

(local
 (defthm queue2$extract-state-not-empty
   (implies (and (queue2$out-act inputs st)
                 (queue2$input-format inputs)
                 (queue2$valid-st st))
            (< 0 (len (queue2$extract-state st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               queue2$valid-st
                               queue2$extract-state
                               queue2$out-act)))
   :rule-classes :linear))

(local
 (defthm queue3$extract-state-not-empty
   (implies (and (queue3$out-act inputs st)
                 (queue3$input-format inputs)
                 (queue3$valid-st st))
            (< 0 (len (queue3$extract-state st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               queue3$valid-st
                               queue3$extract-state
                               queue3$out-act)))
   :rule-classes :linear))

(defthm comp-v-or$inv-preserved
  (implies (and (comp-v-or$input-format inputs)
                (comp-v-or$valid-st st)
                (comp-v-or$inv st))
           (comp-v-or$inv (comp-v-or$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue2$step-spec
                            queue3$step-spec
                            comp-v-or$input-format
                            comp-v-or$valid-st
                            comp-v-or$inv
                            comp-v-or$state-fn
                            comp-v-or$in-act
                            comp-v-or$out-act
                            f-sr)
                           (if*
                            nfix
                            nth
                            nthcdr
                            take-of-too-many
                            take-of-len-is-itself
                            open-v-threefix)))))

(defun comp-v-or$in-seq (inputs-lst st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (comp-v-or$in-act inputs st) t)
          (append (comp-v-or$in-seq (cdr inputs-lst)
                                      (comp-v-or$state-fn inputs st)
                                      (1- n))
                  (list
                   (cons (pairlis$ (comp-v-or$get-a inputs)
                                   nil)
                         (pairlis$ (comp-v-or$get-b inputs)
                                   nil))))
        (comp-v-or$in-seq (cdr inputs-lst)
                            (comp-v-or$state-fn inputs st)
                            (1- n))))))

(defun comp-v-or$out-seq (inputs-lst st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst))
         (extracted-st (comp-v-or$extract-state st)))
      (if (equal (comp-v-or$out-act inputs st) t)
          (append (comp-v-or$out-seq (cdr inputs-lst)
                                       (comp-v-or$state-fn inputs st)
                                       (1- n))
                  (list (nth (1- (len extracted-st))
                             extracted-st)))
        (comp-v-or$out-seq (cdr inputs-lst)
                             (comp-v-or$state-fn inputs st)
                             (1- n))))))

(defun v-to-nat-flatten-2-lst (x)
  (declare (xargs :guard (alistp x)))
  (if (atom x)
      nil
    (cons (list (v-to-nat (acl2::flatten (caar x)))
                (v-to-nat (acl2::flatten (cdar x))))
          (v-to-nat-flatten-2-lst (cdr x)))))

(defund comp-v-or$in-out-seq-sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *comp-v-or$ins-len*)
       ((mv inputs-lst state)
        (go-vals-gen num-signals n state nil))
       (empty '(nil))
       (invalid-data (make-list *data-width* :initial-element '(x)))
       (la0 empty)
       (a0 invalid-data)
       (lb0 empty)
       (b0 invalid-data)
       (la1 empty)
       (a1 invalid-data)
       (lb1 empty)
       (b1 invalid-data)
       (q2 (list empty invalid-data
                 empty invalid-data))
       (q3 (list empty invalid-data
                 empty invalid-data
                 empty invalid-data))
       (st (list la0 a0 lb0 b0 la1 a1 lb1 b1 q2 q3)))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-flatten-2-lst
                   (comp-v-or$in-seq inputs-lst st n))))
      (list (cons 'out-seq
                  (v-to-nat-flatten-lst
                   (comp-v-or$out-seq inputs-lst st n)))))
     state)))

(defund comp-v-or$step-spec (inputs st)
  (b* ((a (comp-v-or$get-a inputs))
       (b (comp-v-or$get-b inputs))
       (s (pairlis$ (v-or a b) nil))
       (extracted-st (comp-v-or$extract-state st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (comp-v-or$out-act inputs st) t)
      (cond
       ((equal (comp-v-or$in-act inputs st) t)
        (cons s (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (comp-v-or$in-act inputs st) t)
          (cons s extracted-st))
         (t extracted-st))))))

(encapsulate
  ()

  (local
   (defthm comp-v-or$q2-get-data-in-rewrite
     (b* ((a0 (get-field *comp-v-or$a0* st)))
       (implies (and (bvp (strip-cars a0))
                     (equal (len a0) *data-width*))
                (equal (queue2$get-data-in
                        (comp-v-or$q2-inputs inputs st))
                       (strip-cars a0))))
     :hints (("Goal"
              :in-theory (enable queue2$get-data-in
                                 comp-v-or$q2-inputs)))))

  (local
   (defthm comp-v-or$q3-get-data-in-rewrite
     (b* ((b0 (get-field *comp-v-or$b0* st)))
       (implies (and (bvp (strip-cars b0))
                     (equal (len b0) *data-width*))
                (equal (queue3$get-data-in
                        (comp-v-or$q3-inputs inputs st))
                       (strip-cars b0))))
     :hints (("Goal"
              :in-theory (enable queue3$get-data-in
                                 comp-v-or$q3-inputs)))))

  (local
   (defthm car-queue3$extract-state-lemma
     (implies (and (<= (len (queue3$extract-state st))
                       1)
                   (queue3$valid-st st)
                   (queue3$out-act inputs st))
              (equal (car (queue3$extract-state st))
                     (pairlis$ (queue3$data-out st) nil)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue3$valid-st
                                 queue3$extract-state
                                 queue3$out-act
                                 queue3$data-out)))))

  (local
   (defthm cdr-queue3$extract-state-lemma
     (implies
      (and (< 1 (len (queue3$extract-state st)))
           (queue3$valid-st st)
           (equal n
                  (1- (len (cdr (queue3$extract-state st)))))
           (queue3$out-act inputs st))
      (equal (append (take n (cdr (queue3$extract-state st)))
                     (list (pairlis$ (queue3$data-out st) nil)))
             (cdr (queue3$extract-state st))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue3$valid-st
                                        queue3$extract-state
                                        queue3$out-act
                                        queue3$data-out)))))

  (local
   (defthm comp-v-or$step-spec-correct-aux
     (and (equal (cons e (append (queue2$extract-state st)
                                 x))
                 (append (cons e (queue2$extract-state st))
                         x))
          (equal (cons e (append (queue3$extract-state st)
                                 x))
                 (append (cons e (queue3$extract-state st))
                         x)))))

  (local
   (defthm queue2$extract-state-lemma
     (implies (and (queue2$valid-st st)
                   (equal n (1- (len (queue2$extract-state st))))
                   (queue2$out-act inputs st))
              (equal (append
                      (take n (queue2$extract-state st))
                      (list (pairlis$ (queue2$data-out st) nil)))
                     (queue2$extract-state st)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue2$valid-st
                                 queue2$extract-state
                                 queue2$out-act
                                 queue2$data-out)))))

  (local
   (defthm queue3$extract-state-lemma
     (implies (and (queue3$valid-st st)
                   (equal n (1- (len (queue3$extract-state st))))
                   (queue3$out-act inputs st))
              (equal (append
                      (take n (queue3$extract-state st))
                      (list (pairlis$ (queue3$data-out st) nil)))
                     (queue3$extract-state st)))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue3$valid-st
                                 queue3$extract-state
                                 queue3$out-act
                                 queue3$data-out)))))

  (defthm comp-v-or$step-spec-correct
    (b* ((next-st (comp-v-or$state-fn inputs st)))
      (implies (and (comp-v-or$input-format inputs)
                    (comp-v-or$valid-st st)
                    (comp-v-or$inv st))
               (equal (comp-v-or$extract-state next-st)
                      (comp-v-or$step-spec inputs st))))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              queue2$step-spec
                              queue3$step-spec
                              comp-v-or$step-spec
                              comp-v-or$input-format
                              comp-v-or$valid-st
                              comp-v-or$inv
                              comp-v-or$state-fn
                              comp-v-or$in-act
                              comp-v-or$out-act
                              comp-v-or$extract-state)
                             (nfix
                              nth
                              nthcdr
                              len-nthcdr
                              if*
                              take-of-len-is-itself
                              strip-cars
                              default-car
                              default-cdr
                              acl2::append-of-cons)))))
  )

(encapsulate
  ()
  
  (local
   (defthm consp-pairlis$
     (implies (consp x)
              (consp (pairlis$ x y)))
     :rule-classes :type-prescription))

  (local
   (defthm consp-comp-v-or$op
     (implies (consp x)
              (consp (comp-v-or$op x)))
     :rule-classes :type-prescription))

  (defthm consp-comp-v-or$extract-state
    (implies (and (comp-v-or$valid-st st)
                  (comp-v-or$out-act inputs st))
             (consp (comp-v-or$extract-state st)))
    :hints (("Goal"
             :in-theory (enable comp-v-or$valid-st
                                comp-v-or$extract-state
                                comp-v-or$out-act)))
    :rule-classes :type-prescription)
  )

;; (encapsulate
;;   ()
  
;;   (local
;;    (defthm take-of-comp-v-or$op-of-pairlis$
;;      (implies (and (equal (len x) (len y))
;;                    (<= n (len x)))
;;               (equal (take n (comp-v-or$op (pairlis$ x y)))
;;                      (comp-v-or$op (pairlis$ (take n x)
;;                                                (take n y)))))))

;;   (local
;;    (defthm take-of-comp-v-or$op-of-pairlis$-instance
;;      (implies
;;       (and (equal (len (append x1
;;                                (queue2$extract-state q2)
;;                                (list e1)))
;;                   (len (append x2
;;                                (queue3$extract-state q3)
;;                                (list e2))))
;;            (equal n (1- (len (append x1
;;                                      (queue2$extract-state q2)
;;                                      (list e1))))))
;;       (equal (take n (comp-v-or$op
;;                       (pairlis$
;;                        (append x1
;;                                (queue2$extract-state q2)
;;                                (list e1))
;;                        (append x2
;;                                (queue3$extract-state q3)
;;                                (list e2)))))
;;              (comp-v-or$op
;;               (pairlis$
;;                (append x1
;;                        (queue2$extract-state q2))
;;                (append x2
;;                        (queue3$extract-state q3))))))))

;;   (local
;;    (defthm append-of-comp-v-or$op-pairlis$-instance
;;      (implies (equal (len (append x (list e1)))
;;                      (len (append y (list e2))))
;;               (equal (append (comp-v-or$op (pairlis$ x y))
;;                              (list (pairlis$ (v-or (strip-cars e1)
;;                                                    (strip-cars e2))
;;                                              nil)))
;;                      (comp-v-or$op (pairlis$ (append x (list e1))
;;                                                (append y (list e2))))))))

;;   (defthm comp-v-or$extract-state-lemma
;;     (implies (and (comp-v-or$valid-st st)
;;                   (comp-v-or$inv st)
;;                   (equal n (1- (len (comp-v-or$extract-state st))))
;;                   (comp-v-or$out-act inputs st))
;;              (equal (append
;;                      (take n (comp-v-or$extract-state st))
;;                      (list (pairlis$ (comp-v-or$data-out st) nil)))
;;                     (comp-v-or$extract-state st)))
;;     :hints (("Goal"
;;              :in-theory (e/d (get-field
;;                               comp-v-or$valid-st
;;                               comp-v-or$inv
;;                               comp-v-or$extract-state
;;                               comp-v-or$out-act
;;                               comp-v-or$data-out)
;;                              (pairlis$
;;                               append
;;                               acl2::append-of-cons
;;                               acl2::append-when-not-consp
;;                               pairlis$-append
;;                               acl2::len-of-append)))))
;;   )

(encapsulate
  ()

  (local
   (defthm comp-v-or$dataflow-correct-aux
     (implies (equal (append x1 y1)
                     (append (comp-v-or$op in-seq) y2))
              (equal (append x1 y1 z)
                     (append (comp-v-or$op in-seq) y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (acl2::associativity-of-append))))))

  (defthmd comp-v-or$dataflow-correct
    (b* ((extracted-st (comp-v-or$extract-state st))
         (final-st (comp-v-or$state-fn-n inputs-lst st n))
         (final-extracted-st
          (comp-v-or$extract-state final-st)))
      (implies (and (comp-v-or$input-format-n inputs-lst n)
                    (comp-v-or$valid-st st)
                    (comp-v-or$inv st))
               (equal (append final-extracted-st
                              (comp-v-or$out-seq inputs-lst st n))
                      (append (comp-v-or$op
                               (comp-v-or$in-seq inputs-lst st n))
                              extracted-st))))
    :hints (("Goal"
             :in-theory (e/d (comp-v-or$step-spec)
                             ()))))
  )

