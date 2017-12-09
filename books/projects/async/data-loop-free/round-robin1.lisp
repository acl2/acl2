;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; December 2017

(in-package "ADE")

(include-book "alt-branch")
(include-book "alt-merge")
(include-book "queue2")
(include-book "queue3")

(local (in-theory (e/d (f-buf-delete-lemmas-1
                        f-buf-delete-lemmas-2)
                       (nth-of-bvp-is-booleanp
                        take-of-len-free))))

;; ======================================================================

(defconst *round-robin1$data-ins-len* (+ 2 *data-width*))
(defconst *round-robin1$go-num* (+ *alt-branch$go-num*
                                  *alt-merge$go-num*
                                  *queue2$go-num*
                                  *queue3$go-num*))
(defconst *round-robin1$ins-len* (+ *round-robin1$data-ins-len*
                                   *round-robin1$go-num*))
(defconst *round-robin1$st-len* 12)

;; A round-robin module:
;;
;;   -> A0 -Q2-> A1 -
;;  |                |
;; -BR               ME->
;;  |                |
;;   -> B0 -Q3-> B1 -

(module-generator
 round-robin1* ()
 'round-robin1
 (list* 'full-in 'full-out- (append (sis 'data-in 0 *data-width*)
                                    (sis 'go 0 *round-robin1$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 *data-width*))
 '(la0 a0 lb0 b0 la1 a1 lb1 b1 q2 q3 br me)
 (list
  ;; LINKS
  ;; A0
  '(la0 (a0-status) link-cntl (br-act0 q2-in-act))
  (list 'a0
        (sis 'a0-out 0 *data-width*)
        (si 'latch-n *data-width*)
        (list* 'br-act0 (sis 'data 0 *data-width*)))

  ;; B0
  '(lb0 (b0-status) link-cntl (br-act1 q3-in-act))
  (list 'b0
        (sis 'b0-out 0 *data-width*)
        (si 'latch-n *data-width*)
        (list* 'br-act1 (sis 'data 0 *data-width*)))

  ;; A1
  '(la1 (a1-status) link-cntl (q2-out-act me-act0))
  (list 'a1
        (sis 'a1-out 0 *data-width*)
        (si 'latch-n *data-width*)
        (list* 'q2-out-act (sis 'q2-data-out 0 *data-width*)))

  ;; B1
  '(lb1 (b1-status) link-cntl (q3-out-act me-act1))
  (list 'b1
        (sis 'b1-out 0 *data-width*)
        (si 'latch-n *data-width*)
        (list* 'q3-out-act (sis 'q3-data-out 0 *data-width*)))

  ;; JOINTS
  ;; 2-link queue Q2
  (list 'q2
        (list* 'q2-in-act 'q2-out-act
               (sis 'q2-data-out 0 *data-width*))
        'queue2
        (list* 'a0-status 'a1-status
               (append (sis 'a0-out 0 *data-width*)
                       (sis 'go 0 *queue2$go-num*))))

  ;; 3-link queue Q3
  (list 'q3
        (list* 'q3-in-act 'q3-out-act
               (sis 'q3-data-out 0 *data-width*))
        'queue3
        (list* 'b0-status 'b1-status
               (append (sis 'b0-out 0 *data-width*)
                       (sis 'go
                            *queue2$go-num*
                            *queue3$go-num*))))

  ;; Alt-Branch
  (list 'br
        (list* 'in-act 'br-act0 'br-act1
               (sis 'data 0 *data-width*))
        'alt-branch
        (list* 'full-in 'a0-status 'b0-status
               (append (sis 'data-in 0 *data-width*)
                       (sis 'go
                            (+ *queue2$go-num*
                               *queue3$go-num*)
                            *alt-branch$go-num*))))

  ;; Alt-Merge
  (list 'me
        (list* 'out-act 'me-act0 'me-act1
               (sis 'data-out 0 *data-width*))
        'alt-merge
        (list* 'a1-status 'b1-status 'full-out-
               (append (sis 'a1-out 0 *data-width*)
                       (sis 'b1-out 0 *data-width*)
                       (sis 'go
                            (+ *queue2$go-num*
                               *queue3$go-num*
                               *alt-branch$go-num*)
                            *alt-merge$go-num*)))))

 :guard t)

(defun round-robin1$netlist ()
  (declare (xargs :guard t))
  (cons (round-robin1*)
        (union$ (queue2$netlist)
                (queue3$netlist)
                (alt-branch$netlist)
                (alt-merge$netlist)
                :test 'equal)))

(defthmd round-robin1$netlist-okp
  (and (net-syntax-okp (round-robin1$netlist))
       (net-arity-okp (round-robin1$netlist))))

(defund round-robin1& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (and (equal (assoc 'round-robin1 netlist)
              (round-robin1*))
       (b* ((netlist (delete-to-eq 'round-robin1 netlist)))
         (and (queue2& netlist)
              (queue3& netlist)
              (alt-branch& netlist)
              (alt-merge& netlist)
              (latch-n& netlist *data-width*)))))

(defthm check-round-robin1$netlist
  (round-robin1& (round-robin1$netlist)))

(defconst *round-robin1$la0* 0)
(defconst *round-robin1$a0*  1)
(defconst *round-robin1$lb0* 2)
(defconst *round-robin1$b0*  3)
(defconst *round-robin1$la1* 4)
(defconst *round-robin1$a1*  5)
(defconst *round-robin1$lb1* 6)
(defconst *round-robin1$b1*  7)
(defconst *round-robin1$q2*  8)
(defconst *round-robin1$q3*  9)
(defconst *round-robin1$br* 10)
(defconst *round-robin1$me* 11)

(defund round-robin1$valid-st (st)
  (b* ((la0 (get-field *round-robin1$la0* st))
       (a0  (get-field *round-robin1$a0* st))
       (lb0 (get-field *round-robin1$lb0* st))
       (b0  (get-field *round-robin1$b0* st))
       (la1 (get-field *round-robin1$la1* st))
       (a1  (get-field *round-robin1$a1* st))
       (lb1 (get-field *round-robin1$lb1* st))
       (b1  (get-field *round-robin1$b1* st))
       (q2  (get-field *round-robin1$q2* st))
       (q3  (get-field *round-robin1$q3* st))
       (br  (get-field *round-robin1$br* st))
       (me  (get-field *round-robin1$me* st)))
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
         (queue3$valid-st q3)

         (alt-branch$valid-st br)
         (alt-merge$valid-st me))))

(defun round-robin1$map-to-links (st)
  (b* ((la0 (get-field *round-robin1$la0* st))
       (a0  (get-field *round-robin1$a0* st))
       (lb0 (get-field *round-robin1$lb0* st))
       (b0  (get-field *round-robin1$b0* st))
       (la1 (get-field *round-robin1$la1* st))
       (a1  (get-field *round-robin1$a1* st))
       (lb1 (get-field *round-robin1$lb1* st))
       (b1  (get-field *round-robin1$b1* st))
       (q2  (get-field *round-robin1$q2* st))
       (q3  (get-field *round-robin1$q3* st))
       (br  (get-field *round-robin1$br* st))
       (me  (get-field *round-robin1$me* st)))
    (append (list (cons 'alt-branch (alt-branch$map-to-links br)))
            (map-to-links (list (list 'a0 la0 a0)
                                (list 'b0 lb0 b0)))
            (cons (cons 'Q2 (queue2$map-to-links q2))
                  (cons (cons 'Q3 (queue3$map-to-links q3))
                        (map-to-links (list (list 'a1 la1 a1)
                                            (list 'b1 lb1 b1)))))
            (list (cons 'alt-merge (alt-merge$map-to-links me))))))

(defun round-robin1$map-to-links-list (x)
  (if (atom x)
      nil
    (cons (round-robin1$map-to-links (car x))
          (round-robin1$map-to-links-list (cdr x)))))

(defund round-robin1$sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *round-robin1$ins-len*)
       ((mv inputs-lst state) (go-vals-gen num-signals n state nil))
       ;;(- (cw "~x0~%" inputs-lst))
       (full '(t))
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
       (br (list full '(nil)
                 empty '(x)))
       (me (list full '(nil)
                 empty '(x)))
       (st (list la0 a0 lb0 b0 la1 a1 lb1 b1 q2 q3 br me)))
    (mv (pretty-list
         (remove-dup-neighbors
          (round-robin1$map-to-links-list
           (de-sim-list 'round-robin1 inputs-lst st (round-robin1$netlist))))
         0)
        state)))

(defun round-robin1$get-data-in (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (subseq-list inputs 2 (+ 2 *data-width*)))

(defthm len-round-robin1$get-data-in
  (equal (len (round-robin1$get-data-in inputs))
         *data-width*))

(in-theory (disable round-robin1$get-data-in))

(defund round-robin1$q2-inputs (inputs st)
  (b* ((go-signals (nthcdr *round-robin1$data-ins-len* inputs))

       (q2-go-signals (take *queue2$go-num* go-signals))

       (la0 (get-field *round-robin1$la0* st))
       (a0  (get-field *round-robin1$a0* st))
       (la1 (get-field *round-robin1$la1* st)))
    
    (list* (f-buf (car la0)) (f-buf (car la1))
           (append (v-threefix (strip-cars a0))
                   q2-go-signals))))

(defund round-robin1$q3-inputs (inputs st)
  (b* ((go-signals (nthcdr *round-robin1$data-ins-len* inputs))

       (q3-go-signals (take *queue3$go-num*
                            (nthcdr *queue2$go-num*
                                    go-signals)))

       (lb0 (get-field *round-robin1$lb0* st))
       (b0  (get-field *round-robin1$b0* st))
       (lb1 (get-field *round-robin1$lb1* st)))
    
    (list* (f-buf (car lb0)) (f-buf (car lb1))
           (append (v-threefix (strip-cars b0))
                   q3-go-signals))))

(defund round-robin1$br-inputs (inputs st)
  (b* ((full-in    (nth 0 inputs))
       (data-in    (round-robin1$get-data-in inputs))
       (go-signals (nthcdr *round-robin1$data-ins-len* inputs))

       (br-go-signals (take *alt-branch$go-num*
                            (nthcdr (+ *queue2$go-num*
                                       *queue3$go-num*)
                                    go-signals)))

       (la0 (get-field *round-robin1$la0* st))
       (lb0 (get-field *round-robin1$lb0* st)))

    (list* full-in (f-buf (car la0)) (f-buf (car lb0))
           (append data-in br-go-signals))))

(defund round-robin1$me-inputs (inputs st)
  (b* ((full-out-  (nth 1 inputs))
       (go-signals (nthcdr *round-robin1$data-ins-len* inputs))

       (me-go-signals (nthcdr (+ *queue2$go-num*
                                 *queue3$go-num*
                                 *alt-branch$go-num*)
                              go-signals))

       (la1 (get-field *round-robin1$la1* st))
       (a1  (get-field *round-robin1$a1* st))
       (lb1 (get-field *round-robin1$lb1* st))
       (b1  (get-field *round-robin1$b1* st)))

    (list* (f-buf (car la1)) (f-buf (car lb1)) full-out-
           (append (v-threefix (strip-cars a1))
                   (v-threefix (strip-cars b1))
                   me-go-signals))))

(defund round-robin1$in-act (inputs st)
  (b* ((br-inputs (round-robin1$br-inputs inputs st))
       (br (get-field *round-robin1$br* st)))
    (alt-branch$act br-inputs br)))

(defund round-robin1$out-act (inputs st)
  (b* ((me-inputs (round-robin1$me-inputs inputs st))
       (me (get-field *round-robin1$me* st)))
    (alt-merge$act me-inputs me)))

(defund round-robin1$data-out (st)
  (b* ((a1 (get-field *round-robin1$a1* st))
       (b1 (get-field *round-robin1$b1* st))
       (me (get-field *round-robin1$me* st))
       
       (mux (get-field *alt-merge$mux* me)))
    (fv-if (car mux)
           (strip-cars b1)
           (strip-cars a1))))

(defthm round-robin1$data-out-props
   (implies (round-robin1$valid-st st)
            (and (bvp (round-robin1$data-out st))
                 (equal (len (round-robin1$data-out st))
                        *data-width*)))
   :hints (("Goal" :in-theory (enable round-robin1$valid-st
                                      round-robin1$data-out
                                      alt-merge$valid-st))))

(defthmd round-robin1$value
  (b* ((inputs (list* full-in full-out- (append data-in go-signals))))
    (implies (and (round-robin1& netlist)
                  (true-listp data-in)
                  (equal (len data-in) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *round-robin1$go-num*)
                  (round-robin1$valid-st st))
             (equal (se 'round-robin1 inputs st netlist)
                    (list* (round-robin1$in-act inputs st)
                           (round-robin1$out-act inputs st)
                           (round-robin1$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (se-rules
                            get-field
                            open-nth
                            len-1-true-listp=>true-listp
                            round-robin1&
                            round-robin1*$destructure
                            round-robin1$get-data-in
                            queue2$value
                            queue3$value
                            alt-branch$value
                            alt-merge$value
                            latch-n$value
                            round-robin1$valid-st
                            round-robin1$in-act
                            round-robin1$out-act
                            round-robin1$data-out
                            round-robin1$br-inputs
                            round-robin1$me-inputs)
                           ((round-robin1*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(defun round-robin1$state-fn (inputs st)
  (b* ((data-in (round-robin1$get-data-in inputs))
       
       (la0 (get-field *round-robin1$la0* st))
       (a0  (get-field *round-robin1$a0* st))
       (lb0 (get-field *round-robin1$lb0* st))
       (b0  (get-field *round-robin1$b0* st))
       (la1 (get-field *round-robin1$la1* st))
       (a1  (get-field *round-robin1$a1* st))
       (lb1 (get-field *round-robin1$lb1* st))
       (b1  (get-field *round-robin1$b1* st))
       (q2  (get-field *round-robin1$q2* st))
       (q3  (get-field *round-robin1$q3* st))
       (br  (get-field *round-robin1$br* st))
       (me  (get-field *round-robin1$me* st))

       (q2-inputs (round-robin1$q2-inputs inputs st))
       (q2-in-act (queue2$in-act q2-inputs q2))
       (q2-out-act (queue2$out-act q2-inputs q2))
       (q2-data-out (queue2$data-out q2))
       
       (q3-inputs (round-robin1$q3-inputs inputs st))
       (q3-in-act (queue3$in-act q3-inputs q3))
       (q3-out-act (queue3$out-act q3-inputs q3))
       (q3-data-out (queue3$data-out q3))

       (br-inputs (round-robin1$br-inputs inputs st))
       (br-act0 (alt-branch$act0 br-inputs br))
       (br-act1 (alt-branch$act1 br-inputs br))
       
       (me-inputs (round-robin1$me-inputs inputs st))
       (me-act0 (alt-merge$act0 me-inputs me))
       (me-act1 (alt-merge$act1 me-inputs me)))
    
    (list
     (list (f-sr br-act0 q2-in-act (car la0)))
     (pairlis$ (fv-if br-act0 data-in (strip-cars a0))
               nil)

     (list (f-sr br-act1 q3-in-act (car lb0)))
     (pairlis$ (fv-if br-act1 data-in (strip-cars b0))
               nil)
     
     (list (f-sr q2-out-act me-act0 (car la1)))
     (pairlis$ (fv-if q2-out-act q2-data-out (strip-cars a1))
               nil)

     (list (f-sr q3-out-act me-act1 (car lb1)))
     (pairlis$ (fv-if q3-out-act q3-data-out (strip-cars b1))
               nil)

     (queue2$state-fn q2-inputs q2)
     (queue3$state-fn q3-inputs q3)

     (alt-branch$state-fn br-inputs br)
     (alt-merge$state-fn me-inputs me))))

(defthm len-of-round-robin1$state-fn
  (equal (len (round-robin1$state-fn inputs st))
         *round-robin1$st-len*))

(defthmd round-robin1$state
  (b* ((inputs (list* full-in full-out- (append data-in go-signals))))
    (implies (and (round-robin1& netlist)
                  (true-listp data-in)
                  (equal (len data-in) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *round-robin1$go-num*)
                  (round-robin1$valid-st st))
             (equal (de 'round-robin1 inputs st netlist)
                    (round-robin1$state-fn inputs st))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (de-rules
                            get-field
                            open-nth
                            len-1-true-listp=>true-listp
                            round-robin1&
                            round-robin1*$destructure
                            round-robin1$valid-st
                            round-robin1$get-data-in
                            round-robin1$q2-inputs
                            round-robin1$q3-inputs
                            round-robin1$br-inputs
                            round-robin1$me-inputs
                            queue2$value queue2$state
                            queue3$value queue3$state
                            alt-branch$value alt-branch$state
                            alt-merge$value alt-merge$state
                            latch-n$value latch-n$state)
                           ((round-robin1*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(in-theory (disable round-robin1$state-fn))

;; ======================================================================

(defund round-robin1$input-format (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((full-in    (nth 0 inputs))
       (full-out-  (nth 1 inputs))
       (data-in    (round-robin1$get-data-in inputs))
       (go-signals (nthcdr *round-robin1$data-ins-len* inputs)))
    (and
     (booleanp full-in)
     (booleanp full-out-)
     (bvp data-in)
     (true-listp go-signals)
     (= (len go-signals) *round-robin1$go-num*)
     (equal inputs
            (list* full-in full-out- (append data-in go-signals))))))

(defthmd len-of-round-robin1$inputs
  (implies (round-robin1$input-format inputs)
           (equal (len inputs) *round-robin1$ins-len*))
  :hints (("Goal" :in-theory (enable round-robin1$input-format))))

(local
 (defthm round-robin1$input-format=>q2$input-format
   (implies (and (round-robin1$input-format inputs)
                 (round-robin1$valid-st st))
            (queue2$input-format
             (round-robin1$q2-inputs inputs st)))
   :hints (("Goal"
            :in-theory (e/d (round-robin1$input-format
                             queue2$input-format
                             queue2$get-data-in
                             round-robin1$valid-st
                             round-robin1$q2-inputs)
                            (nth
                             nthcdr
                             len
                             take-of-too-many
                             take-of-len-is-itself))))))

(local
 (defthm round-robin1$input-format=>q3$input-format
   (implies (and (round-robin1$input-format inputs)
                 (round-robin1$valid-st st))
            (queue3$input-format
             (round-robin1$q3-inputs inputs st)))
   :hints (("Goal"
            :in-theory (e/d (round-robin1$input-format
                             queue3$input-format
                             queue3$get-data-in
                             round-robin1$valid-st
                             round-robin1$q3-inputs)
                            (nth
                             nthcdr
                             len
                             take-of-too-many
                             take-of-len-is-itself))))))

(local
 (defthm round-robin1$input-format=>br$input-format
   (implies (and (round-robin1$input-format inputs)
                 (round-robin1$valid-st st))
            (alt-branch$input-format
             (round-robin1$br-inputs inputs st)))
   :hints (("Goal"
            :in-theory (e/d (round-robin1$input-format
                             alt-branch$input-format
                             alt-branch$get-data-in
                             round-robin1$valid-st
                             round-robin1$br-inputs)
                            (nth
                             nthcdr
                             take-of-too-many
                             take-of-len-is-itself))))))

(local
 (defthm round-robin1$input-format=>me$input-format
   (implies (and (round-robin1$input-format inputs)
                 (round-robin1$valid-st st))
            (alt-merge$input-format
             (round-robin1$me-inputs inputs st)))
   :hints (("Goal"
            :in-theory (e/d (len-of-round-robin1$inputs
                             round-robin1$input-format
                             alt-merge$input-format
                             alt-merge$get-data-in0
                             alt-merge$get-data-in1
                             round-robin1$valid-st
                             round-robin1$me-inputs)
                            (nth
                             nthcdr
                             take-of-too-many
                             take-of-len-is-itself))))))

(local
 (defthm booleanp-round-robin1$q2-in-act
   (implies (and (or (equal (nth *round-robin1$la0* st) '(t))
                     (equal (nth *round-robin1$la0* st) '(nil)))
                 (queue2$valid-st (nth *round-robin1$q2* st)))
            (booleanp (queue2$in-act (round-robin1$q2-inputs inputs st)
                                     (nth *round-robin1$q2* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               round-robin1$q2-inputs
                               queue2$valid-st
                               queue2$in-act)))
   :rule-classes :type-prescription))

(local
 (defthm booleanp-round-robin1$q3-in-act
   (implies (and (or (equal (nth *round-robin1$lb0* st) '(t))
                     (equal (nth *round-robin1$lb0* st) '(nil)))
                 (queue3$valid-st (nth *round-robin1$q3* st)))
            (booleanp (queue3$in-act (round-robin1$q3-inputs inputs st)
                                     (nth *round-robin1$q3* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               round-robin1$q3-inputs
                               queue3$valid-st
                               queue3$in-act)))
   :rule-classes :type-prescription))

(local
 (defthm round-robin1$q2-in-act-nil
   (implies (equal (nth *round-robin1$la0* st) '(nil))
            (not (queue2$in-act (round-robin1$q2-inputs inputs st)
                                (nth *round-robin1$q2* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               round-robin1$q2-inputs
                               queue2$in-act)))))

(local
 (defthm round-robin1$q3-in-act-nil
   (implies (equal (nth *round-robin1$lb0* st) '(nil))
            (not (queue3$in-act (round-robin1$q3-inputs inputs st)
                                (nth *round-robin1$q3* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               round-robin1$q3-inputs
                               queue3$in-act)))))

(local
 (defthm booleanp-round-robin1$q2-out-act
   (implies (and (or (equal (nth *round-robin1$la1* st) '(t))
                     (equal (nth *round-robin1$la1* st) '(nil)))
                 (queue2$valid-st (nth *round-robin1$q2* st)))
            (booleanp (queue2$out-act (round-robin1$q2-inputs inputs st)
                                      (nth *round-robin1$q2* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               round-robin1$q2-inputs
                               queue2$valid-st
                               queue2$out-act)))
   :rule-classes :type-prescription))

(local
 (defthm booleanp-round-robin1$q3-out-act
   (implies (and (or (equal (nth *round-robin1$lb1* st) '(t))
                     (equal (nth *round-robin1$lb1* st) '(nil)))
                 (queue3$valid-st (nth *round-robin1$q3* st)))
            (booleanp (queue3$out-act (round-robin1$q3-inputs inputs st)
                                      (nth *round-robin1$q3* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               round-robin1$q3-inputs
                               queue3$valid-st
                               queue3$out-act)))
   :rule-classes :type-prescription))

(local
 (defthm round-robin1$q2-out-act-nil
   (implies (equal (nth *round-robin1$la1* st) '(t))
            (not (queue2$out-act (round-robin1$q2-inputs inputs st)
                                 (nth *round-robin1$q2* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               round-robin1$q2-inputs
                               queue2$out-act)))))

(local
 (defthm round-robin1$q3-out-act-nil
   (implies (equal (nth *round-robin1$lb1* st) '(t))
            (not (queue3$out-act (round-robin1$q3-inputs inputs st)
                                 (nth *round-robin1$q3* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               round-robin1$q3-inputs
                               queue3$out-act)))))

(local
 (defthm booleanp-round-robin1$br-act0
   (implies (and (booleanp (nth 0 inputs))
                 (or (equal (nth *round-robin1$la0* st) '(t))
                     (equal (nth *round-robin1$la0* st) '(nil)))
                 (or (equal (nth *round-robin1$lb0* st) '(t))
                     (equal (nth *round-robin1$lb0* st) '(nil)))
                 (alt-branch$valid-st (nth *round-robin1$br* st)))
            (booleanp (alt-branch$act0 (round-robin1$br-inputs inputs st)
                                   (nth *round-robin1$br* st))))
   :hints (("Goal" :in-theory (enable get-field
                                      round-robin1$br-inputs
                                      alt-branch$valid-st
                                      alt-branch$act0
                                      alt-branch$act)))
   :rule-classes :type-prescription))

(local
 (defthm booleanp-round-robin1$br-act1
   (implies (and (booleanp (nth 0 inputs))
                 (or (equal (nth *round-robin1$la0* st) '(t))
                     (equal (nth *round-robin1$la0* st) '(nil)))
                 (or (equal (nth *round-robin1$lb0* st) '(t))
                     (equal (nth *round-robin1$lb0* st) '(nil)))
                 (alt-branch$valid-st (nth *round-robin1$br* st)))
            (booleanp (alt-branch$act1 (round-robin1$br-inputs inputs st)
                                   (nth *round-robin1$br* st))))
   :hints (("Goal" :in-theory (enable get-field
                                      round-robin1$br-inputs
                                      alt-branch$valid-st
                                      alt-branch$act1
                                      alt-branch$act)))
   :rule-classes :type-prescription))

(local
 (defthm round-robin1$br-act0-nil
   (implies (and (equal (nth *round-robin1$la0* st) '(t))
                 (alt-branch$valid-st (nth *round-robin1$br* st)))
            (not (alt-branch$act0 (round-robin1$br-inputs inputs st)
                              (nth *round-robin1$br* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               f-if
                               round-robin1$br-inputs
                               alt-branch$valid-st
                               alt-branch$act0
                               alt-branch$act)))))

(local
 (defthm round-robin1$br-act1-nil
   (implies (and (equal (nth *round-robin1$lb0* st) '(t))
                 (alt-branch$valid-st (nth *round-robin1$br* st)))
            (not (alt-branch$act1 (round-robin1$br-inputs inputs st)
                              (nth *round-robin1$br* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               f-if
                               round-robin1$br-inputs
                               alt-branch$valid-st
                               alt-branch$act1
                               alt-branch$act)))))

(local
 (defthm booleanp-round-robin1$me-act0
   (implies (and (booleanp (nth 1 inputs))
                 (or (equal (nth *round-robin1$la1* st) '(t))
                     (equal (nth *round-robin1$la1* st) '(nil)))
                 (or (equal (nth *round-robin1$lb1* st) '(t))
                     (equal (nth *round-robin1$lb1* st) '(nil)))
                 (alt-merge$valid-st (nth *round-robin1$me* st)))
            (booleanp (alt-merge$act0 (round-robin1$me-inputs inputs st)
                                  (nth *round-robin1$me* st))))
   :hints (("Goal" :in-theory (enable get-field
                                      round-robin1$me-inputs
                                      alt-merge$valid-st
                                      alt-merge$act0
                                      alt-merge$act)))
   :rule-classes :type-prescription))

(local
 (defthm booleanp-round-robin1$me-act1
   (implies (and (booleanp (nth 1 inputs))
                 (or (equal (nth *round-robin1$la1* st) '(t))
                     (equal (nth *round-robin1$la1* st) '(nil)))
                 (or (equal (nth *round-robin1$lb1* st) '(t))
                     (equal (nth *round-robin1$lb1* st) '(nil)))
                 (alt-merge$valid-st (nth *round-robin1$me* st)))
            (booleanp (alt-merge$act1 (round-robin1$me-inputs inputs st)
                                  (nth *round-robin1$me* st))))
   :hints (("Goal" :in-theory (enable get-field
                                      round-robin1$me-inputs
                                      alt-merge$valid-st
                                      alt-merge$act1
                                      alt-merge$act)))
   :rule-classes :type-prescription))

(local
 (defthm round-robin1$me-act0-nil
   (implies (and (equal (nth *round-robin1$la1* st) '(nil))
                 (alt-merge$valid-st (nth *round-robin1$me* st)))
            (not (alt-merge$act0 (round-robin1$me-inputs inputs st)
                             (nth *round-robin1$me* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               f-if
                               round-robin1$me-inputs
                               alt-merge$valid-st
                               alt-merge$act0
                               alt-merge$act)))))

(local
 (defthm round-robin1$me-act1-nil
   (implies (and (equal (nth *round-robin1$lb1* st) '(nil))
                 (alt-merge$valid-st (nth *round-robin1$me* st)))
            (not (alt-merge$act1 (round-robin1$me-inputs inputs st)
                             (nth *round-robin1$me* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               f-if
                               round-robin1$me-inputs
                               alt-merge$valid-st
                               alt-merge$act1
                               alt-merge$act)))))

(defthm round-robin1$valid-st-preserved
  (implies (and (round-robin1$input-format inputs)
                (round-robin1$valid-st st))
           (round-robin1$valid-st (round-robin1$state-fn inputs st)))
  :hints (("Goal"
           :use ((:instance queue2$valid-st-preserved
                            (inputs (round-robin1$q2-inputs inputs st))
                            (st (get-field *round-robin1$q2* st)))
                 (:instance queue3$valid-st-preserved
                            (inputs (round-robin1$q3-inputs inputs st))
                            (st (get-field *round-robin1$q3* st)))
                 (:instance alt-branch$valid-st-preserved
                            (inputs (round-robin1$br-inputs inputs st))
                            (st (get-field *round-robin1$br* st)))
                 (:instance alt-merge$valid-st-preserved
                            (inputs (round-robin1$me-inputs inputs st))
                            (st (get-field *round-robin1$me* st))))
           :in-theory (e/d (get-field
                            round-robin1$input-format
                            round-robin1$valid-st
                            round-robin1$state-fn
                            round-robin1$in-act
                            round-robin1$out-act
                            f-sr)
                           (queue2$valid-st-preserved
                            queue3$valid-st-preserved
                            alt-branch$valid-st-preserved
                            alt-merge$valid-st-preserved
                            if*
                            nth
                            nthcdr
                            acl2::true-listp-append)))))

(defthmd round-robin1$state-alt
  (implies (and (round-robin1& netlist)
                (round-robin1$input-format inputs)
                (round-robin1$valid-st st))
           (equal (de 'round-robin1 inputs st netlist)
                  (round-robin1$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (enable round-robin1$input-format)
           :use (:instance round-robin1$state
                           (full-in    (nth 0 inputs))
                           (full-out-  (nth 1 inputs))
                           (data-in    (round-robin1$get-data-in inputs))
                           (go-signals (nthcdr *round-robin1$data-ins-len*
                                               inputs))))))

(state-fn-n-gen round-robin1)

(input-format-n-gen round-robin1)

(defthmd de-sim-n$round-robin1
  (implies (and (round-robin1& netlist)
                (round-robin1$input-format-n inputs-lst n)
                (round-robin1$valid-st st))
           (equal (de-sim-n 'round-robin1 inputs-lst st netlist n)
                  (round-robin1$state-fn-n inputs-lst st n)))
  :hints (("Goal" :in-theory (enable round-robin1$state-alt))))

;; ======================================================================

(defun interleave (l1 l2)
  (declare (xargs :guard t))
  (cond ((atom l1) l2)
        ((atom l2) l1)
        (t (append (list (car l1) (car l2))
                   (interleave (cdr l1) (cdr l2))))))

(defthm consp-interleave
  (implies (or (consp l1) (consp l2)
               (< 0 (len l1)) (< 0 (len l2)))
           (consp (interleave l1 l2)))
  :rule-classes :type-prescription)

(defthm true-listp-interleave
  (implies (and (true-listp l1)
                (true-listp l2))
           (true-listp (interleave l1 l2)))
  :rule-classes :type-prescription)

(defthm len-interleave
  (equal (len (interleave l1 l2))
         (+ (len l1) (len l2))))

(defthm len-of-cdr-interleave
  (implies (or (< 0 (len l1)) (< 0 (len l2)))
           (equal (len (cdr (interleave l1 l2)))
                  (+ -1 (len l1) (len l2)))))

(defthm interleave-append-1
  (implies (and (or (equal (len x1) (len x2))
                    (equal (len x1) (1+ (len x2))))
                (consp y))
           (equal (interleave (append x1 y) x2)
                  (append (interleave x1 x2) y))))

(defthm interleave-append-2
  (implies (and (<= (len x1) (1+ (len x2)))
                (consp y))
           (equal (interleave x1 (append x2 y))
                  (append (interleave x1 x2) y))))

(defthm interleave-append-append
  (implies (equal (len x1) (len x2))
           (equal (interleave (append x1 y1) (append x2 y2))
                  (append (interleave x1 x2) (interleave y1 y2)))))

(defund round-robin1$extract-state (st)
  (b* ((la0 (get-field *round-robin1$la0* st))
       (a0  (get-field *round-robin1$a0* st))
       (lb0 (get-field *round-robin1$lb0* st))
       (b0  (get-field *round-robin1$b0* st))
       (la1 (get-field *round-robin1$la1* st))
       (a1  (get-field *round-robin1$a1* st))
       (lb1 (get-field *round-robin1$lb1* st))
       (b1  (get-field *round-robin1$b1* st))
       (q2  (get-field *round-robin1$q2* st))
       (q3  (get-field *round-robin1$q3* st))
       (me  (get-field *round-robin1$me* st))

       (a-seq (append (extract-state (list la0 a0))
                      (queue2$extract-state q2)
                      (extract-state (list la1 a1))))
       (b-seq (append (extract-state (list lb0 b0))
                      (queue3$extract-state q3)
                      (extract-state (list lb1 b1))))

       (lmux    (get-field *alt-merge$lmux* me))
       (mux     (get-field *alt-merge$mux* me))
       (mux-buf (get-field *alt-merge$mux-buf* me))
       (me-select (if (fullp lmux) (car mux) (car mux-buf))))
    
    (cond ((< (len a-seq) (len b-seq))
           (interleave b-seq a-seq))
          ((< (len b-seq) (len a-seq))
           (interleave a-seq b-seq))
          (me-select (interleave a-seq b-seq))
          (t (interleave b-seq a-seq)))))

(defund round-robin1$inv (st)
  (b* ((la0 (get-field *round-robin1$la0* st))
       (a0  (get-field *round-robin1$a0* st))
       (lb0 (get-field *round-robin1$lb0* st))
       (b0  (get-field *round-robin1$b0* st))
       (la1 (get-field *round-robin1$la1* st))
       (a1  (get-field *round-robin1$a1* st))
       (lb1 (get-field *round-robin1$lb1* st))
       (b1  (get-field *round-robin1$b1* st))
       (q2  (get-field *round-robin1$q2* st))
       (q3  (get-field *round-robin1$q3* st))
       (br  (get-field *round-robin1$br* st))
       (me  (get-field *round-robin1$me* st))

       (a-seq (append (extract-state (list la0 a0))
                      (queue2$extract-state q2)
                      (extract-state (list la1 a1))))
       (b-seq (append (extract-state (list lb0 b0))
                      (queue3$extract-state q3)
                      (extract-state (list lb1 b1))))

       (ldemux    (get-field *alt-branch$ldemux* br))
       (demux     (get-field *alt-branch$demux* br))
       (demux-buf (get-field *alt-branch$demux-buf* br))
       (br-select (if (fullp ldemux) (car demux) (car demux-buf)))

       (lmux      (get-field *alt-merge$lmux* me))
       (mux       (get-field *alt-merge$mux* me))
       (mux-buf   (get-field *alt-merge$mux-buf* me))
       (me-select (if (fullp lmux) (car mux) (car mux-buf))))

    (and (alt-branch$inv br)
         (alt-merge$inv me)
         (or (and (equal (len a-seq) (len b-seq))
                  (equal br-select me-select))
             (and (equal (len a-seq) (1+ (len b-seq)))
                  br-select
                  (not me-select))
             (and (equal (1+ (len a-seq)) (len b-seq))
                  (not br-select)
                  me-select)))))

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

(defthm round-robin1$inv-preserved
  (implies (and (round-robin1$input-format inputs)
                (round-robin1$valid-st st)
                (round-robin1$inv st))
           (round-robin1$inv (round-robin1$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue2$step-spec
                            queue3$step-spec
                            round-robin1$input-format
                            round-robin1$valid-st
                            round-robin1$inv
                            round-robin1$state-fn
                            round-robin1$in-act
                            round-robin1$out-act
                            round-robin1$br-inputs
                            round-robin1$me-inputs
                            alt-branch$valid-st
                            alt-branch$inv
                            alt-branch$state-fn
                            alt-branch$act
                            alt-branch$act0
                            alt-branch$act1
                            alt-merge$valid-st
                            alt-merge$inv
                            alt-merge$state-fn
                            alt-merge$act
                            alt-merge$act0
                            alt-merge$act1
                            f-sr)
                           (if*
                            nfix
                            nth
                            nthcdr
                            append
                            pairlis$
                            strip-cars
                            default-car
                            default-cdr
                            default-+-1
                            default-+-2
                            take-of-too-many
                            take-of-len-is-itself
                            open-v-threefix)))))

(defun round-robin1$in-seq (inputs-lst st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (round-robin1$in-act inputs st) t)
          (append (round-robin1$in-seq (cdr inputs-lst)
                                 (round-robin1$state-fn inputs st)
                                 (1- n))
                  (list (pairlis$ (round-robin1$get-data-in inputs)
                                  nil)))
        (round-robin1$in-seq (cdr inputs-lst)
                       (round-robin1$state-fn inputs st)
                       (1- n))))))

(defun round-robin1$out-seq (inputs-lst st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst))
         (extracted-st (round-robin1$extract-state st)))
      (if (equal (round-robin1$out-act inputs st) t)
          (append (round-robin1$out-seq (cdr inputs-lst)
                                  (round-robin1$state-fn inputs st)
                                  (1- n))
                  (list (nth (1- (len extracted-st))
                             extracted-st)))
        (round-robin1$out-seq (cdr inputs-lst)
                        (round-robin1$state-fn inputs st)
                        (1- n))))))

(defund round-robin1$in-out-seq-sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *round-robin1$ins-len*)
       ((mv inputs-lst state)
        (go-vals-gen num-signals n state nil))
       (full '(t))
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
       (br (list full '(nil)
                 empty '(x)))
       (me (list full '(nil)
                 empty '(x)))
       (st (list la0 a0 lb0 b0 la1 a1 lb1 b1 q2 q3 br me)))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-flatten-lst
                   (round-robin1$in-seq inputs-lst st n))))
      (list (cons 'out-seq
                  (v-to-nat-flatten-lst
                   (round-robin1$out-seq inputs-lst st n)))))
     state)))

(defund round-robin1$step-spec (inputs st)
  (b* ((data-in (round-robin1$get-data-in inputs))
       (extracted-st (round-robin1$extract-state st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (round-robin1$out-act inputs st) t)
      (cond
       ((equal (round-robin1$in-act inputs st) t)
        (cons (pairlis$ data-in nil)
              (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (round-robin1$in-act inputs st) t)
          (cons (pairlis$ data-in nil)
                extracted-st))
         (t extracted-st))))))

(local
 (defthm len-0-is-atom
   (equal (equal (len x) 0)
          (atom x))))

(local
 (defthmd cons-append-instances
   (and (equal (cons e (append (queue2$extract-state st)
                               x))
               (append (cons e (queue2$extract-state st))
                       x))
        (equal (cons e (append (queue3$extract-state st)
                               x))
               (append (cons e (queue3$extract-state st))
                       x)))))

(encapsulate
  ()

  (local
   (defthm len-of-cons
     (implies (consp x)
              (< 0 (len x)))
     :rule-classes :linear))

  (local
   (defthm round-robin1$q2-get-data-in-rewrite
     (b* ((a0 (get-field *round-robin1$a0* st)))
       (implies (and (bvp (strip-cars a0))
                     (equal (len a0) *data-width*))
                (equal (queue2$get-data-in
                        (round-robin1$q2-inputs inputs st))
                       (strip-cars a0))))
     :hints (("Goal"
              :in-theory (enable queue2$get-data-in
                                 round-robin1$q2-inputs)))))

  (local
   (defthm round-robin1$q3-get-data-in-rewrite
     (b* ((b0 (get-field *round-robin1$b0* st)))
       (implies (and (bvp (strip-cars b0))
                     (equal (len b0) *data-width*))
                (equal (queue3$get-data-in
                        (round-robin1$q3-inputs inputs st))
                       (strip-cars b0))))
     :hints (("Goal"
              :in-theory (enable queue3$get-data-in
                                 round-robin1$q3-inputs)))))

  (local
   (defthm queue2$extract-state-singleton
     (implies (and (equal (len (queue2$extract-state st))
                          1)
                   (queue2$valid-st st)
                   (queue2$out-act inputs st))
              (equal (queue2$extract-state st)
                     (list (pairlis$ (queue2$data-out st) nil))))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue2$valid-st
                                 queue2$extract-state
                                 queue2$out-act
                                 queue2$data-out)))))

  (local
   (defthm cdr-queue2$extract-state-singleton
     (implies (and (equal (len (queue2$extract-state st))
                          2)
                   (queue2$valid-st st)
                   (queue2$out-act inputs st))
              (equal (cdr (queue2$extract-state st))
                     (list (pairlis$ (queue2$data-out st) nil))))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue2$valid-st
                                 queue2$extract-state
                                 queue2$out-act
                                 queue2$data-out)))))

  (local
   (defthm queue3$extract-state-singleton
     (implies (and (equal (len (queue3$extract-state st))
                          1)
                   (queue3$valid-st st)
                   (queue3$out-act inputs st))
              (equal (queue3$extract-state st)
                     (list (pairlis$ (queue3$data-out st) nil))))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue3$valid-st
                                 queue3$extract-state
                                 queue3$out-act
                                 queue3$data-out)))))

  (local
   (defthm cdr-queue3$extract-state-singleton
     (implies (and (equal (len (queue3$extract-state st))
                          2)
                   (queue3$valid-st st)
                   (queue3$out-act inputs st))
              (equal (cdr (queue3$extract-state st))
                     (list (pairlis$ (queue3$data-out st) nil))))
     :hints (("Goal"
              :in-theory (enable get-field
                                 queue3$valid-st
                                 queue3$extract-state
                                 queue3$out-act
                                 queue3$data-out)))))

  (local
   (defthm round-robin1$step-spec-correct-aux-1
     (equal (cons e (append (interleave x y)
                            z))
            (append (interleave (cons e y)
                                 x)
                    z))))

  (local
   (defthm round-robin1$step-spec-correct-aux-2
     (equal (cons e (append (cdr (interleave x y))
                            z))
            (append (cons e (cdr (interleave x y)))
                    z))))

  (local
   (defthm round-robin1$step-spec-correct-aux-3
     (implies (consp x)
              (equal (cons (car x)
                           (interleave (queue2$extract-state st)
                                        (cdr x)))
                     (interleave x (queue2$extract-state st))))))

  (local
   (defthm round-robin1$step-spec-correct-aux-4
     (implies (consp x)
              (equal (cons (car x)
                           (interleave (queue3$extract-state st)
                                        (cdr x)))
                     (interleave x (queue3$extract-state st))))))

  (local
   (defthm round-robin1$step-spec-correct-aux-5
     (implies (consp x)
              (equal (cons (car x)
                           (interleave (append y z)
                                        (cdr x)))
                     (interleave x (append y z))))
     :hints (("Goal" :in-theory (disable interleave-append-2)))))

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

  (defthm round-robin1$step-spec-correct
    (b* ((next-st (round-robin1$state-fn inputs st)))
      (implies (and (round-robin1$input-format inputs)
                    (round-robin1$valid-st st)
                    (round-robin1$inv st))
               (equal (round-robin1$extract-state next-st)
                      (round-robin1$step-spec inputs st))))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              f-sr
                              cons-append-instances
                              queue2$step-spec
                              queue3$step-spec
                              round-robin1$step-spec
                              round-robin1$input-format
                              round-robin1$valid-st
                              round-robin1$inv
                              round-robin1$state-fn
                              round-robin1$in-act
                              round-robin1$out-act
                              round-robin1$extract-state
                              round-robin1$br-inputs
                              round-robin1$me-inputs
                              alt-branch$valid-st
                              alt-branch$inv
                              alt-branch$act
                              alt-branch$act0
                              alt-branch$act1
                              alt-merge$valid-st
                              alt-merge$inv
                              alt-merge$state-fn
                              alt-merge$act
                              alt-merge$act0
                              alt-merge$act1)
                             (nfix
                              nth
                              nthcdr
                              len-nthcdr
                              if*
                              pairlis$
                              strip-cars
                              take-of-len-is-itself
                              default-car
                              default-cdr
                              default-+-1
                              default-+-2
                              acl2::append-of-cons)))))
  )

(defthm consp-round-robin1$extract-state
  (implies (and (round-robin1$valid-st st)
                (round-robin1$out-act inputs st))
           (consp (round-robin1$extract-state st)))
  :hints (("Goal"
           :in-theory (enable round-robin1$valid-st
                              round-robin1$extract-state
                              round-robin1$out-act
                              round-robin1$me-inputs
                              alt-merge$valid-st
                              alt-merge$act
                              alt-merge$act0
                              alt-merge$act1)))
  :rule-classes :type-prescription)

;; (defthm round-robin1$extract-state-lemma
;;   (implies (and (round-robin1$valid-st st)
;;                 (round-robin1$inv st)
;;                 (equal n (1- (len (round-robin1$extract-state st))))
;;                 (round-robin1$out-act inputs st))
;;            (equal (append
;;                    (take n (round-robin1$extract-state st))
;;                    (list (pairlis$ (round-robin1$data-out st) nil)))
;;                   (round-robin1$extract-state st)))
;;   :hints (("Goal"
;;            :in-theory (e/d (get-field
;;                             cons-append-instances
;;                             left-associativity-of-append
;;                             round-robin1$valid-st
;;                             round-robin1$inv
;;                             round-robin1$extract-state
;;                             round-robin1$out-act
;;                             round-robin1$data-out
;;                             round-robin1$me-inputs
;;                             alt-merge$valid-st
;;                             alt-merge$act
;;                             alt-merge$act0
;;                             alt-merge$act1)
;;                            (nfix
;;                             nth
;;                             nthcdr
;;                             len-nthcdr
;;                             if*
;;                             append
;;                             pairlis$
;;                             strip-cars
;;                             not
;;                             take-of-len-is-itself
;;                             default-car
;;                             default-cdr
;;                             default-+-1
;;                             default-+-2
;;                             acl2::append-of-cons
;;                             acl2::associativity-of-append)))))

(encapsulate
  ()

  (local
   (defthm round-robin1$dataflow-correct-aux
     (implies (equal (append x1 y1)
                     (append (round-robin1$in-seq inputs-lst st n) y2))
              (equal (append x1 y1 z)
                     (append (round-robin1$in-seq inputs-lst st n) y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (acl2::associativity-of-append))))))

  (defthmd round-robin1$dataflow-correct
    (b* ((extracted-st (round-robin1$extract-state st))
         (final-st (round-robin1$state-fn-n inputs-lst st n))
         (final-extracted-st (round-robin1$extract-state final-st)))
      (implies (and (round-robin1$input-format-n inputs-lst n)
                    (round-robin1$valid-st st)
                    (round-robin1$inv st))
               (equal (append final-extracted-st
                              (round-robin1$out-seq inputs-lst st n))
                      (append (round-robin1$in-seq inputs-lst st n)
                              extracted-st))))
    :hints (("Goal"
             :in-theory (e/d (round-robin1$step-spec)
                             ()))))
  )

