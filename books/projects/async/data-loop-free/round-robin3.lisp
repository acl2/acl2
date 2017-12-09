;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; December 2017

(in-package "ADE")

(include-book "alt-branch")
(include-book "alt-merge")
(include-book "queue8-as-link")
(include-book "queue10-as-link")

(local (in-theory (e/d (f-buf-delete-lemmas-1
                        f-buf-delete-lemmas-2)
                       (nth-of-bvp-is-booleanp
                        take-of-len-free))))

;; ======================================================================

(defconst *round-robin3$data-ins-len* (+ 2 *data-width*))
(defconst *round-robin3$go-num* (+ *alt-branch$go-num*
                                  *alt-merge$go-num*
                                  *queue8$go-num*
                                  *queue10$go-num*))
(defconst *round-robin3$ins-len* (+ *round-robin3$data-ins-len*
                                   *round-robin3$go-num*))
(defconst *round-robin3$st-len* 4)

;; A round-robin module:
;;
;;   -> Q8 --
;;  |        |
;; -BR       ME->
;;  |        |
;;   -> Q10 -

(module-generator
 round-robin3* ()
 'round-robin3
 (list* 'full-in 'full-out- (append (sis 'data-in 0 *data-width*)
                                    (sis 'go 0 *round-robin3$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 *data-width*))
 '(q8 q10 br me)
 (list
  ;; LINKS
  ;; 8-link queue Q8
  (list 'q8
        (list* 'q8-ready-in- 'q8-ready-out
               (sis 'q8-data-out 0 *data-width*))
        'queue8
        (list* 'br-act0 'me-act0
               (append (sis 'data 0 *data-width*)
                       (sis 'go 0 *queue8$go-num*))))

  ;; 10-link queue Q10
  (list 'q10
        (list* 'q10-ready-in- 'q10-ready-out
               (sis 'q10-data-out 0 *data-width*))
        'queue10
        (list* 'br-act1 'me-act1
               (append (sis 'data 0 *data-width*)
                       (sis 'go
                            *queue8$go-num*
                            *queue10$go-num*))))

  ;; JOINTS
  ;; Alt-Branch
  (list 'br
        (list* 'in-act 'br-act0 'br-act1
               (sis 'data 0 *data-width*))
        'alt-branch
        (list* 'full-in 'q8-ready-in- 'q10-ready-in-
               (append (sis 'data-in 0 *data-width*)
                       (sis 'go
                            (+ *queue8$go-num*
                               *queue10$go-num*)
                            *alt-branch$go-num*))))

  ;; Alt-Merge
  (list 'me
        (list* 'out-act 'me-act0 'me-act1
               (sis 'data-out 0 *data-width*))
        'alt-merge
        (list* 'q8-ready-out 'q10-ready-out 'full-out-
               (append (sis 'q8-data-out 0 *data-width*)
                       (sis 'q10-data-out 0 *data-width*)
                       (sis 'go
                            (+ *queue8$go-num*
                               *queue10$go-num*
                               *alt-branch$go-num*)
                            *alt-merge$go-num*)))))

 :guard t)

(defun round-robin3$netlist ()
  (declare (xargs :guard t))
  (cons (round-robin3*)
        (union$ (queue8$netlist)
                (queue10$netlist)
                (alt-branch$netlist)
                (alt-merge$netlist)
                :test 'equal)))

(defthmd round-robin3$netlist-okp
  (and (net-syntax-okp (round-robin3$netlist))
       (net-arity-okp (round-robin3$netlist))))

(defund round-robin3& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (and (equal (assoc 'round-robin3 netlist)
              (round-robin3*))
       (b* ((netlist (delete-to-eq 'round-robin3 netlist)))
         (and (queue8& netlist)
              (queue10& netlist)
              (alt-branch& netlist)
              (alt-merge& netlist)))))

(defthm check-round-robin3$netlist
  (round-robin3& (round-robin3$netlist)))

(defconst *round-robin3$q8*  0)
(defconst *round-robin3$q10* 1)
(defconst *round-robin3$br*  2)
(defconst *round-robin3$me*  3)

(defund round-robin3$valid-st (st)
  (b* ((q8 (get-field *round-robin3$q8* st))
       (q10 (get-field *round-robin3$q10* st))
       (br (get-field *round-robin3$br* st))
       (me (get-field *round-robin3$me* st)))
    (and (queue8$valid-st q8)
         (queue10$valid-st q10)

         (alt-branch$valid-st br)
         (alt-merge$valid-st me))))

(defun round-robin3$map-to-links (st)
  (b* ((q8 (get-field *round-robin3$q8* st))
       (q10 (get-field *round-robin3$q10* st))
       (br (get-field *round-robin3$br* st))
       (me (get-field *round-robin3$me* st)))
    (append (list (cons 'alt-branch (alt-branch$map-to-links br)))
            (list (cons 'Q8 (queue8$map-to-links q8)))
            (list (cons 'Q10 (queue10$map-to-links q10)))
            (list (cons 'alt-merge (alt-merge$map-to-links me))))))

(defun round-robin3$map-to-links-list (x)
  (if (atom x)
      nil
    (cons (round-robin3$map-to-links (car x))
          (round-robin3$map-to-links-list (cdr x)))))

(defund round-robin3$sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *round-robin3$ins-len*)
       ((mv inputs-lst state) (go-vals-gen num-signals n state nil))
       ;;(- (cw "~x0~%" inputs-lst))
       (full '(t))
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
       (q8 (list q4-0 q4-1))
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
       (q10 (list q5-0 q5-1))
       (br (list full '(nil)
                 empty '(x)))
       (me (list full '(nil)
                 empty '(x)))
       (st (list q8 q10 br me)))
    (mv (pretty-list
         (remove-dup-neighbors
          (round-robin3$map-to-links-list
           (de-sim-list 'round-robin3 inputs-lst st (round-robin3$netlist))))
         0)
        state)))

(defun round-robin3$get-data-in (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (subseq-list inputs 2 (+ 2 *data-width*)))

(defthm len-round-robin3$get-data-in
  (equal (len (round-robin3$get-data-in inputs))
         *data-width*))

(in-theory (disable round-robin3$get-data-in))

(defund round-robin3$br-inputs (inputs st)
  (b* ((full-in (nth 0 inputs))
       (data-in (round-robin3$get-data-in inputs))
       (go-signals (nthcdr *round-robin3$data-ins-len* inputs))

       (br-go-signals (take *alt-branch$go-num*
                            (nthcdr (+ *queue8$go-num*
                                       *queue10$go-num*)
                                    go-signals)))

       (q8 (get-field *round-robin3$q8* st))
       (q10 (get-field *round-robin3$q10* st))

       (q8-ready-in- (queue8$ready-in- q8))
       (q10-ready-in- (queue10$ready-in- q10)))

    (list* full-in q8-ready-in- q10-ready-in-
           (append data-in br-go-signals))))

(defund round-robin3$me-inputs (inputs st)
  (b* ((full-out- (nth 1 inputs))
       (go-signals (nthcdr *round-robin3$data-ins-len* inputs))

       (me-go-signals (nthcdr (+ *queue8$go-num*
                                 *queue10$go-num*
                                 *alt-branch$go-num*)
                              go-signals))

       (q8 (get-field *round-robin3$q8* st))
       (q10 (get-field *round-robin3$q10* st))

       (q8-ready-out (queue8$ready-out q8))
       (q8-data-out (queue8$data-out q8))
       (q10-ready-out (queue10$ready-out q10))
       (q10-data-out (queue10$data-out q10)))

    (list* q8-ready-out q10-ready-out full-out-
           (append q8-data-out q10-data-out me-go-signals))))

(defund round-robin3$q8-inputs (inputs st)
  (b* ((data-in (round-robin3$get-data-in inputs))
       (go-signals (nthcdr *round-robin3$data-ins-len* inputs))

       (q8-go-signals (take *queue8$go-num* go-signals))

       (br (get-field *round-robin3$br* st))
       (me (get-field *round-robin3$me* st))

       (br-inputs (round-robin3$br-inputs inputs st))
       (me-inputs (round-robin3$me-inputs inputs st))

       (br-act0 (alt-branch$act0 br-inputs br))
       (me-act0 (alt-merge$act0 me-inputs me)))
    
    (list* br-act0 me-act0
           (append (v-threefix data-in)
                   q8-go-signals))))

(defund round-robin3$q10-inputs (inputs st)
  (b* ((data-in (round-robin3$get-data-in inputs))
       (go-signals (nthcdr *round-robin3$data-ins-len* inputs))

       (q10-go-signals (take *queue10$go-num*
                            (nthcdr *queue8$go-num*
                                    go-signals)))

       (br (get-field *round-robin3$br* st))
       (me (get-field *round-robin3$me* st))

       (br-inputs (round-robin3$br-inputs inputs st))
       (me-inputs (round-robin3$me-inputs inputs st))

       (br-act1 (alt-branch$act1 br-inputs br))
       (me-act1 (alt-merge$act1 me-inputs me)))
    
    (list* br-act1 me-act1
           (append (v-threefix data-in)
                   q10-go-signals))))

(defund round-robin3$in-act (inputs st)
  (b* ((br-inputs (round-robin3$br-inputs inputs st))
       (br (get-field *round-robin3$br* st)))
    (alt-branch$act br-inputs br)))

(defund round-robin3$out-act (inputs st)
  (b* ((me-inputs (round-robin3$me-inputs inputs st))
       (me (get-field *round-robin3$me* st)))
    (alt-merge$act me-inputs me)))

(defund round-robin3$data-out (st)
  (b* ((q8 (get-field *round-robin3$q8* st))
       (q10 (get-field *round-robin3$q10* st))
       (me (get-field *round-robin3$me* st))

       (q8-data-out (queue8$data-out q8))
       (q10-data-out (queue10$data-out q10))
       
       (mux (get-field *alt-merge$mux* me)))
    (fv-if (car mux)
           q10-data-out
           q8-data-out)))

(defthm round-robin3$data-out-props
   (implies (round-robin3$valid-st st)
            (and (bvp (round-robin3$data-out st))
                 (equal (len (round-robin3$data-out st))
                        *data-width*)))
   :hints (("Goal" :in-theory (enable round-robin3$valid-st
                                      round-robin3$data-out
                                      alt-merge$valid-st))))

(defthmd round-robin3$value
  (b* ((inputs (list* full-in full-out- (append data-in go-signals))))
    (implies (and (round-robin3& netlist)
                  (true-listp data-in)
                  (equal (len data-in) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *round-robin3$go-num*)
                  (round-robin3$valid-st st))
             (equal (se 'round-robin3 inputs st netlist)
                    (list* (round-robin3$in-act inputs st)
                           (round-robin3$out-act inputs st)
                           (round-robin3$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (se-rules
                            get-field
                            open-nth
                            len-1-true-listp=>true-listp
                            round-robin3&
                            round-robin3*$destructure
                            round-robin3$get-data-in
                            queue8$value
                            queue10$value
                            alt-branch$value
                            alt-merge$value
                            round-robin3$valid-st
                            round-robin3$in-act
                            round-robin3$out-act
                            round-robin3$data-out
                            round-robin3$br-inputs
                            round-robin3$me-inputs)
                           ((round-robin3*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(defun round-robin3$state-fn (inputs st)
  (b* ((q8 (get-field *round-robin3$q8* st))
       (q10 (get-field *round-robin3$q10* st))
       (br (get-field *round-robin3$br* st))
       (me (get-field *round-robin3$me* st))

       (q8-inputs (round-robin3$q8-inputs inputs st))
       (q10-inputs (round-robin3$q10-inputs inputs st))
       (br-inputs (round-robin3$br-inputs inputs st))
       (me-inputs (round-robin3$me-inputs inputs st)))
    
    (list
     (queue8$state-fn q8-inputs q8)
     (queue10$state-fn q10-inputs q10)

     (alt-branch$state-fn br-inputs br)
     (alt-merge$state-fn me-inputs me))))

(defthm len-of-round-robin3$state-fn
  (equal (len (round-robin3$state-fn inputs st))
         *round-robin3$st-len*))

(defthmd round-robin3$state
  (b* ((inputs (list* full-in full-out- (append data-in go-signals))))
    (implies (and (round-robin3& netlist)
                  (true-listp data-in)
                  (equal (len data-in) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *round-robin3$go-num*)
                  (round-robin3$valid-st st))
             (equal (de 'round-robin3 inputs st netlist)
                    (round-robin3$state-fn inputs st))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (de-rules
                            get-field
                            open-nth
                            len-1-true-listp=>true-listp
                            round-robin3&
                            round-robin3*$destructure
                            round-robin3$valid-st
                            round-robin3$get-data-in
                            round-robin3$q8-inputs
                            round-robin3$q10-inputs
                            round-robin3$br-inputs
                            round-robin3$me-inputs
                            queue8$value queue8$state
                            queue10$value queue10$state
                            alt-branch$value alt-branch$state
                            alt-merge$value alt-merge$state)
                           ((round-robin3*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(in-theory (disable round-robin3$state-fn))

;; ======================================================================

(defund round-robin3$input-format (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((full-in    (nth 0 inputs))
       (full-out-  (nth 1 inputs))
       (data-in    (round-robin3$get-data-in inputs))
       (go-signals (nthcdr *round-robin3$data-ins-len* inputs)))
    (and
     (booleanp full-in)
     (booleanp full-out-)
     (bvp data-in)
     (true-listp go-signals)
     (= (len go-signals) *round-robin3$go-num*)
     (equal inputs
            (list* full-in full-out- (append data-in go-signals))))))

(defthmd len-of-round-robin3$inputs
  (implies (round-robin3$input-format inputs)
           (equal (len inputs) *round-robin3$ins-len*))
  :hints (("Goal" :in-theory (enable round-robin3$input-format))))

(local
 (defthm round-robin3$input-format=>q8$input-format
   (implies (and (round-robin3$input-format inputs)
                 (round-robin3$valid-st st))
            (queue8$input-format
             (round-robin3$q8-inputs inputs st)
             (nth *round-robin3$q8* st)))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             queue8$input-format
                             queue8$in-act
                             queue8$out-act
                             queue8$get-data-in
                             alt-branch$valid-st
                             alt-branch$act
                             alt-branch$act0
                             alt-merge$valid-st
                             alt-merge$act
                             alt-merge$act0
                             round-robin3$input-format
                             round-robin3$valid-st
                             round-robin3$q8-inputs
                             round-robin3$br-inputs
                             round-robin3$me-inputs)
                            (nth
                             nthcdr
                             take-of-too-many
                             take-of-len-is-itself))))))

(local
 (defthm round-robin3$input-format=>q10$input-format
   (implies (and (round-robin3$input-format inputs)
                 (round-robin3$valid-st st))
            (queue10$input-format
             (round-robin3$q10-inputs inputs st)
             (nth *round-robin3$q10* st)))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             queue10$input-format
                             queue10$in-act
                             queue10$out-act
                             queue10$get-data-in
                             alt-branch$valid-st
                             alt-branch$act
                             alt-branch$act1
                             alt-merge$valid-st
                             alt-merge$act
                             alt-merge$act1
                             round-robin3$input-format
                             round-robin3$valid-st
                             round-robin3$q10-inputs
                             round-robin3$br-inputs
                             round-robin3$me-inputs)
                            (nth
                             nthcdr
                             take-of-too-many
                             take-of-len-is-itself))))))

(local
 (defthm round-robin3$input-format=>br$input-format
   (implies (and (round-robin3$input-format inputs)
                 (round-robin3$valid-st st))
            (alt-branch$input-format
             (round-robin3$br-inputs inputs st)))
   :hints (("Goal"
            :in-theory (e/d (alt-branch$input-format
                             alt-branch$get-data-in
                             round-robin3$input-format
                             round-robin3$valid-st
                             round-robin3$br-inputs)
                            (nth
                             nthcdr
                             take-of-too-many
                             take-of-len-is-itself))))))

(local
 (defthm round-robin3$input-format=>me$input-format
   (implies (and (round-robin3$input-format inputs)
                 (round-robin3$valid-st st))
            (alt-merge$input-format
             (round-robin3$me-inputs inputs st)))
   :hints (("Goal"
            :in-theory (e/d (len-of-round-robin3$inputs
                             alt-merge$input-format
                             alt-merge$get-data-in0
                             alt-merge$get-data-in1
                             round-robin3$input-format
                             round-robin3$valid-st
                             round-robin3$me-inputs)
                            (nth
                             nthcdr
                             take-of-too-many
                             take-of-len-is-itself))))))

(defthm round-robin3$valid-st-preserved
  (implies (and (round-robin3$input-format inputs)
                (round-robin3$valid-st st))
           (round-robin3$valid-st (round-robin3$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            round-robin3$valid-st
                            round-robin3$state-fn)
                           (nth)))))

(defthmd round-robin3$state-alt
  (implies (and (round-robin3& netlist)
                (round-robin3$input-format inputs)
                (round-robin3$valid-st st))
           (equal (de 'round-robin3 inputs st netlist)
                  (round-robin3$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (enable round-robin3$input-format)
           :use (:instance round-robin3$state
                           (full-in    (nth 0 inputs))
                           (full-out-  (nth 1 inputs))
                           (data-in    (round-robin3$get-data-in inputs))
                           (go-signals (nthcdr *round-robin3$data-ins-len*
                                               inputs))))))

(state-fn-n-gen round-robin3)

(input-format-n-gen round-robin3)

(defthmd de-sim-n$round-robin3
  (implies (and (round-robin3& netlist)
                (round-robin3$input-format-n inputs-lst n)
                (round-robin3$valid-st st))
           (equal (de-sim-n 'round-robin3 inputs-lst st netlist n)
                  (round-robin3$state-fn-n inputs-lst st n)))
  :hints (("Goal" :in-theory (enable round-robin3$state-alt))))

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

(defund round-robin3$extract-state (st)
  (b* ((q8 (get-field *round-robin3$q8* st))
       (q10 (get-field *round-robin3$q10* st))
       (me (get-field *round-robin3$me* st))

       (a-seq (queue8$extract-state q8))
       (b-seq (queue10$extract-state q10))

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

(defund round-robin3$inv (st)
  (b* ((q8 (get-field *round-robin3$q8* st))
       (q10 (get-field *round-robin3$q10* st))
       (br (get-field *round-robin3$br* st))
       (me (get-field *round-robin3$me* st))

       (a-seq (queue8$extract-state q8))
       (b-seq (queue10$extract-state q10))

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
 (defthm queue4$ready-out-lemma
   (implies (and (queue4$valid-st st)
                 (equal (len (queue4$extract-state st)) 0))
            (not (queue4$ready-out st)))
   :hints (("Goal" :in-theory (enable queue4$valid-st
                                      queue4$extract-state
                                      queue4$ready-out)))))

(local
 (defthm queue8$extract-state-not-empty
   (implies (and (booleanp (car (nth *alt-merge$mux*
                                     (nth *round-robin3$me* st))))
                 (queue8$out-act (round-robin3$q8-inputs inputs st))
                 (queue8$valid-st (nth *round-robin3$q8* st)))
            (< 0 (len (queue8$extract-state (nth *round-robin3$q8* st)))))
   :hints (("Goal"
            :in-theory (enable get-field
                               f-and3
                               f-if
                               round-robin3$q8-inputs
                               round-robin3$me-inputs
                               alt-merge$act0
                               queue8$valid-st
                               queue8$extract-state
                               queue8$ready-out
                               queue8$out-act)))
   :rule-classes :linear))

(local
 (defthm queue5$ready-out-lemma
   (implies (and (queue5$valid-st st)
                 (equal (len (queue5$extract-state st)) 0))
            (not (queue5$ready-out st)))
   :hints (("Goal" :in-theory (enable queue5$valid-st
                                      queue5$extract-state
                                      queue5$ready-out)))))

(local
 (defthm queue10$extract-state-not-empty
   (implies (and (booleanp (car (nth *alt-merge$mux*
                                     (nth *round-robin3$me* st))))
                 (queue10$out-act (round-robin3$q10-inputs inputs st))
                 (queue10$valid-st (nth *round-robin3$q10* st)))
            (< 0 (len (queue10$extract-state (nth *round-robin3$q10* st)))))
   :hints (("Goal"
            :in-theory (enable get-field
                               f-and3
                               f-if
                               round-robin3$q10-inputs
                               round-robin3$me-inputs
                               alt-merge$act1
                               queue10$valid-st
                               queue10$extract-state
                               queue10$ready-out
                               queue10$out-act)))
   :rule-classes :linear))

(local
 (defthm round-robin3$q8-in-act-nil-1
   (b* ((br (nth *round-robin3$br* st))
        
        (ldemux (nth *alt-branch$ldemux* br))
        (demux (nth *alt-branch$demux* br))
        (ldemux-buf (nth *alt-branch$ldemux-buf* br)))
     
     (implies (and (alt-branch$valid-st br)
                   (or (and (equal ldemux '(t))
                            (car demux))
                       (equal ldemux-buf '(t))))
              (not (queue8$in-act (round-robin3$q8-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      f-or3
                                      queue8$in-act
                                      alt-branch$valid-st
                                      alt-branch$act0
                                      round-robin3$q8-inputs)))))

(local
 (defthm round-robin3$q8-in-act-nil-2
   (implies (and (queue8$valid-st (nth *round-robin3$q8* st))
                 (queue8$ready-in- (nth *round-robin3$q8* st)))
            (not (queue8$in-act (round-robin3$q8-inputs inputs st))))
   :hints (("Goal" :in-theory (e/d (get-field
                                    f-or3
                                    queue8$valid-st
                                    queue8$ready-in-
                                    queue8$in-act
                                    alt-branch$act0
                                    round-robin3$q8-inputs
                                    round-robin3$br-inputs)
                                   (nth))))))

(local
 (defthm round-robin3$q8-out-act-nil-1
   (b* ((me (nth *round-robin3$me* st))
        
        (lmux (nth *alt-merge$lmux* me))
        (mux (nth *alt-merge$mux* me))
        (lmux-buf (nth *alt-merge$lmux-buf* me)))
     
     (implies (and (alt-merge$valid-st me)
                   (or (and (equal lmux '(t))
                            (car mux))
                       (equal lmux-buf '(t))))
              (not (queue8$out-act (round-robin3$q8-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      f-and3
                                      queue8$out-act
                                      alt-merge$valid-st
                                      alt-merge$act0
                                      round-robin3$q8-inputs)))))

(local
 (defthm round-robin3$q8-out-act-nil-2
   (implies (and (queue8$valid-st (nth *round-robin3$q8* st))
                 (not (queue8$ready-out (nth *round-robin3$q8* st))))
            (not (queue8$out-act (round-robin3$q8-inputs inputs st))))
   :hints (("Goal" :in-theory (e/d (get-field
                                    f-and3
                                    queue8$valid-st
                                    queue8$ready-out
                                    queue8$out-act
                                    alt-merge$act0
                                    round-robin3$q8-inputs
                                    round-robin3$me-inputs)
                                   (nth))))))

(local
 (defthm round-robin3$q10-in-act-nil-1
   (b* ((br (nth *round-robin3$br* st))
        
        (ldemux (nth *alt-branch$ldemux* br))
        (demux (nth *alt-branch$demux* br))
        (ldemux-buf (nth *alt-branch$ldemux-buf* br)))
     
     (implies (and (alt-branch$valid-st br)
                   (or (and (equal ldemux '(t))
                            (not (car demux)))
                       (equal ldemux-buf '(t))))
              (not (queue10$in-act (round-robin3$q10-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      f-or3
                                      queue10$in-act
                                      alt-branch$valid-st
                                      alt-branch$act1
                                      round-robin3$q10-inputs)))))

(local
 (defthm round-robin3$q10-in-act-nil-2
   (implies (and (queue10$valid-st (nth *round-robin3$q10* st))
                 (queue10$ready-in- (nth *round-robin3$q10* st)))
            (not (queue10$in-act (round-robin3$q10-inputs inputs st))))
   :hints (("Goal" :in-theory (e/d (get-field
                                    f-or3
                                    queue10$valid-st
                                    queue10$ready-in-
                                    queue10$in-act
                                    alt-branch$act1
                                    round-robin3$q10-inputs
                                    round-robin3$br-inputs)
                                   (nth))))))

(local
 (defthm round-robin3$q10-out-act-nil-1
   (b* ((me (nth *round-robin3$me* st))
        
        (lmux (nth *alt-merge$lmux* me))
        (mux (nth *alt-merge$mux* me))
        (lmux-buf (nth *alt-merge$lmux-buf* me)))
     
     (implies (and (alt-merge$valid-st me)
                   (or (and (equal lmux '(t))
                            (not (car mux)))
                       (equal lmux-buf '(t))))
              (not (queue10$out-act (round-robin3$q10-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      f-and3
                                      queue10$out-act
                                      alt-merge$valid-st
                                      alt-merge$act1
                                      round-robin3$q10-inputs)))))

(local
 (defthm round-robin3$q10-out-act-nil-2
   (implies (and (queue10$valid-st (nth *round-robin3$q10* st))
                 (not (queue10$ready-out (nth *round-robin3$q10* st))))
            (not (queue10$out-act (round-robin3$q10-inputs inputs st))))
   :hints (("Goal" :in-theory (e/d (get-field
                                    f-and3
                                    queue10$valid-st
                                    queue10$ready-out
                                    queue10$out-act
                                    alt-merge$act1
                                    round-robin3$q10-inputs
                                    round-robin3$me-inputs)
                                   (nth))))))

(local
 (defthm booleanp-round-robin3$q8-in-act
   (b* ((q8 (nth *round-robin3$q8* st))
        (br (nth *round-robin3$br* st))
        
        (ldemux (nth *alt-branch$ldemux* br))
        (demux (nth *alt-branch$demux* br))
        (ldemux-buf (nth *alt-branch$ldemux-buf* br)))
     
     (implies (and (booleanp (nth 0 inputs))
                   (queue8$valid-st q8)
                   (equal ldemux '(t))
                   (not (car demux))
                   (equal ldemux-buf '(nil)))
              (booleanp (queue8$in-act
                         (round-robin3$q8-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      queue8$in-act
                                      alt-branch$act0
                                      round-robin3$q8-inputs
                                      round-robin3$br-inputs)))
   :rule-classes :type-prescription))

(local
 (defthm round-robin3$rewrite-to-q8-in-act-1
   (b* ((q8 (nth *round-robin3$q8* st))
        (br (nth *round-robin3$br* st))
        
        (ldemux (nth *alt-branch$ldemux* br))
        (demux (nth *alt-branch$demux* br))
        (ldemux-buf (nth *alt-branch$ldemux-buf* br)))
     
     (implies (and (booleanp (nth 0 inputs))
                   (queue8$valid-st q8)
                   (equal ldemux '(t))
                   (not (car demux))
                   (equal ldemux-buf '(nil)))
              (equal (joint-act (nth 0 inputs)
                                (queue8$ready-in- q8)
                                (car (nthcdr (+ *round-robin3$data-ins-len*
                                                *queue8$go-num*
                                                *queue10$go-num*)
                                             inputs)))
                     (queue8$in-act
                      (round-robin3$q8-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      queue8$in-act
                                      alt-branch$act0
                                      round-robin3$q8-inputs
                                      round-robin3$br-inputs)))))

(local
 (defthm round-robin3$rewrite-to-q8-in-act-2
   (b* ((q8 (nth *round-robin3$q8* st))
        (br (nth *round-robin3$br* st))
        
        (ldemux (nth *alt-branch$ldemux* br))
        (demux (nth *alt-branch$demux* br))
        (ldemux-buf (nth *alt-branch$ldemux-buf* br)))
     
     (implies (and (booleanp (nth 0 inputs))
                   (queue8$valid-st q8)
                   (equal ldemux '(t))
                   (not (queue8$ready-in- q8))
                   (equal ldemux-buf '(nil)))
              (equal (joint-act (nth 0 inputs)
                                (car demux)
                                (car (nthcdr (+ *round-robin3$data-ins-len*
                                                *queue8$go-num*
                                                *queue10$go-num*)
                                             inputs)))
                     (queue8$in-act
                      (round-robin3$q8-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      f-or3
                                      queue8$in-act
                                      alt-branch$act0
                                      round-robin3$q8-inputs
                                      round-robin3$br-inputs)))))

(local
 (defthm round-robin3$rewrite-to-q8-in-act-3
   (b* ((q8 (nth *round-robin3$q8* st))
        (br (nth *round-robin3$br* st))
        
        (ldemux (nth *alt-branch$ldemux* br))
        (demux (nth *alt-branch$demux* br))
        (ldemux-buf (nth *alt-branch$ldemux-buf* br)))
     
     (implies (and (booleanp (nth 0 inputs))
                   (queue8$valid-st q8)
                   (equal ldemux '(t))
                   (not (queue8$ready-in- q8))
                   (not (car demux))
                   (equal ldemux-buf '(nil)))
              (equal (joint-act (nth 0 inputs)
                                nil
                                (car (nthcdr (+ *round-robin3$data-ins-len*
                                                *queue8$go-num*
                                                *queue10$go-num*)
                                             inputs)))
                     (queue8$in-act
                      (round-robin3$q8-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      f-or3
                                      queue8$in-act
                                      alt-branch$act0
                                      round-robin3$q8-inputs
                                      round-robin3$br-inputs)))))

(local
 (defthm booleanp-round-robin3$q8-out-act
   (b* ((q8 (nth *round-robin3$q8* st))
        (q10 (nth *round-robin3$q10* st))
        (me (nth *round-robin3$me* st))
        
        (lmux (nth *alt-merge$lmux* me))
        (mux (nth *alt-merge$mux* me))
        (lmux-buf (nth *alt-merge$lmux-buf* me)))
     
     (implies (and (booleanp (nth 1 inputs))
                   (queue8$valid-st q8)
                   (queue10$valid-st q10)
                   (equal lmux '(t))
                   (not (car mux))
                   (equal lmux-buf '(nil)))
              (booleanp (queue8$out-act
                         (round-robin3$q8-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      queue8$out-act
                                      alt-merge$act0
                                      round-robin3$q8-inputs
                                      round-robin3$me-inputs)))
   :rule-classes :type-prescription))

(local
 (defthm round-robin3$rewrite-to-q8-out-act-1
   (b* ((q8 (nth *round-robin3$q8* st))
        (q10 (nth *round-robin3$q10* st))
        (me (nth *round-robin3$me* st))
        
        (lmux (nth *alt-merge$lmux* me))
        (mux (nth *alt-merge$mux* me))
        (lmux-buf (nth *alt-merge$lmux-buf* me)))
     
     (implies (and (booleanp (nth 1 inputs))
                   (queue8$valid-st q8)
                   (queue10$valid-st q10)
                   (equal lmux '(t))
                   (not (car mux))
                   (equal lmux-buf '(nil)))
              (equal (joint-act (queue8$ready-out q8)
                                (nth 1 inputs)
                                (nth 0 (nthcdr (+ *round-robin3$data-ins-len*
                                                  *queue8$go-num*
                                                  *queue10$go-num*
                                                  *alt-branch$go-num*)
                                               inputs)))
                     (queue8$out-act
                      (round-robin3$q8-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      queue8$out-act
                                      alt-merge$act0
                                      round-robin3$q8-inputs
                                      round-robin3$me-inputs)))))

(local
 (defthm round-robin3$rewrite-to-q8-out-act-2
   (b* ((q8 (nth *round-robin3$q8* st))
        (q10 (nth *round-robin3$q10* st))
        (me (nth *round-robin3$me* st))
        
        (lmux (nth *alt-merge$lmux* me))
        (mux (nth *alt-merge$mux* me))
        (lmux-buf (nth *alt-merge$lmux-buf* me)))
     
     (implies (and (booleanp (nth 1 inputs))
                   (queue8$valid-st q8)
                   (queue10$valid-st q10)
                   (equal lmux '(t))
                   (queue8$ready-out q8)
                   (not (car mux))
                   (equal lmux-buf '(nil)))
              (equal (joint-act t
                                (nth 1 inputs)
                                (nth 0 (nthcdr (+ *round-robin3$data-ins-len*
                                                  *queue8$go-num*
                                                  *queue10$go-num*
                                                  *alt-branch$go-num*)
                                               inputs)))
                     (queue8$out-act
                      (round-robin3$q8-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      f-and3
                                      queue8$out-act
                                      alt-merge$act0
                                      round-robin3$q8-inputs
                                      round-robin3$me-inputs)))))

(local
 (defthm booleanp-round-robin3$q10-in-act
   (b* ((q10 (nth *round-robin3$q10* st))
        (br (nth *round-robin3$br* st))
        
        (ldemux (nth *alt-branch$ldemux* br))
        (demux (nth *alt-branch$demux* br))
        (ldemux-buf (nth *alt-branch$ldemux-buf* br)))
     
     (implies (and (booleanp (nth 0 inputs))
                   (queue10$valid-st q10)
                   (equal ldemux '(t))
                   (equal (car demux) t)
                   (equal ldemux-buf '(nil)))
              (booleanp (queue10$in-act
                         (round-robin3$q10-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      queue10$in-act
                                      alt-branch$act1
                                      round-robin3$q10-inputs
                                      round-robin3$br-inputs)))
   :rule-classes :type-prescription))

(local
 (defthm round-robin3$rewrite-to-q10-in-act-1
   (b* ((q10 (nth *round-robin3$q10* st))
        (br (nth *round-robin3$br* st))
        
        (ldemux (nth *alt-branch$ldemux* br))
        (demux (nth *alt-branch$demux* br))
        (ldemux-buf (nth *alt-branch$ldemux-buf* br)))
     
     (implies (and (booleanp (nth 0 inputs))
                   (queue10$valid-st q10)
                   (equal ldemux '(t))
                   (equal (car demux) t)
                   (equal ldemux-buf '(nil)))
              (equal (joint-act (nth 0 inputs)
                                (queue10$ready-in- q10)
                                (car (nthcdr (+ *round-robin3$data-ins-len*
                                                *queue8$go-num*
                                                *queue10$go-num*)
                                             inputs)))
                     (queue10$in-act
                      (round-robin3$q10-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      queue10$in-act
                                      alt-branch$act1
                                      round-robin3$q10-inputs
                                      round-robin3$br-inputs)))))

(local
 (defthm round-robin3$rewrite-to-q10-in-act-2
   (b* ((q10 (nth *round-robin3$q10* st))
        (br (nth *round-robin3$br* st))
        
        (ldemux (nth *alt-branch$ldemux* br))
        (demux (nth *alt-branch$demux* br))
        (ldemux-buf (nth *alt-branch$ldemux-buf* br)))
     
     (implies (and (booleanp (nth 0 inputs))
                   (queue10$valid-st q10)
                   (equal ldemux '(t))
                   (not (queue10$ready-in- q10))
                   (equal (car demux) t)
                   (equal ldemux-buf '(nil)))
              (equal (joint-act (nth 0 inputs)
                                nil
                                (car (nthcdr (+ *round-robin3$data-ins-len*
                                                *queue8$go-num*
                                                *queue10$go-num*)
                                             inputs)))
                     (queue10$in-act
                      (round-robin3$q10-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      f-or3
                                      queue10$in-act
                                      alt-branch$act1
                                      round-robin3$q10-inputs
                                      round-robin3$br-inputs)))))

(local
 (defthm booleanp-round-robin3$q10-out-act
   (b* ((q8 (nth *round-robin3$q8* st))
        (q10 (nth *round-robin3$q10* st))
        (me (nth *round-robin3$me* st))
        
        (lmux (nth *alt-merge$lmux* me))
        (mux (nth *alt-merge$mux* me))
        (lmux-buf (nth *alt-merge$lmux-buf* me)))
     
     (implies (and (booleanp (nth 1 inputs))
                   (queue8$valid-st q8)
                   (queue10$valid-st q10)
                   (equal lmux '(t))
                   (equal (car mux) t)
                   (equal lmux-buf '(nil)))
              (booleanp (queue10$out-act
                         (round-robin3$q10-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      queue10$out-act
                                      alt-merge$act1
                                      round-robin3$q10-inputs
                                      round-robin3$me-inputs)))
   :rule-classes :type-prescription))

(local
 (defthm round-robin3$rewrite-to-q10-out-act-1
   (b* ((q8 (nth *round-robin3$q8* st))
        (q10 (nth *round-robin3$q10* st))
        (me (nth *round-robin3$me* st))
        
        (lmux (nth *alt-merge$lmux* me))
        (mux (nth *alt-merge$mux* me))
        (lmux-buf (nth *alt-merge$lmux-buf* me)))
     
     (implies (and (booleanp (nth 1 inputs))
                   (queue8$valid-st q8)
                   (queue10$valid-st q10)
                   (equal lmux '(t))
                   (equal (car mux) t)
                   (equal lmux-buf '(nil)))
              (equal (joint-act (queue10$ready-out q10)
                                (nth 1 inputs)
                                (nth 0 (nthcdr (+ *round-robin3$data-ins-len*
                                                  *queue8$go-num*
                                                  *queue10$go-num*
                                                  *alt-branch$go-num*)
                                               inputs)))
                     (queue10$out-act
                      (round-robin3$q10-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      queue10$out-act
                                      alt-merge$act1
                                      round-robin3$q10-inputs
                                      round-robin3$me-inputs)))))

(local
 (defthm round-robin3$rewrite-to-q10-out-act-2
   (b* ((q8 (nth *round-robin3$q8* st))
        (q10 (nth *round-robin3$q10* st))
        (me (nth *round-robin3$me* st))
        
        (lmux (nth *alt-merge$lmux* me))
        (mux (nth *alt-merge$mux* me))
        (lmux-buf (nth *alt-merge$lmux-buf* me)))
     
     (implies (and (booleanp (nth 1 inputs))
                   (queue8$valid-st q8)
                   (queue10$valid-st q10)
                   (equal lmux '(t))
                   (queue10$ready-out q10)
                   (equal lmux-buf '(nil)))
              (equal (joint-act (car mux)
                                (nth 1 inputs)
                                (nth 0 (nthcdr (+ *round-robin3$data-ins-len*
                                                  *queue8$go-num*
                                                  *queue10$go-num*
                                                  *alt-branch$go-num*)
                                               inputs)))
                     (queue10$out-act
                      (round-robin3$q10-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      f-and3
                                      queue10$out-act
                                      alt-merge$act1
                                      round-robin3$q10-inputs
                                      round-robin3$me-inputs)))))

(local
 (defthm round-robin3$rewrite-to-q10-out-act-3
   (b* ((q8 (nth *round-robin3$q8* st))
        (q10 (nth *round-robin3$q10* st))
        (me (nth *round-robin3$me* st))
        
        (lmux (nth *alt-merge$lmux* me))
        (mux (nth *alt-merge$mux* me))
        (lmux-buf (nth *alt-merge$lmux-buf* me)))
     
     (implies (and (booleanp (nth 1 inputs))
                   (queue8$valid-st q8)
                   (queue10$valid-st q10)
                   (equal lmux '(t))
                   (queue10$ready-out q10)
                   (equal (car mux) t)
                   (equal lmux-buf '(nil)))
              (equal (joint-act t
                                (nth 1 inputs)
                                (nth 0 (nthcdr (+ *round-robin3$data-ins-len*
                                                  *queue8$go-num*
                                                  *queue10$go-num*
                                                  *alt-branch$go-num*)
                                               inputs)))
                     (queue10$out-act
                      (round-robin3$q10-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      f-and3
                                      queue10$out-act
                                      alt-merge$act1
                                      round-robin3$q10-inputs
                                      round-robin3$me-inputs)))))

(defthm round-robin3$inv-preserved
  (implies (and (round-robin3$input-format inputs)
                (round-robin3$valid-st st)
                (round-robin3$inv st))
           (round-robin3$inv (round-robin3$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue8$step-spec
                            queue10$step-spec
                            round-robin3$input-format
                            round-robin3$valid-st
                            round-robin3$inv
                            round-robin3$state-fn
                            round-robin3$in-act
                            round-robin3$out-act
                            round-robin3$br-inputs
                            round-robin3$me-inputs
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
                            alt-merge$act1)
                           (nfix
                            nth
                            nthcdr
                            len-nthcdr
                            append
                            pairlis$
                            strip-cars
                            true-listp
                            default-car
                            default-cdr
                            default-+-1
                            default-+-2
                            take-of-too-many
                            take-of-len-is-itself
                            open-v-threefix)))))

(defun round-robin3$in-seq (inputs-lst st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (round-robin3$in-act inputs st) t)
          (append (round-robin3$in-seq (cdr inputs-lst)
                                      (round-robin3$state-fn inputs st)
                                      (1- n))
                  (list (pairlis$ (round-robin3$get-data-in inputs)
                                  nil)))
        (round-robin3$in-seq (cdr inputs-lst)
                            (round-robin3$state-fn inputs st)
                            (1- n))))))

(defun round-robin3$out-seq (inputs-lst st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst))
         (extracted-st (round-robin3$extract-state st)))
      (if (equal (round-robin3$out-act inputs st) t)
          (append (round-robin3$out-seq (cdr inputs-lst)
                                       (round-robin3$state-fn inputs st)
                                       (1- n))
                  (list (nth (1- (len extracted-st))
                             extracted-st)))
        (round-robin3$out-seq (cdr inputs-lst)
                             (round-robin3$state-fn inputs st)
                             (1- n))))))

(defund round-robin3$in-out-seq-sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *round-robin3$ins-len*)
       ((mv inputs-lst state)
        (go-vals-gen num-signals n state nil))
       (full '(t))
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
       (q8 (list q4-0 q4-1))
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
       (q10 (list q5-0 q5-1))
       (br (list full '(nil)
                 empty '(x)))
       (me (list full '(nil)
                 empty '(x)))
       (st (list q8 q10 br me)))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-flatten-lst
                   (round-robin3$in-seq inputs-lst st n))))
      (list (cons 'out-seq
                  (v-to-nat-flatten-lst
                   (round-robin3$out-seq inputs-lst st n)))))
     state)))

(defund round-robin3$step-spec (inputs st)
  (b* ((data-in (round-robin3$get-data-in inputs))
       (extracted-st (round-robin3$extract-state st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (round-robin3$out-act inputs st) t)
      (cond
       ((equal (round-robin3$in-act inputs st) t)
        (cons (pairlis$ data-in nil)
              (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (round-robin3$in-act inputs st) t)
          (cons (pairlis$ data-in nil)
                extracted-st))
         (t extracted-st))))))

(encapsulate
  ()

  (local
   (defthm round-robin3$q8-and-q10-get-data-in-rewrite
     (implies (bvp (round-robin3$get-data-in inputs))
              (and (equal (queue8$get-data-in
                           (round-robin3$q8-inputs inputs st))
                          (round-robin3$get-data-in inputs))
                   (equal (queue10$get-data-in
                           (round-robin3$q10-inputs inputs st))
                          (round-robin3$get-data-in inputs))))
     :hints (("Goal"
              :in-theory (enable queue8$get-data-in
                                 queue10$get-data-in
                                 round-robin3$q8-inputs
                                 round-robin3$q10-inputs)))))

  (local
   (defthm cons-interleave
     (implies (consp l1)
              (equal (cons (car l1)
                           (interleave l2 (cdr l1)))
                     (interleave l1 l2)))))

  (local
   (defthmd take-interleave-1
     (implies (and (equal (len l1) (len l2))
                   (natp m)
                   (<= m (len l1))
                   (equal m (1+ n)))
              (equal (take (+ m n) (interleave l1 l2))
                     (interleave (take m l1) (take n l2))))))

  (local
   (defthmd take-interleave-2
     (implies (and (equal (len l1) (1+ (len l2)))
                   (natp m)
                   (<= m (len l1))
                   (equal m n))
              (equal (take (+ m n) (interleave l1 l2))
                     (interleave (take m l1) (take n l2))))))

  (local
   (defthm take-interleave-1-instance
     (implies (and (equal (len l1) (len l2))
                   (true-listp l1)
                   (equal m (+ -1 (len l1) (len l2)))
                   (equal n (1- (len l2))))
              (equal (take m (interleave l1 l2))
                     (interleave l1 (take n l2))))
     :hints (("Goal"
              :use (:instance take-interleave-1
                              (m (- m n)))))))

  (local
   (defthm take-interleave-2-instance
     (implies (and (equal (len l1) (1+ (len l2)))
                   (true-listp l2)
                   (equal m (1- (len l1)))
                   (equal n (+ -1 (len l1) (len l2))))
              (equal (take n (interleave l1 l2))
                     (interleave (take m l1) l2)))
     :hints (("Goal"
              :use (:instance take-interleave-2
                              (n (- n m)))))))

  (defthm round-robin3$step-spec-correct
    (b* ((next-st (round-robin3$state-fn inputs st)))
      (implies (and (round-robin3$input-format inputs)
                    (round-robin3$valid-st st)
                    (round-robin3$inv st))
               (equal (round-robin3$extract-state next-st)
                      (round-robin3$step-spec inputs st))))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              queue8$step-spec
                              queue10$step-spec
                              round-robin3$step-spec
                              round-robin3$input-format
                              round-robin3$valid-st
                              round-robin3$inv
                              round-robin3$state-fn
                              round-robin3$in-act
                              round-robin3$out-act
                              round-robin3$extract-state
                              round-robin3$br-inputs
                              round-robin3$me-inputs
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
                              pairlis$
                              strip-cars
                              not
                              take-of-len-is-itself
                              default-car
                              default-cdr
                              default-+-1
                              default-+-2)))))
  )

(encapsulate
  ()
  
  (local
   (defthm consp-queue8$extract-state-alt
     (implies (and (queue8$valid-st st)
                   (queue8$ready-out st))
              (consp (queue8$extract-state st)))
     :hints (("Goal" :in-theory (enable queue8$valid-st
                                        queue8$ready-out
                                        queue8$extract-state)))
     :rule-classes :type-prescription))

  (local
   (defthm consp-queue10$extract-state-alt
     (implies (and (queue10$valid-st st)
                   (queue10$ready-out st))
              (consp (queue10$extract-state st)))
     :hints (("Goal" :in-theory (enable queue10$valid-st
                                        queue10$ready-out
                                        queue10$extract-state)))
     :rule-classes :type-prescription))

  (defthm consp-round-robin3$extract-state
    (implies (and (round-robin3$input-format inputs)
                  (round-robin3$valid-st st)
                  (round-robin3$out-act inputs st))
             (consp (round-robin3$extract-state st)))
    :hints (("Goal"
             :in-theory (enable joint-act
                                round-robin3$input-format
                                round-robin3$valid-st
                                round-robin3$extract-state
                                round-robin3$out-act
                                round-robin3$me-inputs
                                alt-merge$valid-st
                                alt-merge$act
                                alt-merge$act0
                                alt-merge$act1)))
    :rule-classes :type-prescription)
  )

(encapsulate
  ()

  (local
   (defthm round-robin3$dataflow-correct-aux
     (implies (equal (append x1 y1)
                     (append (round-robin3$in-seq inputs-lst st n) y2))
              (equal (append x1 y1 z)
                     (append (round-robin3$in-seq inputs-lst st n) y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (acl2::associativity-of-append))))))

  (defthmd round-robin3$dataflow-correct
    (b* ((extracted-st (round-robin3$extract-state st))
         (final-st (round-robin3$state-fn-n inputs-lst st n))
         (final-extracted-st (round-robin3$extract-state final-st)))
      (implies (and (round-robin3$input-format-n inputs-lst n)
                    (round-robin3$valid-st st)
                    (round-robin3$inv st))
               (equal (append final-extracted-st
                              (round-robin3$out-seq inputs-lst st n))
                      (append (round-robin3$in-seq inputs-lst st n)
                              extracted-st))))
    :hints (("Goal"
             :in-theory (e/d (round-robin3$step-spec)
                             ()))))
  )

