;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; December 2017

(in-package "ADE")

(include-book "alt-branch")
(include-book "alt-merge")
(include-book "queue4-as-link")
(include-book "queue5-as-link")

(local (in-theory (e/d (f-buf-delete-lemmas-1
                        f-buf-delete-lemmas-2)
                       (nth-of-bvp-is-booleanp
                        take-of-len-free))))

;; ======================================================================

(defconst *round-robin2$data-ins-len* (+ 2 *data-width*))
(defconst *round-robin2$go-num* (+ *alt-branch$go-num*
                                  *alt-merge$go-num*
                                  *queue4$go-num*
                                  *queue5$go-num*))
(defconst *round-robin2$ins-len* (+ *round-robin2$data-ins-len*
                                   *round-robin2$go-num*))
(defconst *round-robin2$st-len* 4)

;; A round-robin module:
;;
;;   -> Q4 -
;;  |       |
;; -BR      ME->
;;  |       |
;;   -> Q5 -

(module-generator
 round-robin2* ()
 'round-robin2
 (list* 'full-in 'full-out- (append (sis 'data-in 0 *data-width*)
                                    (sis 'go 0 *round-robin2$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 *data-width*))
 '(q4 q5 br me)
 (list
  ;; LINKS
  ;; 4-link queue Q4
  (list 'q4
        (list* 'q4-ready-in- 'q4-ready-out
               (sis 'q4-data-out 0 *data-width*))
        'queue4
        (list* 'br-act0 'me-act0
               (append (sis 'data 0 *data-width*)
                       (sis 'go 0 *queue4$go-num*))))

  ;; 5-link queue Q5
  (list 'q5
        (list* 'q5-ready-in- 'q5-ready-out
               (sis 'q5-data-out 0 *data-width*))
        'queue5
        (list* 'br-act1 'me-act1
               (append (sis 'data 0 *data-width*)
                       (sis 'go
                            *queue4$go-num*
                            *queue5$go-num*))))

  ;; JOINTS
  ;; Alt-Branch
  (list 'br
        (list* 'in-act 'br-act0 'br-act1
               (sis 'data 0 *data-width*))
        'alt-branch
        (list* 'full-in 'q4-ready-in- 'q5-ready-in-
               (append (sis 'data-in 0 *data-width*)
                       (sis 'go
                            (+ *queue4$go-num*
                               *queue5$go-num*)
                            *alt-branch$go-num*))))

  ;; Alt-Merge
  (list 'me
        (list* 'out-act 'me-act0 'me-act1
               (sis 'data-out 0 *data-width*))
        'alt-merge
        (list* 'q4-ready-out 'q5-ready-out 'full-out-
               (append (sis 'q4-data-out 0 *data-width*)
                       (sis 'q5-data-out 0 *data-width*)
                       (sis 'go
                            (+ *queue4$go-num*
                               *queue5$go-num*
                               *alt-branch$go-num*)
                            *alt-merge$go-num*)))))

 :guard t)

(defun round-robin2$netlist ()
  (declare (xargs :guard t))
  (cons (round-robin2*)
        (union$ (queue4$netlist)
                (queue5$netlist)
                (alt-branch$netlist)
                (alt-merge$netlist)
                :test 'equal)))

(defthmd round-robin2$netlist-okp
  (and (net-syntax-okp (round-robin2$netlist))
       (net-arity-okp (round-robin2$netlist))))

(defund round-robin2& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (and (equal (assoc 'round-robin2 netlist)
              (round-robin2*))
       (b* ((netlist (delete-to-eq 'round-robin2 netlist)))
         (and (queue4& netlist)
              (queue5& netlist)
              (alt-branch& netlist)
              (alt-merge& netlist)))))

(defthm check-round-robin2$netlist
  (round-robin2& (round-robin2$netlist)))

(defconst *round-robin2$q4* 0)
(defconst *round-robin2$q5* 1)
(defconst *round-robin2$br* 2)
(defconst *round-robin2$me* 3)

(defund round-robin2$valid-st (st)
  (b* ((q4 (get-field *round-robin2$q4* st))
       (q5 (get-field *round-robin2$q5* st))
       (br (get-field *round-robin2$br* st))
       (me (get-field *round-robin2$me* st)))
    (and (queue4$valid-st q4)
         (queue5$valid-st q5)

         (alt-branch$valid-st br)
         (alt-merge$valid-st me))))

(defun round-robin2$map-to-links (st)
  (b* ((q4 (get-field *round-robin2$q4* st))
       (q5 (get-field *round-robin2$q5* st))
       (br (get-field *round-robin2$br* st))
       (me (get-field *round-robin2$me* st)))
    (append (list (cons 'alt-branch (alt-branch$map-to-links br)))
            (list (cons 'Q4 (queue4$map-to-links q4)))
            (list (cons 'Q5 (queue5$map-to-links q5)))
            (list (cons 'alt-merge (alt-merge$map-to-links me))))))

(defun round-robin2$map-to-links-list (x)
  (if (atom x)
      nil
    (cons (round-robin2$map-to-links (car x))
          (round-robin2$map-to-links-list (cdr x)))))

(defund round-robin2$sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *round-robin2$ins-len*)
       ((mv inputs-lst state) (go-vals-gen num-signals n state nil))
       ;;(- (cw "~x0~%" inputs-lst))
       (full '(t))
       (empty '(nil))
       (invalid-data (make-list *data-width* :initial-element '(x)))
       (q4 (list empty invalid-data
                 empty invalid-data
                 empty invalid-data
                 empty invalid-data))
       (q5 (list empty invalid-data
                 empty invalid-data
                 empty invalid-data
                 empty invalid-data
                 empty invalid-data))
       (br (list full '(nil)
                 empty '(x)))
       (me (list full '(nil)
                 empty '(x)))
       (st (list q4 q5 br me)))
    (mv (pretty-list
         (remove-dup-neighbors
          (round-robin2$map-to-links-list
           (de-sim-list 'round-robin2 inputs-lst st (round-robin2$netlist))))
         0)
        state)))

(defun round-robin2$get-data-in (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (subseq-list inputs 2 (+ 2 *data-width*)))

(defthm len-round-robin2$get-data-in
  (equal (len (round-robin2$get-data-in inputs))
         *data-width*))

(in-theory (disable round-robin2$get-data-in))

(defund round-robin2$br-inputs (inputs st)
  (b* ((full-in (nth 0 inputs))
       (data-in (round-robin2$get-data-in inputs))
       (go-signals (nthcdr *round-robin2$data-ins-len* inputs))

       (br-go-signals (take *alt-branch$go-num*
                            (nthcdr (+ *queue4$go-num*
                                       *queue5$go-num*)
                                    go-signals)))

       (q4 (get-field *round-robin2$q4* st))
       (q5 (get-field *round-robin2$q5* st))

       (q4-ready-in- (queue4$ready-in- q4))
       (q5-ready-in- (queue5$ready-in- q5)))

    (list* full-in q4-ready-in- q5-ready-in-
           (append data-in br-go-signals))))

(defund round-robin2$me-inputs (inputs st)
  (b* ((full-out- (nth 1 inputs))
       (go-signals (nthcdr *round-robin2$data-ins-len* inputs))

       (me-go-signals (nthcdr (+ *queue4$go-num*
                                 *queue5$go-num*
                                 *alt-branch$go-num*)
                              go-signals))

       (q4 (get-field *round-robin2$q4* st))
       (q5 (get-field *round-robin2$q5* st))

       (q4-ready-out (queue4$ready-out q4))
       (q4-data-out (queue4$data-out q4))
       (q5-ready-out (queue5$ready-out q5))
       (q5-data-out (queue5$data-out q5)))

    (list* q4-ready-out q5-ready-out full-out-
           (append q4-data-out q5-data-out me-go-signals))))

(defund round-robin2$q4-inputs (inputs st)
  (b* ((data-in (round-robin2$get-data-in inputs))
       (go-signals (nthcdr *round-robin2$data-ins-len* inputs))

       (q4-go-signals (take *queue4$go-num* go-signals))

       (br (get-field *round-robin2$br* st))
       (me (get-field *round-robin2$me* st))

       (br-inputs (round-robin2$br-inputs inputs st))
       (me-inputs (round-robin2$me-inputs inputs st))

       (br-act0 (alt-branch$act0 br-inputs br))
       (me-act0 (alt-merge$act0 me-inputs me)))
    
    (list* br-act0 me-act0
           (append (v-threefix data-in)
                   q4-go-signals))))

(defund round-robin2$q5-inputs (inputs st)
  (b* ((data-in (round-robin2$get-data-in inputs))
       (go-signals (nthcdr *round-robin2$data-ins-len* inputs))

       (q5-go-signals (take *queue5$go-num*
                            (nthcdr *queue4$go-num*
                                    go-signals)))

       (br (get-field *round-robin2$br* st))
       (me (get-field *round-robin2$me* st))

       (br-inputs (round-robin2$br-inputs inputs st))
       (me-inputs (round-robin2$me-inputs inputs st))

       (br-act1 (alt-branch$act1 br-inputs br))
       (me-act1 (alt-merge$act1 me-inputs me)))
    
    (list* br-act1 me-act1
           (append (v-threefix data-in)
                   q5-go-signals))))

(defund round-robin2$in-act (inputs st)
  (b* ((br-inputs (round-robin2$br-inputs inputs st))
       (br (get-field *round-robin2$br* st)))
    (alt-branch$act br-inputs br)))

(defund round-robin2$out-act (inputs st)
  (b* ((me-inputs (round-robin2$me-inputs inputs st))
       (me (get-field *round-robin2$me* st)))
    (alt-merge$act me-inputs me)))

(defund round-robin2$data-out (st)
  (b* ((q4 (get-field *round-robin2$q4* st))
       (q5 (get-field *round-robin2$q5* st))
       (me (get-field *round-robin2$me* st))

       (q4-data-out (queue4$data-out q4))
       (q5-data-out (queue5$data-out q5))
       
       (mux (get-field *alt-merge$mux* me)))
    (fv-if (car mux)
           q5-data-out
           q4-data-out)))

(defthm round-robin2$data-out-props
   (implies (round-robin2$valid-st st)
            (and (bvp (round-robin2$data-out st))
                 (equal (len (round-robin2$data-out st))
                        *data-width*)))
   :hints (("Goal" :in-theory (enable round-robin2$valid-st
                                      round-robin2$data-out
                                      alt-merge$valid-st))))

(defthmd round-robin2$value
  (b* ((inputs (list* full-in full-out- (append data-in go-signals))))
    (implies (and (round-robin2& netlist)
                  (true-listp data-in)
                  (equal (len data-in) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *round-robin2$go-num*)
                  (round-robin2$valid-st st))
             (equal (se 'round-robin2 inputs st netlist)
                    (list* (round-robin2$in-act inputs st)
                           (round-robin2$out-act inputs st)
                           (round-robin2$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (se-rules
                            get-field
                            open-nth
                            len-1-true-listp=>true-listp
                            round-robin2&
                            round-robin2*$destructure
                            round-robin2$get-data-in
                            queue4$value
                            queue5$value
                            alt-branch$value
                            alt-merge$value
                            round-robin2$valid-st
                            round-robin2$in-act
                            round-robin2$out-act
                            round-robin2$data-out
                            round-robin2$br-inputs
                            round-robin2$me-inputs)
                           ((round-robin2*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(defun round-robin2$state-fn (inputs st)
  (b* ((q4 (get-field *round-robin2$q4* st))
       (q5 (get-field *round-robin2$q5* st))
       (br (get-field *round-robin2$br* st))
       (me (get-field *round-robin2$me* st))

       (q4-inputs (round-robin2$q4-inputs inputs st))
       (q5-inputs (round-robin2$q5-inputs inputs st))
       (br-inputs (round-robin2$br-inputs inputs st))
       (me-inputs (round-robin2$me-inputs inputs st)))
    
    (list
     (queue4$state-fn q4-inputs q4)
     (queue5$state-fn q5-inputs q5)

     (alt-branch$state-fn br-inputs br)
     (alt-merge$state-fn me-inputs me))))

(defthm len-of-round-robin2$state-fn
  (equal (len (round-robin2$state-fn inputs st))
         *round-robin2$st-len*))

(defthmd round-robin2$state
  (b* ((inputs (list* full-in full-out- (append data-in go-signals))))
    (implies (and (round-robin2& netlist)
                  (true-listp data-in)
                  (equal (len data-in) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *round-robin2$go-num*)
                  (round-robin2$valid-st st))
             (equal (de 'round-robin2 inputs st netlist)
                    (round-robin2$state-fn inputs st))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (de-rules
                            get-field
                            open-nth
                            len-1-true-listp=>true-listp
                            round-robin2&
                            round-robin2*$destructure
                            round-robin2$valid-st
                            round-robin2$get-data-in
                            round-robin2$q4-inputs
                            round-robin2$q5-inputs
                            round-robin2$br-inputs
                            round-robin2$me-inputs
                            queue4$value queue4$state
                            queue5$value queue5$state
                            alt-branch$value alt-branch$state
                            alt-merge$value alt-merge$state)
                           ((round-robin2*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(in-theory (disable round-robin2$state-fn))

;; ======================================================================

(defund round-robin2$input-format (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((full-in    (nth 0 inputs))
       (full-out-  (nth 1 inputs))
       (data-in    (round-robin2$get-data-in inputs))
       (go-signals (nthcdr *round-robin2$data-ins-len* inputs)))
    (and
     (booleanp full-in)
     (booleanp full-out-)
     (bvp data-in)
     (true-listp go-signals)
     (= (len go-signals) *round-robin2$go-num*)
     (equal inputs
            (list* full-in full-out- (append data-in go-signals))))))

(defthmd len-of-round-robin2$inputs
  (implies (round-robin2$input-format inputs)
           (equal (len inputs) *round-robin2$ins-len*))
  :hints (("Goal" :in-theory (enable round-robin2$input-format))))

(local
 (defthm round-robin2$input-format=>q4$input-format
   (implies (and (round-robin2$input-format inputs)
                 (round-robin2$valid-st st))
            (queue4$input-format
             (round-robin2$q4-inputs inputs st)
             (nth *round-robin2$q4* st)))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             queue4$input-format
                             queue4$in-act
                             queue4$out-act
                             queue4$get-data-in
                             alt-branch$valid-st
                             alt-branch$act
                             alt-branch$act0
                             alt-merge$valid-st
                             alt-merge$act
                             alt-merge$act0
                             round-robin2$input-format
                             round-robin2$valid-st
                             round-robin2$q4-inputs
                             round-robin2$br-inputs
                             round-robin2$me-inputs)
                            (nth
                             nthcdr
                             take-of-too-many
                             take-of-len-is-itself))))))

(local
 (defthm round-robin2$input-format=>q5$input-format
   (implies (and (round-robin2$input-format inputs)
                 (round-robin2$valid-st st))
            (queue5$input-format
             (round-robin2$q5-inputs inputs st)
             (nth *round-robin2$q5* st)))
   :hints (("Goal"
            :in-theory (e/d (get-field
                             queue5$input-format
                             queue5$in-act
                             queue5$out-act
                             queue5$get-data-in
                             alt-branch$valid-st
                             alt-branch$act
                             alt-branch$act1
                             alt-merge$valid-st
                             alt-merge$act
                             alt-merge$act1
                             round-robin2$input-format
                             round-robin2$valid-st
                             round-robin2$q5-inputs
                             round-robin2$br-inputs
                             round-robin2$me-inputs)
                            (nth
                             nthcdr
                             take-of-too-many
                             take-of-len-is-itself))))))

(local
 (defthm round-robin2$input-format=>br$input-format
   (implies (and (round-robin2$input-format inputs)
                 (round-robin2$valid-st st))
            (alt-branch$input-format
             (round-robin2$br-inputs inputs st)))
   :hints (("Goal"
            :in-theory (e/d (alt-branch$input-format
                             alt-branch$get-data-in
                             round-robin2$input-format
                             round-robin2$valid-st
                             round-robin2$br-inputs)
                            (nth
                             nthcdr
                             take-of-too-many
                             take-of-len-is-itself))))))

(local
 (defthm round-robin2$input-format=>me$input-format
   (implies (and (round-robin2$input-format inputs)
                 (round-robin2$valid-st st))
            (alt-merge$input-format
             (round-robin2$me-inputs inputs st)))
   :hints (("Goal"
            :in-theory (e/d (len-of-round-robin2$inputs
                             alt-merge$input-format
                             alt-merge$get-data-in0
                             alt-merge$get-data-in1
                             round-robin2$input-format
                             round-robin2$valid-st
                             round-robin2$me-inputs)
                            (nth
                             nthcdr
                             take-of-too-many
                             take-of-len-is-itself))))))

(defthm round-robin2$valid-st-preserved
  (implies (and (round-robin2$input-format inputs)
                (round-robin2$valid-st st))
           (round-robin2$valid-st (round-robin2$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            round-robin2$valid-st
                            round-robin2$state-fn)
                           (nth)))))

(defthmd round-robin2$state-alt
  (implies (and (round-robin2& netlist)
                (round-robin2$input-format inputs)
                (round-robin2$valid-st st))
           (equal (de 'round-robin2 inputs st netlist)
                  (round-robin2$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (enable round-robin2$input-format)
           :use (:instance round-robin2$state
                           (full-in    (nth 0 inputs))
                           (full-out-  (nth 1 inputs))
                           (data-in    (round-robin2$get-data-in inputs))
                           (go-signals (nthcdr *round-robin2$data-ins-len*
                                               inputs))))))

(state-fn-n-gen round-robin2)

(input-format-n-gen round-robin2)

(defthmd de-sim-n$round-robin2
  (implies (and (round-robin2& netlist)
                (round-robin2$input-format-n inputs-lst n)
                (round-robin2$valid-st st))
           (equal (de-sim-n 'round-robin2 inputs-lst st netlist n)
                  (round-robin2$state-fn-n inputs-lst st n)))
  :hints (("Goal" :in-theory (enable round-robin2$state-alt))))

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

(defund round-robin2$extract-state (st)
  (b* ((q4 (get-field *round-robin2$q4* st))
       (q5 (get-field *round-robin2$q5* st))
       (me (get-field *round-robin2$me* st))

       (a-seq (queue4$extract-state q4))
       (b-seq (queue5$extract-state q5))

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

(defund round-robin2$inv (st)
  (b* ((q4 (get-field *round-robin2$q4* st))
       (q5 (get-field *round-robin2$q5* st))
       (br (get-field *round-robin2$br* st))
       (me (get-field *round-robin2$me* st))

       (a-seq (queue4$extract-state q4))
       (b-seq (queue5$extract-state q5))

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
 (defthm queue4$extract-state-not-empty
   (implies (and (booleanp (car (nth *alt-merge$mux*
                                     (nth *round-robin2$me* st))))
                 (queue4$out-act (round-robin2$q4-inputs inputs st))
                 (queue4$valid-st (nth *round-robin2$q4* st)))
            (< 0 (len (queue4$extract-state (nth *round-robin2$q4* st)))))
   :hints (("Goal"
            :in-theory (enable get-field
                               f-and3
                               f-if
                               round-robin2$q4-inputs
                               round-robin2$me-inputs
                               alt-merge$act0
                               queue4$valid-st
                               queue4$extract-state
                               queue4$ready-out
                               queue4$out-act)))
   :rule-classes :linear))

(local
 (defthm queue5$extract-state-not-empty
   (implies (and (booleanp (car (nth *alt-merge$mux*
                                     (nth *round-robin2$me* st))))
                 (queue5$out-act (round-robin2$q5-inputs inputs st))
                 (queue5$valid-st (nth *round-robin2$q5* st)))
            (< 0 (len (queue5$extract-state (nth *round-robin2$q5* st)))))
   :hints (("Goal"
            :in-theory (enable get-field
                               f-and3
                               f-if
                               round-robin2$q5-inputs
                               round-robin2$me-inputs
                               alt-merge$act1
                               queue5$valid-st
                               queue5$extract-state
                               queue5$ready-out
                               queue5$out-act)))
   :rule-classes :linear))

(local
 (defthm round-robin2$q4-in-act-nil-1
   (b* ((br (nth *round-robin2$br* st))
        
        (ldemux (nth *alt-branch$ldemux* br))
        (demux (nth *alt-branch$demux* br))
        (ldemux-buf (nth *alt-branch$ldemux-buf* br)))
     
     (implies (and (alt-branch$valid-st br)
                   (or (and (equal ldemux '(t))
                            (car demux))
                       (equal ldemux-buf '(t))))
              (not (queue4$in-act (round-robin2$q4-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      f-or3
                                      queue4$in-act
                                      alt-branch$valid-st
                                      alt-branch$act0
                                      round-robin2$q4-inputs)))))

(local
 (defthm round-robin2$q4-in-act-nil-2
   (implies (and (queue4$valid-st (nth *round-robin2$q4* st))
                 (queue4$ready-in- (nth *round-robin2$q4* st)))
            (not (queue4$in-act (round-robin2$q4-inputs inputs st))))
   :hints (("Goal" :in-theory (e/d (get-field
                                    f-or3
                                    queue4$valid-st
                                    queue4$ready-in-
                                    queue4$in-act
                                    alt-branch$act0
                                    round-robin2$q4-inputs
                                    round-robin2$br-inputs)
                                   (nth))))))

(local
 (defthm round-robin2$q4-out-act-nil-1
   (b* ((me (nth *round-robin2$me* st))
        
        (lmux (nth *alt-merge$lmux* me))
        (mux (nth *alt-merge$mux* me))
        (lmux-buf (nth *alt-merge$lmux-buf* me)))
     
     (implies (and (alt-merge$valid-st me)
                   (or (and (equal lmux '(t))
                            (car mux))
                       (equal lmux-buf '(t))))
              (not (queue4$out-act (round-robin2$q4-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      f-and3
                                      queue4$out-act
                                      alt-merge$valid-st
                                      alt-merge$act0
                                      round-robin2$q4-inputs)))))

(local
 (defthm round-robin2$q4-out-act-nil-2
   (implies (and (queue4$valid-st (nth *round-robin2$q4* st))
                 (not (queue4$ready-out (nth *round-robin2$q4* st))))
            (not (queue4$out-act (round-robin2$q4-inputs inputs st))))
   :hints (("Goal" :in-theory (e/d (get-field
                                    f-and3
                                    queue4$valid-st
                                    queue4$ready-out
                                    queue4$out-act
                                    alt-merge$act0
                                    round-robin2$q4-inputs
                                    round-robin2$me-inputs)
                                   (nth))))))

(local
 (defthm round-robin2$q5-in-act-nil-1
   (b* ((br (nth *round-robin2$br* st))
        
        (ldemux (nth *alt-branch$ldemux* br))
        (demux (nth *alt-branch$demux* br))
        (ldemux-buf (nth *alt-branch$ldemux-buf* br)))
     
     (implies (and (alt-branch$valid-st br)
                   (or (and (equal ldemux '(t))
                            (not (car demux)))
                       (equal ldemux-buf '(t))))
              (not (queue5$in-act (round-robin2$q5-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      f-or3
                                      queue5$in-act
                                      alt-branch$valid-st
                                      alt-branch$act1
                                      round-robin2$q5-inputs)))))

(local
 (defthm round-robin2$q5-in-act-nil-2
   (implies (and (queue5$valid-st (nth *round-robin2$q5* st))
                 (queue5$ready-in- (nth *round-robin2$q5* st)))
            (not (queue5$in-act (round-robin2$q5-inputs inputs st))))
   :hints (("Goal" :in-theory (e/d (get-field
                                    f-or3
                                    queue5$valid-st
                                    queue5$ready-in-
                                    queue5$in-act
                                    alt-branch$act1
                                    round-robin2$q5-inputs
                                    round-robin2$br-inputs)
                                   (nth))))))

(local
 (defthm round-robin2$q5-out-act-nil-1
   (b* ((me (nth *round-robin2$me* st))
        
        (lmux (nth *alt-merge$lmux* me))
        (mux (nth *alt-merge$mux* me))
        (lmux-buf (nth *alt-merge$lmux-buf* me)))
     
     (implies (and (alt-merge$valid-st me)
                   (or (and (equal lmux '(t))
                            (not (car mux)))
                       (equal lmux-buf '(t))))
              (not (queue5$out-act (round-robin2$q5-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      f-and3
                                      queue5$out-act
                                      alt-merge$valid-st
                                      alt-merge$act1
                                      round-robin2$q5-inputs)))))

(local
 (defthm round-robin2$q5-out-act-nil-2
   (implies (and (queue5$valid-st (nth *round-robin2$q5* st))
                 (not (queue5$ready-out (nth *round-robin2$q5* st))))
            (not (queue5$out-act (round-robin2$q5-inputs inputs st))))
   :hints (("Goal" :in-theory (e/d (get-field
                                    f-and3
                                    queue5$valid-st
                                    queue5$ready-out
                                    queue5$out-act
                                    alt-merge$act1
                                    round-robin2$q5-inputs
                                    round-robin2$me-inputs)
                                   (nth))))))

(local
 (defthm booleanp-round-robin2$q4-in-act
   (b* ((q4 (nth *round-robin2$q4* st))
        (br (nth *round-robin2$br* st))
        
        (ldemux (nth *alt-branch$ldemux* br))
        (demux (nth *alt-branch$demux* br))
        (ldemux-buf (nth *alt-branch$ldemux-buf* br)))
     
     (implies (and (booleanp (nth 0 inputs))
                   (queue4$valid-st q4)
                   (equal ldemux '(t))
                   (not (car demux))
                   (equal ldemux-buf '(nil)))
              (booleanp (queue4$in-act
                         (round-robin2$q4-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      queue4$in-act
                                      alt-branch$act0
                                      round-robin2$q4-inputs
                                      round-robin2$br-inputs)))
   :rule-classes :type-prescription))

(local
 (defthm round-robin2$rewrite-to-q4-in-act-1
   (b* ((q4 (nth *round-robin2$q4* st))
        (br (nth *round-robin2$br* st))
        
        (ldemux (nth *alt-branch$ldemux* br))
        (demux (nth *alt-branch$demux* br))
        (ldemux-buf (nth *alt-branch$ldemux-buf* br)))
     
     (implies (and (booleanp (nth 0 inputs))
                   (queue4$valid-st q4)
                   (equal ldemux '(t))
                   (not (car demux))
                   (equal ldemux-buf '(nil)))
              (equal (joint-act (nth 0 inputs)
                                (queue4$ready-in- q4)
                                (car (nthcdr (+ *round-robin2$data-ins-len*
                                                *queue4$go-num*
                                                *queue5$go-num*)
                                             inputs)))
                     (queue4$in-act
                      (round-robin2$q4-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      queue4$in-act
                                      alt-branch$act0
                                      round-robin2$q4-inputs
                                      round-robin2$br-inputs)))))

(local
 (defthm round-robin2$rewrite-to-q4-in-act-2
   (b* ((q4 (nth *round-robin2$q4* st))
        (br (nth *round-robin2$br* st))
        
        (ldemux (nth *alt-branch$ldemux* br))
        (demux (nth *alt-branch$demux* br))
        (ldemux-buf (nth *alt-branch$ldemux-buf* br)))
     
     (implies (and (booleanp (nth 0 inputs))
                   (queue4$valid-st q4)
                   (equal ldemux '(t))
                   (not (queue4$ready-in- q4))
                   (equal ldemux-buf '(nil)))
              (equal (joint-act (nth 0 inputs)
                                (car demux)
                                (car (nthcdr (+ *round-robin2$data-ins-len*
                                                *queue4$go-num*
                                                *queue5$go-num*)
                                             inputs)))
                     (queue4$in-act
                      (round-robin2$q4-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      f-or3
                                      queue4$in-act
                                      alt-branch$act0
                                      round-robin2$q4-inputs
                                      round-robin2$br-inputs)))))

(local
 (defthm round-robin2$rewrite-to-q4-in-act-3
   (b* ((q4 (nth *round-robin2$q4* st))
        (br (nth *round-robin2$br* st))
        
        (ldemux (nth *alt-branch$ldemux* br))
        (demux (nth *alt-branch$demux* br))
        (ldemux-buf (nth *alt-branch$ldemux-buf* br)))
     
     (implies (and (booleanp (nth 0 inputs))
                   (queue4$valid-st q4)
                   (equal ldemux '(t))
                   (not (queue4$ready-in- q4))
                   (not (car demux))
                   (equal ldemux-buf '(nil)))
              (equal (joint-act (nth 0 inputs)
                                nil
                                (car (nthcdr (+ *round-robin2$data-ins-len*
                                                *queue4$go-num*
                                                *queue5$go-num*)
                                             inputs)))
                     (queue4$in-act
                      (round-robin2$q4-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      f-or3
                                      queue4$in-act
                                      alt-branch$act0
                                      round-robin2$q4-inputs
                                      round-robin2$br-inputs)))))

(local
 (defthm booleanp-round-robin2$q4-out-act
   (b* ((q4 (nth *round-robin2$q4* st))
        (q5 (nth *round-robin2$q5* st))
        (me (nth *round-robin2$me* st))
        
        (lmux (nth *alt-merge$lmux* me))
        (mux (nth *alt-merge$mux* me))
        (lmux-buf (nth *alt-merge$lmux-buf* me)))
     
     (implies (and (booleanp (nth 1 inputs))
                   (queue4$valid-st q4)
                   (queue5$valid-st q5)
                   (equal lmux '(t))
                   (not (car mux))
                   (equal lmux-buf '(nil)))
              (booleanp (queue4$out-act
                         (round-robin2$q4-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      queue4$out-act
                                      alt-merge$act0
                                      round-robin2$q4-inputs
                                      round-robin2$me-inputs)))
   :rule-classes :type-prescription))

(local
 (defthm round-robin2$rewrite-to-q4-out-act-1
   (b* ((q4 (nth *round-robin2$q4* st))
        (q5 (nth *round-robin2$q5* st))
        (me (nth *round-robin2$me* st))
        
        (lmux (nth *alt-merge$lmux* me))
        (mux (nth *alt-merge$mux* me))
        (lmux-buf (nth *alt-merge$lmux-buf* me)))
     
     (implies (and (booleanp (nth 1 inputs))
                   (queue4$valid-st q4)
                   (queue5$valid-st q5)
                   (equal lmux '(t))
                   (not (car mux))
                   (equal lmux-buf '(nil)))
              (equal (joint-act (queue4$ready-out q4)
                                (nth 1 inputs)
                                (nth 0 (nthcdr (+ *round-robin2$data-ins-len*
                                                  *queue4$go-num*
                                                  *queue5$go-num*
                                                  *alt-branch$go-num*)
                                               inputs)))
                     (queue4$out-act
                      (round-robin2$q4-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      queue4$out-act
                                      alt-merge$act0
                                      round-robin2$q4-inputs
                                      round-robin2$me-inputs)))))

(local
 (defthm round-robin2$rewrite-to-q4-out-act-2
   (b* ((q4 (nth *round-robin2$q4* st))
        (q5 (nth *round-robin2$q5* st))
        (me (nth *round-robin2$me* st))
        
        (lmux (nth *alt-merge$lmux* me))
        (mux (nth *alt-merge$mux* me))
        (lmux-buf (nth *alt-merge$lmux-buf* me)))
     
     (implies (and (booleanp (nth 1 inputs))
                   (queue4$valid-st q4)
                   (queue5$valid-st q5)
                   (equal lmux '(t))
                   (queue4$ready-out q4)
                   (not (car mux))
                   (equal lmux-buf '(nil)))
              (equal (joint-act t
                                (nth 1 inputs)
                                (nth 0 (nthcdr (+ *round-robin2$data-ins-len*
                                                  *queue4$go-num*
                                                  *queue5$go-num*
                                                  *alt-branch$go-num*)
                                               inputs)))
                     (queue4$out-act
                      (round-robin2$q4-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      f-and3
                                      queue4$out-act
                                      alt-merge$act0
                                      round-robin2$q4-inputs
                                      round-robin2$me-inputs)))))

(local
 (defthm booleanp-round-robin2$q5-in-act
   (b* ((q5 (nth *round-robin2$q5* st))
        (br (nth *round-robin2$br* st))
        
        (ldemux (nth *alt-branch$ldemux* br))
        (demux (nth *alt-branch$demux* br))
        (ldemux-buf (nth *alt-branch$ldemux-buf* br)))
     
     (implies (and (booleanp (nth 0 inputs))
                   (queue5$valid-st q5)
                   (equal ldemux '(t))
                   (equal (car demux) t)
                   (equal ldemux-buf '(nil)))
              (booleanp (queue5$in-act
                         (round-robin2$q5-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      queue5$in-act
                                      alt-branch$act1
                                      round-robin2$q5-inputs
                                      round-robin2$br-inputs)))
   :rule-classes :type-prescription))

(local
 (defthm round-robin2$rewrite-to-q5-in-act-1
   (b* ((q5 (nth *round-robin2$q5* st))
        (br (nth *round-robin2$br* st))
        
        (ldemux (nth *alt-branch$ldemux* br))
        (demux (nth *alt-branch$demux* br))
        (ldemux-buf (nth *alt-branch$ldemux-buf* br)))
     
     (implies (and (booleanp (nth 0 inputs))
                   (queue5$valid-st q5)
                   (equal ldemux '(t))
                   (equal (car demux) t)
                   (equal ldemux-buf '(nil)))
              (equal (joint-act (nth 0 inputs)
                                (queue5$ready-in- q5)
                                (car (nthcdr (+ *round-robin2$data-ins-len*
                                                *queue4$go-num*
                                                *queue5$go-num*)
                                             inputs)))
                     (queue5$in-act
                      (round-robin2$q5-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      queue5$in-act
                                      alt-branch$act1
                                      round-robin2$q5-inputs
                                      round-robin2$br-inputs)))))

(local
 (defthm round-robin2$rewrite-to-q5-in-act-2
   (b* ((q5 (nth *round-robin2$q5* st))
        (br (nth *round-robin2$br* st))
        
        (ldemux (nth *alt-branch$ldemux* br))
        (demux (nth *alt-branch$demux* br))
        (ldemux-buf (nth *alt-branch$ldemux-buf* br)))
     
     (implies (and (booleanp (nth 0 inputs))
                   (queue5$valid-st q5)
                   (equal ldemux '(t))
                   (not (queue5$ready-in- q5))
                   (equal (car demux) t)
                   (equal ldemux-buf '(nil)))
              (equal (joint-act (nth 0 inputs)
                                nil
                                (car (nthcdr (+ *round-robin2$data-ins-len*
                                                *queue4$go-num*
                                                *queue5$go-num*)
                                             inputs)))
                     (queue5$in-act
                      (round-robin2$q5-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      f-or3
                                      queue5$in-act
                                      alt-branch$act1
                                      round-robin2$q5-inputs
                                      round-robin2$br-inputs)))))

(local
 (defthm booleanp-round-robin2$q5-out-act
   (b* ((q4 (nth *round-robin2$q4* st))
        (q5 (nth *round-robin2$q5* st))
        (me (nth *round-robin2$me* st))
        
        (lmux (nth *alt-merge$lmux* me))
        (mux (nth *alt-merge$mux* me))
        (lmux-buf (nth *alt-merge$lmux-buf* me)))
     
     (implies (and (booleanp (nth 1 inputs))
                   (queue4$valid-st q4)
                   (queue5$valid-st q5)
                   (equal lmux '(t))
                   (equal (car mux) t)
                   (equal lmux-buf '(nil)))
              (booleanp (queue5$out-act
                         (round-robin2$q5-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      queue5$out-act
                                      alt-merge$act1
                                      round-robin2$q5-inputs
                                      round-robin2$me-inputs)))
   :rule-classes :type-prescription))

(local
 (defthm round-robin2$rewrite-to-q5-out-act-1
   (b* ((q4 (nth *round-robin2$q4* st))
        (q5 (nth *round-robin2$q5* st))
        (me (nth *round-robin2$me* st))
        
        (lmux (nth *alt-merge$lmux* me))
        (mux (nth *alt-merge$mux* me))
        (lmux-buf (nth *alt-merge$lmux-buf* me)))
     
     (implies (and (booleanp (nth 1 inputs))
                   (queue4$valid-st q4)
                   (queue5$valid-st q5)
                   (equal lmux '(t))
                   (equal (car mux) t)
                   (equal lmux-buf '(nil)))
              (equal (joint-act (queue5$ready-out q5)
                                (nth 1 inputs)
                                (nth 0 (nthcdr (+ *round-robin2$data-ins-len*
                                                  *queue4$go-num*
                                                  *queue5$go-num*
                                                  *alt-branch$go-num*)
                                               inputs)))
                     (queue5$out-act
                      (round-robin2$q5-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      queue5$out-act
                                      alt-merge$act1
                                      round-robin2$q5-inputs
                                      round-robin2$me-inputs)))))

(local
 (defthm round-robin2$rewrite-to-q5-out-act-2
   (b* ((q4 (nth *round-robin2$q4* st))
        (q5 (nth *round-robin2$q5* st))
        (me (nth *round-robin2$me* st))
        
        (lmux (nth *alt-merge$lmux* me))
        (mux (nth *alt-merge$mux* me))
        (lmux-buf (nth *alt-merge$lmux-buf* me)))
     
     (implies (and (booleanp (nth 1 inputs))
                   (queue4$valid-st q4)
                   (queue5$valid-st q5)
                   (equal lmux '(t))
                   (queue5$ready-out q5)
                   (equal lmux-buf '(nil)))
              (equal (joint-act (car mux)
                                (nth 1 inputs)
                                (nth 0 (nthcdr (+ *round-robin2$data-ins-len*
                                                  *queue4$go-num*
                                                  *queue5$go-num*
                                                  *alt-branch$go-num*)
                                               inputs)))
                     (queue5$out-act
                      (round-robin2$q5-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      f-and3
                                      queue5$out-act
                                      alt-merge$act1
                                      round-robin2$q5-inputs
                                      round-robin2$me-inputs)))))

(local
 (defthm round-robin2$rewrite-to-q5-out-act-3
   (b* ((q4 (nth *round-robin2$q4* st))
        (q5 (nth *round-robin2$q5* st))
        (me (nth *round-robin2$me* st))
        
        (lmux (nth *alt-merge$lmux* me))
        (mux (nth *alt-merge$mux* me))
        (lmux-buf (nth *alt-merge$lmux-buf* me)))
     
     (implies (and (booleanp (nth 1 inputs))
                   (queue4$valid-st q4)
                   (queue5$valid-st q5)
                   (equal lmux '(t))
                   (queue5$ready-out q5)
                   (equal (car mux) t)
                   (equal lmux-buf '(nil)))
              (equal (joint-act t
                                (nth 1 inputs)
                                (nth 0 (nthcdr (+ *round-robin2$data-ins-len*
                                                  *queue4$go-num*
                                                  *queue5$go-num*
                                                  *alt-branch$go-num*)
                                               inputs)))
                     (queue5$out-act
                      (round-robin2$q5-inputs inputs st)))))
   :hints (("Goal" :in-theory (enable get-field
                                      f-and3
                                      queue5$out-act
                                      alt-merge$act1
                                      round-robin2$q5-inputs
                                      round-robin2$me-inputs)))))

(defthm round-robin2$inv-preserved
  (implies (and (round-robin2$input-format inputs)
                (round-robin2$valid-st st)
                (round-robin2$inv st))
           (round-robin2$inv (round-robin2$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            queue4$step-spec
                            queue5$step-spec
                            round-robin2$input-format
                            round-robin2$valid-st
                            round-robin2$inv
                            round-robin2$state-fn
                            round-robin2$in-act
                            round-robin2$out-act
                            round-robin2$br-inputs
                            round-robin2$me-inputs
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

(defun round-robin2$in-seq (inputs-lst st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (round-robin2$in-act inputs st) t)
          (append (round-robin2$in-seq (cdr inputs-lst)
                                      (round-robin2$state-fn inputs st)
                                      (1- n))
                  (list (pairlis$ (round-robin2$get-data-in inputs)
                                  nil)))
        (round-robin2$in-seq (cdr inputs-lst)
                            (round-robin2$state-fn inputs st)
                            (1- n))))))

(defun round-robin2$out-seq (inputs-lst st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst))
         (extracted-st (round-robin2$extract-state st)))
      (if (equal (round-robin2$out-act inputs st) t)
          (append (round-robin2$out-seq (cdr inputs-lst)
                                       (round-robin2$state-fn inputs st)
                                       (1- n))
                  (list (nth (1- (len extracted-st))
                             extracted-st)))
        (round-robin2$out-seq (cdr inputs-lst)
                             (round-robin2$state-fn inputs st)
                             (1- n))))))

(defund round-robin2$in-out-seq-sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *round-robin2$ins-len*)
       ((mv inputs-lst state)
        (go-vals-gen num-signals n state nil))
       (full '(t))
       (empty '(nil))
       (invalid-data (make-list *data-width* :initial-element '(x)))
       (q4 (list empty invalid-data
                 empty invalid-data
                 empty invalid-data
                 empty invalid-data))
       (q5 (list empty invalid-data
                 empty invalid-data
                 empty invalid-data
                 empty invalid-data
                 empty invalid-data))
       (br (list full '(nil)
                 empty '(x)))
       (me (list full '(nil)
                 empty '(x)))
       (st (list q4 q5 br me)))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-flatten-lst
                   (round-robin2$in-seq inputs-lst st n))))
      (list (cons 'out-seq
                  (v-to-nat-flatten-lst
                   (round-robin2$out-seq inputs-lst st n)))))
     state)))

(defund round-robin2$step-spec (inputs st)
  (b* ((data-in (round-robin2$get-data-in inputs))
       (extracted-st (round-robin2$extract-state st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (round-robin2$out-act inputs st) t)
      (cond
       ((equal (round-robin2$in-act inputs st) t)
        (cons (pairlis$ data-in nil)
              (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (round-robin2$in-act inputs st) t)
          (cons (pairlis$ data-in nil)
                extracted-st))
         (t extracted-st))))))

(encapsulate
  ()

  (local
   (defthm round-robin2$q4-and-q5-get-data-in-rewrite
     (implies (bvp (round-robin2$get-data-in inputs))
              (and (equal (queue4$get-data-in
                           (round-robin2$q4-inputs inputs st))
                          (round-robin2$get-data-in inputs))
                   (equal (queue5$get-data-in
                           (round-robin2$q5-inputs inputs st))
                          (round-robin2$get-data-in inputs))))
     :hints (("Goal"
              :in-theory (enable queue4$get-data-in
                                 queue5$get-data-in
                                 round-robin2$q4-inputs
                                 round-robin2$q5-inputs)))))

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

  (defthm round-robin2$step-spec-correct
    (b* ((next-st (round-robin2$state-fn inputs st)))
      (implies (and (round-robin2$input-format inputs)
                    (round-robin2$valid-st st)
                    (round-robin2$inv st))
               (equal (round-robin2$extract-state next-st)
                      (round-robin2$step-spec inputs st))))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              queue4$step-spec
                              queue5$step-spec
                              round-robin2$step-spec
                              round-robin2$input-format
                              round-robin2$valid-st
                              round-robin2$inv
                              round-robin2$state-fn
                              round-robin2$in-act
                              round-robin2$out-act
                              round-robin2$extract-state
                              round-robin2$br-inputs
                              round-robin2$me-inputs
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
   (defthm consp-queue4$extract-state-alt
     (implies (and (queue4$valid-st st)
                   (queue4$ready-out st))
              (consp (queue4$extract-state st)))
     :hints (("Goal" :in-theory (enable queue4$valid-st
                                        queue4$ready-out
                                        queue4$extract-state)))
     :rule-classes :type-prescription))

  (local
   (defthm consp-queue5$extract-state-alt
     (implies (and (queue5$valid-st st)
                   (queue5$ready-out st))
              (consp (queue5$extract-state st)))
     :hints (("Goal" :in-theory (enable queue5$valid-st
                                        queue5$ready-out
                                        queue5$extract-state)))
     :rule-classes :type-prescription))

  (defthm consp-round-robin2$extract-state
    (implies (and (round-robin2$input-format inputs)
                  (round-robin2$valid-st st)
                  (round-robin2$out-act inputs st))
             (consp (round-robin2$extract-state st)))
    :hints (("Goal"
             :in-theory (enable joint-act
                                round-robin2$input-format
                                round-robin2$valid-st
                                round-robin2$extract-state
                                round-robin2$out-act
                                round-robin2$me-inputs
                                alt-merge$valid-st
                                alt-merge$act
                                alt-merge$act0
                                alt-merge$act1)))
    :rule-classes :type-prescription)
  )

;; (encapsulate
;;   ()

;;   (local
;;    (defthm round-robin2$q4-data-out-rewrite
;;      (b* ((q4 (nth *round-robin2$q4* st))
;;           (me (nth *round-robin2$me* st)))
;;        (implies (and (queue4$valid-st q4)
;;                      (alt-merge$valid-st me)
;;                      (equal n (1- (len (queue4$extract-state q4))))
;;                      (queue4$out-act (round-robin2$q4-inputs inputs st)))
;;                 (equal (pairlis$ (queue4$data-out q4)
;;                                  nil)
;;                        (nth n (queue4$extract-state q4)))))
;;      :hints (("Goal" :in-theory (e/d (get-field
;;                                       f-if
;;                                       queue4$valid-st
;;                                       queue4$out-act
;;                                       queue4$ready-out
;;                                       queue4$data-out
;;                                       queue4$extract-state
;;                                       alt-merge$valid-st
;;                                       alt-merge$act
;;                                       alt-merge$act0
;;                                       round-robin2$q4-inputs
;;                                       round-robin2$me-inputs)
;;                                      (nth))))))

;;   (local
;;    (defthm round-robin2$q5-data-out-rewrite
;;      (b* ((q5 (nth *round-robin2$q5* st))
;;           (me (nth *round-robin2$me* st)))
;;        (implies (and (queue5$valid-st q5)
;;                      (alt-merge$valid-st me)
;;                      (equal n (1- (len (queue5$extract-state q5))))
;;                      (queue5$out-act (round-robin2$q5-inputs inputs st)))
;;                 (equal (pairlis$ (queue5$data-out q5)
;;                                  nil)
;;                        (nth n (queue5$extract-state q5)))))
;;      :hints (("Goal" :in-theory (e/d (get-field
;;                                       f-if
;;                                       queue5$valid-st
;;                                       queue5$out-act
;;                                       queue5$ready-out
;;                                       queue5$data-out
;;                                       queue5$extract-state
;;                                       alt-merge$valid-st
;;                                       alt-merge$act
;;                                       alt-merge$act1
;;                                       round-robin2$q5-inputs
;;                                       round-robin2$me-inputs)
;;                                      (nth))))))

;;   (local
;;    (defthmd nth-interleave-1
;;      (implies (and (equal (len l1) (len l2))
;;                    (natp m)
;;                    (< m (len l2)))
;;               (equal (nth m l2)
;;                      (nth (+ 1 m m) (interleave l1 l2))))))

;;   (local
;;    (defthmd nth-interleave-2
;;      (implies (and (equal (len l1) (1+ (len l2)))
;;                    (natp m)
;;                    (< m (len l1)))
;;               (equal (nth m l1)
;;                      (nth (+ m m) (interleave l1 l2))))))

;;   (local
;;    (defthm len-0-is-atom
;;      (equal (equal (len x) 0)
;;             (atom x))))

;;   (local
;;    (defthm nth-interleave-1-instance-1
;;      (implies (and (equal (len l1)
;;                           (len (queue4$extract-state st)))
;;                    (equal m (1- (len (queue4$extract-state st))))
;;                    (equal n (+ -1
;;                                (len l1)
;;                                (len (queue4$extract-state st)))))
;;               (equal (nth m (queue4$extract-state st))
;;                      (nth n (interleave l1 (queue4$extract-state st)))))
;;      :hints (("Goal" :use (:instance nth-interleave-1
;;                                      (l2 (queue4$extract-state st)))))))

;;   (local
;;    (defthm nth-interleave-1-instance-2
;;      (implies (and (equal (len l1)
;;                           (len (queue5$extract-state st)))
;;                    (equal m (1- (len (queue5$extract-state st))))
;;                    (equal n (+ -1
;;                                (len l1)
;;                                (len (queue5$extract-state st)))))
;;               (equal (nth m (queue5$extract-state st))
;;                      (nth n (interleave l1 (queue5$extract-state st)))))
;;      :hints (("Goal" :use (:instance nth-interleave-1
;;                                      (l2 (queue5$extract-state st)))))))

;;   (local
;;    (defthm nth-interleave-2-instance-1
;;      (implies (and (equal (len (queue4$extract-state st))
;;                           (1+ (len l2)))
;;                    (equal m (1- (len (queue4$extract-state st))))
;;                    (equal n (+ -1
;;                                (len (queue4$extract-state st))
;;                                (len l2))))
;;               (equal (nth m (queue4$extract-state st))
;;                      (nth n (interleave (queue4$extract-state st)
;;                                          l2))))
;;      :hints (("Goal" :use (:instance nth-interleave-2
;;                                      (l1 (queue4$extract-state st)))))))

;;   (local
;;    (defthm nth-interleave-2-instance-2
;;      (implies (and (equal (len (queue5$extract-state st))
;;                           (1+ (len l2)))
;;                    (equal m (1- (len (queue5$extract-state st))))
;;                    (equal n (+ -1
;;                                (len (queue5$extract-state st))
;;                                (len l2))))
;;               (equal (nth m (queue5$extract-state st))
;;                      (nth n (interleave (queue5$extract-state st)
;;                                          l2))))
;;      :hints (("Goal" :use (:instance nth-interleave-2
;;                                      (l1 (queue5$extract-state st)))))))

;;   (defthm round-robin2$extract-state-lemma
;;     (implies (and (round-robin2$input-format inputs)
;;                   (round-robin2$valid-st st)
;;                   (round-robin2$inv st)
;;                   (equal n (1- (len (round-robin2$extract-state st))))
;;                   (round-robin2$out-act inputs st))
;;              (equal (append
;;                      (take n (round-robin2$extract-state st))
;;                      (list (pairlis$ (round-robin2$data-out st) nil)))
;;                     (round-robin2$extract-state st)))
;;     :hints (("Goal"
;;              :in-theory (e/d (get-field
;;                               round-robin2$input-format
;;                               round-robin2$valid-st
;;                               round-robin2$inv
;;                               round-robin2$extract-state
;;                               round-robin2$out-act
;;                               round-robin2$data-out
;;                               round-robin2$me-inputs
;;                               alt-merge$valid-st
;;                               alt-merge$act
;;                               alt-merge$act0
;;                               alt-merge$act1)
;;                              (nfix
;;                               nth
;;                               nthcdr
;;                               len-nthcdr
;;                               if*
;;                               append
;;                               pairlis$
;;                               strip-cars
;;                               take-of-len-is-itself
;;                               default-car
;;                               default-cdr
;;                               default-+-1
;;                               default-+-2)))))
;;   )

(encapsulate
  ()

  (local
   (defthm round-robin2$dataflow-correct-aux
     (implies (equal (append x1 y1)
                     (append (round-robin2$in-seq inputs-lst st n) y2))
              (equal (append x1 y1 z)
                     (append (round-robin2$in-seq inputs-lst st n) y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (acl2::associativity-of-append))))))

  (defthmd round-robin2$dataflow-correct
    (b* ((extracted-st (round-robin2$extract-state st))
         (final-st (round-robin2$state-fn-n inputs-lst st n))
         (final-extracted-st (round-robin2$extract-state final-st)))
      (implies (and (round-robin2$input-format-n inputs-lst n)
                    (round-robin2$valid-st st)
                    (round-robin2$inv st))
               (equal (append final-extracted-st
                              (round-robin2$out-seq inputs-lst st n))
                      (append (round-robin2$in-seq inputs-lst st n)
                              extracted-st))))
    :hints (("Goal"
             :in-theory (e/d (round-robin2$step-spec)
                             ()))))
  )

