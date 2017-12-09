;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; December 2017

(in-package "ADE")

(include-book "alt-branch")
(include-book "alt-merge")
(include-book "store-n")

(local (in-theory (e/d (f-buf-delete-lemmas-1
                        f-buf-delete-lemmas-2)
                       (nth-of-bvp-is-booleanp
                        take-of-len-free))))

;; ======================================================================

(defconst *wigwag$data-ins-len* (+ 2 *data-width*))
(defconst *wigwag$go-num* (+ *alt-branch$go-num*
                             *alt-merge$go-num*))
(defconst *wigwag$ins-len* (+ *wigwag$data-ins-len*
                             *wigwag$go-num*))
(defconst *wigwag$st-len* 6)

;; A 2-data-link wigwag module:
;;
;;   -> L0 -
;;  |       |
;; -BR      ME->
;;  |       |
;;   -> L1 -

(module-generator
 wigwag* ()
 'wigwag
 (list* 'full-in 'full-out- (append (sis 'data-in 0 *data-width*)
                                    (sis 'go 0 *wigwag$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 *data-width*))
 '(l0 d0 l1 d1 br me)
 (list
  ;; LINKS
  ;; L0
  '(l0 (l0-status) link-cntl (br-act0 me-act0))
  (list 'd0
        (sis 'd0-out 0 *data-width*)
        (si 'latch-n *data-width*)
        (list* 'br-act0 (sis 'data 0 *data-width*)))

  ;; L1
  '(l1 (l1-status) link-cntl (br-act1 me-act1))
  (list 'd1
        (sis 'd1-out 0 *data-width*)
        (si 'latch-n *data-width*)
        (list* 'br-act1 (sis 'data 0 *data-width*)))

  ;; JOINTS
  ;; Alt-Branch
  (list 'br
        (list* 'in-act 'br-act0 'br-act1
               (sis 'data 0 *data-width*))
        'alt-branch
        (list* 'full-in 'l0-status 'l1-status
               (append (sis 'data-in 0 *data-width*)
                       (sis 'go 0 *alt-branch$go-num*))))

  ;; Alt-Merge
  (list 'me
        (list* 'out-act 'me-act0 'me-act1
               (sis 'data-out 0 *data-width*))
        'alt-merge
        (list* 'l0-status 'l1-status 'full-out-
               (append (sis 'd0-out 0 *data-width*)
                       (sis 'd1-out 0 *data-width*)
                       (sis 'go *alt-branch$go-num* *alt-merge$go-num*)))))

 :guard t)

(defun wigwag$netlist ()
  (declare (xargs :guard t))
  (cons (wigwag*)
        (union$ (alt-branch$netlist)
                (alt-merge$netlist)
                (latch-n$netlist *data-width*)
                :test 'equal)))

(defthmd wigwag$netlist-okp
  (and (net-syntax-okp (wigwag$netlist))
       (net-arity-okp (wigwag$netlist))))

(defund wigwag& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (and (equal (assoc 'wigwag netlist)
              (wigwag*))
       (b* ((netlist (delete-to-eq 'wigwag netlist)))
         (and (alt-branch& netlist)
              (alt-merge& netlist)
              (latch-n& netlist *data-width*)))))

(defthm check-wigwag$netlist
  (wigwag& (wigwag$netlist)))

(defconst *wigwag$l0* 0)
(defconst *wigwag$d0* 1)
(defconst *wigwag$l1* 2)
(defconst *wigwag$d1* 3)
(defconst *wigwag$br* 4)
(defconst *wigwag$me* 5)

(defund wigwag$valid-st (st)
  (b* ((l0 (get-field *wigwag$l0* st))
       (d0 (get-field *wigwag$d0* st))
       (l1 (get-field *wigwag$l1* st))
       (d1 (get-field *wigwag$d1* st))
       (br (get-field *wigwag$br* st))
       (me (get-field *wigwag$me* st)))
    (and (validp l0)
         (len-1-true-listp d0)
         (bvp (strip-cars d0))
         (equal (len d0) *data-width*)
         
         (validp l1)
         (len-1-true-listp d1)
         (bvp (strip-cars d1))
         (equal (len d1) *data-width*)

         (alt-branch$valid-st br)
         (alt-merge$valid-st me))))

(defun wigwag$map-to-links (st)
  (b* ((l0 (get-field *wigwag$l0* st))
       (d0 (get-field *wigwag$d0* st))
       (l1 (get-field *wigwag$l1* st))
       (d1 (get-field *wigwag$d1* st))
       (br (get-field *wigwag$br* st))
       (me (get-field *wigwag$me* st)))
    (append (list (cons 'alt-branch (alt-branch$map-to-links br)))
            (map-to-links (list (list 'l0 l0 d0)
                                (list 'l1 l1 d1)))
            (list (cons 'alt-merge (alt-merge$map-to-links me))))))

(defun wigwag$map-to-links-list (x)
  (if (atom x)
      nil
    (cons (wigwag$map-to-links (car x))
          (wigwag$map-to-links-list (cdr x)))))

(defund wigwag$sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *wigwag$ins-len*)
       ((mv inputs-lst state) (go-vals-gen num-signals n state nil))
       ;;(- (cw "~x0~%" inputs-lst))
       (full '(t))
       (empty '(nil))
       (invalid-data (make-list *data-width* :initial-element '(x)))
       (br (list full '(nil)
                 empty '(x)))
       (me (list full '(nil)
                 empty '(x)))
       (st (list empty invalid-data
                 empty invalid-data
                 br me)))
    (mv (pretty-list
         (remove-dup-neighbors
          (wigwag$map-to-links-list
           (de-sim-list 'wigwag inputs-lst st (wigwag$netlist))))
         0)
        state)))

(defun wigwag$get-data-in (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (subseq-list inputs 2 (+ 2 *data-width*)))

(defthm len-wigwag$get-data-in
  (equal (len (wigwag$get-data-in inputs))
         *data-width*))

(in-theory (disable wigwag$get-data-in))

(defund wigwag$br-inputs (inputs st)
  (b* ((full-in (nth 0 inputs))
       (data-in (wigwag$get-data-in inputs))
       (go-signals (nthcdr *wigwag$data-ins-len* inputs))

       (br-go-signals (take *alt-branch$go-num* go-signals))

       (l0 (get-field *wigwag$l0* st))
       (l1 (get-field *wigwag$l1* st)))

    (list* full-in (f-buf (car l0)) (f-buf (car l1))
           (append data-in br-go-signals))))

(defund wigwag$me-inputs (inputs st)
  (b* ((full-out- (nth 1 inputs))
       (go-signals (nthcdr *wigwag$data-ins-len* inputs))

       (me-go-signals (nthcdr *alt-branch$go-num* go-signals))

       (l0 (get-field *wigwag$l0* st))
       (d0 (get-field *wigwag$d0* st))
       (l1 (get-field *wigwag$l1* st))
       (d1 (get-field *wigwag$d1* st)))

    (list* (f-buf (car l0)) (f-buf (car l1)) full-out-
           (append (v-threefix (strip-cars d0))
                   (v-threefix (strip-cars d1))
                   me-go-signals))))

(defund wigwag$in-act (inputs st)
  (b* ((br-inputs (wigwag$br-inputs inputs st))
       (br (get-field *wigwag$br* st)))
    (alt-branch$act br-inputs br)))

(defund wigwag$out-act (inputs st)
  (b* ((me-inputs (wigwag$me-inputs inputs st))
       (me (get-field *wigwag$me* st)))
    (alt-merge$act me-inputs me)))

(defund wigwag$data-out (st)
  (b* ((d0 (get-field *wigwag$d0* st))
       (d1 (get-field *wigwag$d1* st))
       (me (get-field *wigwag$me* st))
       
       (mux (get-field *alt-merge$mux* me)))
    (fv-if (car mux)
           (strip-cars d1)
           (strip-cars d0))))

(defthm wigwag$data-out-props
   (implies (wigwag$valid-st st)
            (and (bvp (wigwag$data-out st))
                 (equal (len (wigwag$data-out st))
                        *data-width*)))
   :hints (("Goal" :in-theory (enable wigwag$valid-st
                                      wigwag$data-out
                                      alt-merge$valid-st))))

(defthmd wigwag$value
  (b* ((inputs (list* full-in full-out- (append data-in go-signals))))
    (implies (and (wigwag& netlist)
                  (true-listp data-in)
                  (equal (len data-in) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *wigwag$go-num*)
                  (wigwag$valid-st st))
             (equal (se 'wigwag inputs st netlist)
                    (list* (wigwag$in-act inputs st)
                           (wigwag$out-act inputs st)
                           (wigwag$data-out st)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (se-rules
                            get-field
                            open-nth
                            len-1-true-listp=>true-listp
                            wigwag&
                            wigwag*$destructure
                            wigwag$get-data-in
                            alt-branch$value
                            alt-merge$value
                            latch-n$value
                            wigwag$valid-st
                            wigwag$in-act
                            wigwag$out-act
                            wigwag$data-out
                            wigwag$br-inputs
                            wigwag$me-inputs)
                           ((wigwag*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(defun wigwag$state-fn (inputs st)
  (b* ((data-in (wigwag$get-data-in inputs))
       
       (l0 (get-field *wigwag$l0* st))
       (d0 (get-field *wigwag$d0* st))
       (l1 (get-field *wigwag$l1* st))
       (d1 (get-field *wigwag$d1* st))
       (br (get-field *wigwag$br* st))
       (me (get-field *wigwag$me* st))

       (br-inputs (wigwag$br-inputs inputs st))
       (me-inputs (wigwag$me-inputs inputs st))

       (br-act0 (alt-branch$act0 br-inputs br))
       (br-act1 (alt-branch$act1 br-inputs br))
       (me-act0 (alt-merge$act0 me-inputs me))
       (me-act1 (alt-merge$act1 me-inputs me)))
    (list
     (list (f-sr br-act0 me-act0 (car l0)))
     (pairlis$ (fv-if br-act0 data-in (strip-cars d0))
               nil)
     
     (list (f-sr br-act1 me-act1 (car l1)))
     (pairlis$ (fv-if br-act1 data-in (strip-cars d1))
               nil)

     (alt-branch$state-fn br-inputs br)
     (alt-merge$state-fn me-inputs me))))

(defthm len-of-wigwag$state-fn
  (equal (len (wigwag$state-fn inputs st))
         *wigwag$st-len*))

(defthmd wigwag$state
  (b* ((inputs (list* full-in full-out- (append data-in go-signals))))
    (implies (and (wigwag& netlist)
                  (true-listp data-in)
                  (equal (len data-in) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *wigwag$go-num*)
                  (wigwag$valid-st st))
             (equal (de 'wigwag inputs st netlist)
                    (wigwag$state-fn inputs st))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (de-rules
                            get-field
                            open-nth
                            len-1-true-listp=>true-listp
                            wigwag&
                            wigwag*$destructure
                            wigwag$valid-st
                            wigwag$get-data-in
                            wigwag$br-inputs
                            wigwag$me-inputs
                            alt-branch$value alt-branch$state
                            alt-merge$value alt-merge$state
                            latch-n$value latch-n$state)
                           ((wigwag*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(in-theory (disable wigwag$state-fn))

;; ======================================================================

(defund wigwag$input-format (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((full-in    (nth 0 inputs))
       (full-out-  (nth 1 inputs))
       (data-in    (wigwag$get-data-in inputs))
       (go-signals (nthcdr *wigwag$data-ins-len* inputs)))
    (and
     (booleanp full-in)
     (booleanp full-out-)
     (bvp data-in)
     (true-listp go-signals)
     (= (len go-signals) *wigwag$go-num*)
     (equal inputs
            (list* full-in full-out- (append data-in go-signals))))))

(defthmd len-of-wigwag$inputs
  (implies (wigwag$input-format inputs)
           (equal (len inputs) *wigwag$ins-len*))
  :hints (("Goal" :in-theory (enable wigwag$input-format))))

(local
 (defthm wigwag$input-format=>br$input-format
   (implies (and (wigwag$input-format inputs)
                 (wigwag$valid-st st))
            (alt-branch$input-format
             (wigwag$br-inputs inputs st)))
   :hints (("Goal"
            :in-theory (e/d (wigwag$input-format
                             alt-branch$input-format
                             alt-branch$get-data-in
                             wigwag$valid-st
                             wigwag$br-inputs)
                            (nth
                             nthcdr
                             take-of-too-many
                             take-of-len-is-itself))))))

(local
 (defthm wigwag$input-format=>me$input-format
   (implies (and (wigwag$input-format inputs)
                 (wigwag$valid-st st))
            (alt-merge$input-format
             (wigwag$me-inputs inputs st)))
   :hints (("Goal"
            :in-theory (e/d (len-of-wigwag$inputs
                             wigwag$input-format
                             alt-merge$input-format
                             alt-merge$get-data-in0
                             alt-merge$get-data-in1
                             wigwag$valid-st
                             wigwag$me-inputs)
                            (nth
                             nthcdr
                             take-of-too-many
                             take-of-len-is-itself))))))

(local
 (defthm booleanp-wigwag$br-act0
   (implies (and (booleanp (nth 0 inputs))
                 (or (equal (nth *wigwag$l0* st) '(t))
                     (equal (nth *wigwag$l0* st) '(nil)))
                 (or (equal (nth *wigwag$l1* st) '(t))
                     (equal (nth *wigwag$l1* st) '(nil)))
                 (alt-branch$valid-st (nth *wigwag$br* st)))
            (booleanp (alt-branch$act0 (wigwag$br-inputs inputs st)
                                   (nth *wigwag$br* st))))
   :hints (("Goal" :in-theory (enable get-field
                                      wigwag$br-inputs
                                      alt-branch$valid-st
                                      alt-branch$act0
                                      alt-branch$act)))
   :rule-classes :type-prescription))

(local
 (defthm booleanp-wigwag$br-act1
   (implies (and (booleanp (nth 0 inputs))
                 (or (equal (nth *wigwag$l0* st) '(t))
                     (equal (nth *wigwag$l0* st) '(nil)))
                 (or (equal (nth *wigwag$l1* st) '(t))
                     (equal (nth *wigwag$l1* st) '(nil)))
                 (alt-branch$valid-st (nth *wigwag$br* st)))
            (booleanp (alt-branch$act1 (wigwag$br-inputs inputs st)
                                   (nth *wigwag$br* st))))
   :hints (("Goal" :in-theory (enable get-field
                                      wigwag$br-inputs
                                      alt-branch$valid-st
                                      alt-branch$act1
                                      alt-branch$act)))
   :rule-classes :type-prescription))

(local
 (defthm booleanp-wigwag$me-act0
   (implies (and (booleanp (nth 1 inputs))
                 (or (equal (nth *wigwag$l0* st) '(t))
                     (equal (nth *wigwag$l0* st) '(nil)))
                 (or (equal (nth *wigwag$l1* st) '(t))
                     (equal (nth *wigwag$l1* st) '(nil)))
                 (alt-merge$valid-st (nth *wigwag$me* st)))
            (booleanp (alt-merge$act0 (wigwag$me-inputs inputs st)
                                  (nth *wigwag$me* st))))
   :hints (("Goal" :in-theory (enable get-field
                                      wigwag$me-inputs
                                      alt-merge$valid-st
                                      alt-merge$act0
                                      alt-merge$act)))
   :rule-classes :type-prescription))

(local
 (defthm booleanp-wigwag$me-act1
   (implies (and (booleanp (nth 1 inputs))
                 (or (equal (nth *wigwag$l0* st) '(t))
                     (equal (nth *wigwag$l0* st) '(nil)))
                 (or (equal (nth *wigwag$l1* st) '(t))
                     (equal (nth *wigwag$l1* st) '(nil)))
                 (alt-merge$valid-st (nth *wigwag$me* st)))
            (booleanp (alt-merge$act1 (wigwag$me-inputs inputs st)
                                  (nth *wigwag$me* st))))
   :hints (("Goal" :in-theory (enable get-field
                                      wigwag$me-inputs
                                      alt-merge$valid-st
                                      alt-merge$act1
                                      alt-merge$act)))
   :rule-classes :type-prescription))

(local
 (defthm wigwag$br-act0-nil
   (implies (and (equal (nth *wigwag$l0* st) '(t))
                 (alt-branch$valid-st (nth *wigwag$br* st)))
            (not (alt-branch$act0 (wigwag$br-inputs inputs st)
                              (nth *wigwag$br* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               f-if
                               wigwag$br-inputs
                               alt-branch$valid-st
                               alt-branch$act0
                               alt-branch$act)))))

(local
 (defthm wigwag$br-act1-nil
   (implies (and (equal (nth *wigwag$l1* st) '(t))
                 (alt-branch$valid-st (nth *wigwag$br* st)))
            (not (alt-branch$act1 (wigwag$br-inputs inputs st)
                              (nth *wigwag$br* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               f-if
                               wigwag$br-inputs
                               alt-branch$valid-st
                               alt-branch$act1
                               alt-branch$act)))))

(local
 (defthm wigwag$me-act0-nil
   (implies (and (equal (nth *wigwag$l0* st) '(nil))
                 (alt-merge$valid-st (nth *wigwag$me* st)))
            (not (alt-merge$act0 (wigwag$me-inputs inputs st)
                             (nth *wigwag$me* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               f-if
                               wigwag$me-inputs
                               alt-merge$valid-st
                               alt-merge$act0
                               alt-merge$act)))))

(local
 (defthm wigwag$me-act1-nil
   (implies (and (equal (nth *wigwag$l1* st) '(nil))
                 (alt-merge$valid-st (nth *wigwag$me* st)))
            (not (alt-merge$act1 (wigwag$me-inputs inputs st)
                             (nth *wigwag$me* st))))
   :hints (("Goal"
            :in-theory (enable get-field
                               f-if
                               wigwag$me-inputs
                               alt-merge$valid-st
                               alt-merge$act1
                               alt-merge$act)))))

(defthm wigwag$valid-st-preserved
  (implies (and (wigwag$input-format inputs)
                (wigwag$valid-st st))
           (wigwag$valid-st (wigwag$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            wigwag$input-format
                            wigwag$valid-st
                            wigwag$state-fn
                            wigwag$in-act
                            wigwag$out-act
                            f-sr)
                           (if*
                            nth
                            nthcdr
                            acl2::true-listp-append)))))

(defthmd wigwag$state-alt
  (implies (and (wigwag& netlist)
                (wigwag$input-format inputs)
                (wigwag$valid-st st))
           (equal (de 'wigwag inputs st netlist)
                  (wigwag$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (enable wigwag$input-format)
           :use (:instance wigwag$state
                           (full-in    (nth 0 inputs))
                           (full-out-  (nth 1 inputs))
                           (data-in    (wigwag$get-data-in inputs))
                           (go-signals (nthcdr *wigwag$data-ins-len*
                                               inputs))))))

(state-fn-n-gen wigwag)

(input-format-n-gen wigwag)

(defthmd de-sim-n$wigwag
  (implies (and (wigwag& netlist)
                (wigwag$input-format-n inputs-lst n)
                (wigwag$valid-st st))
           (equal (de-sim-n 'wigwag inputs-lst st netlist n)
                  (wigwag$state-fn-n inputs-lst st n)))
  :hints (("Goal" :in-theory (enable wigwag$state-alt))))

;; ======================================================================

(defund wigwag$extract-state (st)
  (b* ((l0 (get-field *wigwag$l0* st))
       (d0 (get-field *wigwag$d0* st))
       (l1 (get-field *wigwag$l1* st))
       (d1 (get-field *wigwag$d1* st))
       (me (get-field *wigwag$me* st))

       (lmux    (get-field *alt-merge$lmux* me))
       (mux     (get-field *alt-merge$mux* me))
       (mux-buf (get-field *alt-merge$mux-buf* me))
       (me-select (if (fullp lmux) (car mux) (car mux-buf))))
    
    (if me-select
        (extract-state (list l0 d0 l1 d1))
      (extract-state (list l1 d1 l0 d0)))))

(defund wigwag$inv (st)
  (b* ((l0 (get-field *wigwag$l0* st))
       (l1 (get-field *wigwag$l1* st))
       (br (get-field *wigwag$br* st))
       (me (get-field *wigwag$me* st))

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
         (or (and (equal l0 l1)
                  (equal br-select me-select))
             (and (fullp l0)
                  (emptyp l1)
                  br-select
                  (not me-select))
             (and (emptyp l0)
                  (fullp l1)
                  (not br-select)
                  me-select)))))

(defthm wigwag$inv-preserved
  (implies (and (wigwag$input-format inputs)
                (wigwag$valid-st st)
                (wigwag$inv st))
           (wigwag$inv (wigwag$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            wigwag$input-format
                            wigwag$valid-st
                            wigwag$inv
                            wigwag$state-fn
                            wigwag$in-act
                            wigwag$out-act
                            wigwag$br-inputs
                            wigwag$me-inputs
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
                           (nth
                            nthcdr
                            len
                            true-listp
                            take-of-too-many
                            take-of-len-is-itself
                            open-v-threefix)))))

(defun wigwag$in-seq (inputs-lst st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (wigwag$in-act inputs st) t)
          (append (wigwag$in-seq (cdr inputs-lst)
                                 (wigwag$state-fn inputs st)
                                 (1- n))
                  (list (pairlis$ (wigwag$get-data-in inputs)
                                  nil)))
        (wigwag$in-seq (cdr inputs-lst)
                       (wigwag$state-fn inputs st)
                       (1- n))))))

(defun wigwag$out-seq (inputs-lst st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst))
         (extracted-st (wigwag$extract-state st)))
      (if (equal (wigwag$out-act inputs st) t)
          (append (wigwag$out-seq (cdr inputs-lst)
                                  (wigwag$state-fn inputs st)
                                  (1- n))
                  (list (nth (1- (len extracted-st))
                             extracted-st)))
        (wigwag$out-seq (cdr inputs-lst)
                        (wigwag$state-fn inputs st)
                        (1- n))))))

(defund wigwag$in-out-seq-sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *wigwag$ins-len*)
       ((mv inputs-lst state)
        (go-vals-gen num-signals n state nil))
       (full '(t))
       (empty '(nil))
       (invalid-data (make-list *data-width* :initial-element '(x)))
       (br (list full '(nil)
                 empty '(x)))
       (me (list full '(nil)
                 empty '(x)))
       (st (list empty invalid-data
                 empty invalid-data
                 br me)))
    (mv
     (append
      (list (cons 'in-seq
                  (v-to-nat-flatten-lst
                   (wigwag$in-seq inputs-lst st n))))
      (list (cons 'out-seq
                  (v-to-nat-flatten-lst
                   (wigwag$out-seq inputs-lst st n)))))
     state)))

(defund wigwag$step-spec (inputs st)
  (b* ((data-in (wigwag$get-data-in inputs))
       (extracted-st (wigwag$extract-state st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (wigwag$out-act inputs st) t)
      (cond
       ((equal (wigwag$in-act inputs st) t)
        (cons (pairlis$ data-in nil)
              (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (wigwag$in-act inputs st) t)
          (cons (pairlis$ data-in nil)
                extracted-st))
         (t extracted-st))))))

(defthm wigwag$step-spec-correct
  (b* ((next-st (wigwag$state-fn inputs st)))
    (implies (and (wigwag$input-format inputs)
                  (wigwag$valid-st st)
                  (wigwag$inv st))
             (equal (wigwag$extract-state next-st)
                    (wigwag$step-spec inputs st))))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            wigwag$step-spec
                            wigwag$input-format
                            wigwag$valid-st
                            wigwag$inv
                            wigwag$state-fn
                            wigwag$in-act
                            wigwag$out-act
                            wigwag$extract-state
                            wigwag$br-inputs
                            wigwag$me-inputs
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
                           (nth
                            nthcdr
                            len-nthcdr
                            true-listp
                            pairlis$
                            strip-cars
                            take-of-len-is-itself
                            default-car
                            default-cdr
                            default-+-1
                            default-+-2)))))

(defthm consp-wigwag$extract-state
  (implies (and (wigwag$valid-st st)
                (wigwag$out-act inputs st))
           (consp (wigwag$extract-state st)))
  :hints (("Goal"
           :in-theory (enable wigwag$valid-st
                              wigwag$extract-state
                              wigwag$out-act
                              wigwag$me-inputs
                              alt-merge$valid-st
                              alt-merge$act
                              alt-merge$act0
                              alt-merge$act1)))
  :rule-classes :type-prescription)

;; (defthm wigwag$extract-state-lemma
;;   (implies (and (wigwag$valid-st st)
;;                 (equal n (1- (len (wigwag$extract-state st))))
;;                 (wigwag$out-act inputs st))
;;            (equal (append
;;                    (take n (wigwag$extract-state st))
;;                    (list (pairlis$ (wigwag$data-out st) nil)))
;;                   (wigwag$extract-state st)))
;;   :hints (("Goal"
;;            :in-theory (enable get-field
;;                               wigwag$valid-st
;;                               wigwag$extract-state
;;                               wigwag$out-act
;;                               wigwag$data-out
;;                               wigwag$me-inputs
;;                               alt-merge$valid-st
;;                               alt-merge$act
;;                               alt-merge$act0
;;                               alt-merge$act1))))

(encapsulate
  ()

  (local
   (defthm wigwag$dataflow-correct-aux
     (implies (equal (append x1 y1)
                     (append (wigwag$in-seq inputs-lst st n) y2))
              (equal (append x1 y1 z)
                     (append (wigwag$in-seq inputs-lst st n) y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (acl2::associativity-of-append))))))

  (defthmd wigwag$dataflow-correct
    (b* ((extracted-st (wigwag$extract-state st))
         (final-st (wigwag$state-fn-n inputs-lst st n))
         (final-extracted-st (wigwag$extract-state final-st)))
      (implies (and (wigwag$input-format-n inputs-lst n)
                    (wigwag$valid-st st)
                    (wigwag$inv st))
               (equal (append final-extracted-st
                              (wigwag$out-seq inputs-lst st n))
                      (append (wigwag$in-seq inputs-lst st n)
                              extracted-st))))
    :hints (("Goal"
             :in-theory (e/d (wigwag$step-spec)
                             ()))))
  )

