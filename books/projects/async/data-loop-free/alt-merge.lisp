;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; December 2017

(in-package "ADE")

(include-book "constants")
(include-book "link-joint")
(include-book "tv-if")

(local (in-theory (e/d (f-buf-delete-lemmas-1
                        f-buf-delete-lemmas-2)
                       (nth-of-bvp-is-booleanp
                        take-of-len-free))))

;; ======================================================================

;; Alternate merge

(defconst *alt-merge$data-ins-len* (+ 3 (* 2 *data-width*)))
(defconst *alt-merge$go-num* 2)
(defconst *alt-merge$ins-len* (+ *alt-merge$data-ins-len*
                             *alt-merge$go-num*))
(defconst *alt-merge$st-len* 4)

(module-generator
 alt-merge* ()
 'alt-merge
 (list* 'full-in0 'full-in1 'full-out-
        (append (sis 'data-in0 0 *data-width*)
                (sis 'data-in1 0 *data-width*)
                (sis 'go 0 *alt-merge$go-num*)))
 (list* 'act 'act0 'act1
        (sis 'data-out 0 *data-width*))
 '(lmux mux lmux-buf mux-buf)
 (list
  ;; LINKS
  ;; Mux
  '(lmux (mux-status) link-cntl (buf-act act))
  '(mux (mux-out mux-out~) latch (buf-act mux-in))
  
  ;; Mux-buf
  '(lmux-buf (mux-buf-status) link-cntl (act buf-act))
  '(mux-buf (mux-buf-out mux-buf-out~) latch (act mux-buf-in))

  ;; JOINTS
  ;; Alt-Merge
  '(g0 (ready-in0) b-and3 (full-in0 mux-status mux-out~))
  '(g1 (ready-in1) b-and3 (full-in1 mux-status mux-out))
  '(g2 (ready-out-) b-or (full-out- mux-buf-status))
  (list 'alt-merge-cntl0
        '(act0)
        'joint-cntl
        (list 'ready-in0 'ready-out- (si 'go 0)))
  (list 'alt-merge-cntl1
        '(act1)
        'joint-cntl
        (list 'ready-in1 'ready-out- (si 'go 0)))
  '(alt-merge-cntl (act) b-or (act0 act1))

  (list 'alt-merge-op0
        (sis 'data-out 0 *data-width*)
        (si 'tv-if (tree-number (make-tree *data-width*)))
        (cons 'mux-out
              (append (sis 'data-in1 0 *data-width*)
                      (sis 'data-in0 0 *data-width*))))
  '(alt-merge-op1 (mux-buf-in) b-not (mux-out))

  ;; Buffer
  (list 'buf-cntl
        '(buf-act)
        'joint-cntl
        (list 'mux-buf-status 'mux-status (si 'go 1)))
  '(buf-op (mux-in) b-buf (mux-buf-out)))

 :guard t)

(defun alt-merge$netlist ()
  (declare (xargs :guard t))
  (cons (alt-merge*)
        (union$ (tv-if$netlist (make-tree *data-width*))
                *joint-cntl*
                :test 'equal)))

(defthmd alt-merge$netlist-okp
  (and (net-syntax-okp (alt-merge$netlist))
       (net-arity-okp (alt-merge$netlist))))

(defund alt-merge& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (and (equal (assoc 'alt-merge netlist)
              (alt-merge*))
       (b* ((netlist (delete-to-eq 'alt-merge netlist)))
         (and (joint-cntl& netlist)
              (tv-if& netlist (make-tree *data-width*))))))

(defthm check-alt-merge$netlist
  (alt-merge& (alt-merge$netlist)))

(defconst *alt-merge$lmux*     0)
(defconst *alt-merge$mux*      1)
(defconst *alt-merge$lmux-buf* 2)
(defconst *alt-merge$mux-buf*  3)

(defund alt-merge$valid-st (st)
  (b* ((lmux (get-field *alt-merge$lmux* st))
       (mux  (get-field *alt-merge$mux* st))
       (lmux-buf (get-field *alt-merge$lmux-buf* st))
       (mux-buf  (get-field *alt-merge$mux-buf* st)))
    (and (validp lmux)
         (booleanp (car mux))

         (validp lmux-buf)
         (booleanp (car mux-buf)))))

(defun alt-merge$map-to-links (st)
  (b* ((lmux     (get-field *alt-merge$lmux* st))
       (mux      (get-field *alt-merge$mux* st))
       (lmux-buf (get-field *alt-merge$lmux-buf* st))
       (mux-buf  (get-field *alt-merge$mux-buf* st)))
    (map-to-links (list (list 'mux lmux (list mux))
                        (list 'mux-buf lmux-buf (list mux-buf))))))

(defun alt-merge$map-to-links-list (x)
  (if (atom x)
      nil
    (cons (alt-merge$map-to-links (car x))
          (alt-merge$map-to-links-list (cdr x)))))

(defund alt-merge$sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *alt-merge$ins-len*)
       ((mv inputs-lst state) (go-vals-gen num-signals n state nil))
       ;;(- (cw "~x0~%" inputs-lst))
       (full '(t))
       (empty '(nil))
       (st (list full '(nil)
                 empty '(x))))
    (mv (pretty-list
         (remove-dup-neighbors
          (alt-merge$map-to-links-list
           (de-sim-list 'alt-merge inputs-lst st (alt-merge$netlist))))
         0)
        state)))

(defun alt-merge$get-data-in0 (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (subseq-list inputs 3 (+ 3 *data-width*)))

(defthm len-alt-merge$get-data-in0
  (equal (len (alt-merge$get-data-in0 inputs))
         *data-width*))

(in-theory (disable alt-merge$get-data-in0))

(defun alt-merge$get-data-in1 (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (subseq-list inputs
               (+ 3 *data-width*)
               (+ 3 (* 2 *data-width*))))

(defthm len-alt-merge$get-data-in1
  (equal (len (alt-merge$get-data-in1 inputs))
         *data-width*))

(in-theory (disable alt-merge$get-data-in1))

(defund alt-merge$act0 (inputs st)
  (b* ((full-in0   (nth 0 inputs))
       (full-out-  (nth 2 inputs))
       (go-signals (nthcdr *alt-merge$data-ins-len* inputs))
       
       (go-alt-merge (nth 0 go-signals))
       
       (lmux (get-field *alt-merge$lmux* st))
       (mux  (get-field *alt-merge$mux* st))
       (lmux-buf (get-field *alt-merge$lmux-buf* st))

       (ready-in0 (f-and3 full-in0 (car lmux) (f-not (car mux))))
       (ready-out- (f-or full-out- (car lmux-buf))))
    
    (joint-act ready-in0 ready-out- go-alt-merge)))

(defund alt-merge$act1 (inputs st)
  (b* ((full-in1   (nth 1 inputs))
       (full-out-  (nth 2 inputs))
       (go-signals (nthcdr *alt-merge$data-ins-len* inputs))
       
       (go-alt-merge (nth 0 go-signals))
       
       (lmux (get-field *alt-merge$lmux* st))
       (mux  (get-field *alt-merge$mux* st))
       (lmux-buf (get-field *alt-merge$lmux-buf* st))

       (ready-in1 (f-and3 full-in1 (car lmux) (car mux)))
       (ready-out- (f-or full-out- (car lmux-buf))))
    
    (joint-act ready-in1 ready-out- go-alt-merge)))

(defund alt-merge$act (inputs st)
  (f-or (alt-merge$act0 inputs st)
        (alt-merge$act1 inputs st)))

(defthmd alt-merge$value
  (b* ((inputs (list* full-in0 full-in1 full-out-
                      (append data-in0 data-in1 go-signals)))
       (mux (get-field *alt-merge$mux* st)))
    (implies (and (alt-merge& netlist)
                  (true-listp data-in0)
                  (equal (len data-in0) *data-width*)
                  (true-listp data-in1)
                  (equal (len data-in1) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *alt-merge$go-num*)
                  (alt-merge$valid-st st))
             (equal (se 'alt-merge inputs st netlist)
                    (list* (alt-merge$act inputs st)
                           (alt-merge$act0 inputs st)
                           (alt-merge$act1 inputs st)
                           (fv-if (car mux) data-in1 data-in0)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (se-rules
                            get-field
                            alt-merge&
                            alt-merge*$destructure
                            joint-cntl$value
                            tv-if$value
                            open-nth
                            alt-merge$valid-st
                            alt-merge$act
                            alt-merge$act0
                            alt-merge$act1)
                           ((alt-merge*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(defun alt-merge$state-fn (inputs st)
  (b* ((go-signals (nthcdr *alt-merge$data-ins-len* inputs))

       (go-buf (nth 1 go-signals))
       
       (lmux (get-field *alt-merge$lmux* st))
       (mux  (get-field *alt-merge$mux* st))
       (lmux-buf (get-field *alt-merge$lmux-buf* st))
       (mux-buf  (get-field *alt-merge$mux-buf* st))

       (act (alt-merge$act inputs st))
       (buf-act (joint-act (car lmux-buf) (car lmux) go-buf)))
    (list
     (list (f-sr buf-act act (car lmux)))
     (list (f-if buf-act (car mux-buf) (car mux)))

     (list (f-sr act buf-act (car lmux-buf)))
     (list (f-if act (f-not (car mux)) (car mux-buf))))))

(defthm len-of-alt-merge$state-fn
  (equal (len (alt-merge$state-fn inputs st))
         *alt-merge$st-len*))

(defthmd alt-merge$state
  (b* ((inputs (list* full-in0 full-in1 full-out-
                      (append data-in0 data-in1 go-signals))))
    (implies (and (alt-merge& netlist)
                  (equal (len data-in0) *data-width*)
                  (equal (len data-in1) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *alt-merge$go-num*)
                  (alt-merge$valid-st st))
             (equal (de 'alt-merge inputs st netlist)
                    (alt-merge$state-fn inputs st))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (de-rules
                            get-field
                            alt-merge&
                            alt-merge*$destructure
                            alt-merge$valid-st
                            alt-merge$act
                            alt-merge$act0
                            alt-merge$act1
                            open-nth
                            joint-cntl$value
                            tv-if$value)
                           ((alt-merge*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(in-theory (disable alt-merge$state-fn))

;; ======================================================================

(defund alt-merge$input-format (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((full-in0   (nth 0 inputs))
       (full-in1   (nth 1 inputs))
       (full-out-  (nth 2 inputs))
       (data-in0   (alt-merge$get-data-in0 inputs))
       (data-in1   (alt-merge$get-data-in1 inputs))
       (go-signals (nthcdr *alt-merge$data-ins-len* inputs)))
    (and
     (booleanp full-in0)
     (booleanp full-in1)
     (booleanp full-out-)
     (bvp data-in0)
     (bvp data-in1)
     (true-listp go-signals)
     (= (len go-signals) *alt-merge$go-num*)
     (equal inputs
            (list* full-in0 full-in1 full-out-
                   (append data-in0 data-in1 go-signals))))))

(defthm alt-merge$valid-st-preserved
  (implies (and (alt-merge$input-format inputs)
                (alt-merge$valid-st st))
           (alt-merge$valid-st (alt-merge$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            alt-merge$input-format
                            alt-merge$valid-st
                            alt-merge$state-fn
                            alt-merge$act
                            alt-merge$act0
                            alt-merge$act1
                            f-sr)
                           (if*
                            nth
                            nthcdr
                            acl2::true-listp-append)))))

(defund alt-merge$inv (st)
  (b* ((lmux     (get-field *alt-merge$lmux* st))
       (lmux-buf (get-field *alt-merge$lmux-buf* st)))
    (not (equal lmux lmux-buf))))

(defthm alt-merge$inv-preserved
  (implies (and (alt-merge$input-format inputs)
                (alt-merge$valid-st st)
                (alt-merge$inv st))
           (alt-merge$inv (alt-merge$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            alt-merge$input-format
                            alt-merge$valid-st
                            alt-merge$inv
                            alt-merge$state-fn
                            alt-merge$act
                            alt-merge$act0
                            alt-merge$act1
                            f-sr)
                           (if*
                            nth
                            nthcdr
                            acl2::true-listp-append)))))

