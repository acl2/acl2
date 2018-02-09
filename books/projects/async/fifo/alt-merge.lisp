;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; February 2018

(in-package "ADE")

(include-book "../link-joint")
(include-book "../tv-if")

(local (include-book "arithmetic-3/top" :dir :system))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of alt-merge
;;; 2. Specifying and Proving a State Invariant

;; ======================================================================

;; 1. DE Module Generator of alt-merge
;;
;; Constructing a DE module generator for an alternate merge, alt-merge,
;; using the link-joint model. Proving the value and state lemmas for this
;; module generator.

(defconst *alt-merge$go-num* 2)
(defconst *alt-merge$st-len* 4)

(defun alt-merge$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 3 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun alt-merge$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (alt-merge$data-ins-len data-width)
     *alt-merge$go-num*))

;; DE module generator of alt-merge

(module-generator
 alt-merge* (data-width)
 (si 'alt-merge data-width)
 (list* 'full-in0 'full-in1 'empty-out-
        (append (sis 'data-in0 0 data-width)
                (sis 'data-in1 0 data-width)
                (sis 'go 0 *alt-merge$go-num*)))
 (list* 'act 'act0 'act1
        (sis 'data-out 0 data-width))
 '(lselect select lselect-buf select-buf)
 (list
  ;; LINKS
  ;; Select
  '(lselect (select-status) link-cntl (buf-act act))
  '(select (select-out select-out~) latch (buf-act select-in))

  ;; Select-buf
  '(lselect-buf (select-buf-status) link-cntl (act buf-act))
  '(select-buf (select-buf-out select-buf-out~) latch (act select-buf-in))

  ;; JOINTS
  ;; Alt-Merge
  '(g0 (ready-in0) b-and3 (full-in0 select-status select-out~))
  '(g1 (ready-in1) b-and3 (full-in1 select-status select-out))
  '(g2 (ready-out-) b-or (empty-out- select-buf-status))
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
        (sis 'data-out 0 data-width)
        (si 'tv-if (tree-number (make-tree data-width)))
        (cons 'select-out
              (append (sis 'data-in1 0 data-width)
                      (sis 'data-in0 0 data-width))))
  '(alt-merge-op1 (select-buf-in) b-not (select-out))

  ;; Buffer
  (list 'buf-cntl
        '(buf-act)
        'joint-cntl
        (list 'select-buf-status 'select-status (si 'go 1)))
  '(buf-op (select-in) b-buf (select-buf-out)))

 :guard (natp data-width))

;; DE netlist generator. A generated netlist will contain an instance of alt-merge.

(defun alt-merge$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (alt-merge* data-width)
        (union$ (tv-if$netlist (make-tree data-width))
                *joint-cntl*
                :test 'equal)))

;; Sanity syntactic check

(defthmd alt-merge$netlist-64-okp
  (and (net-syntax-okp (alt-merge$netlist 64))
       (net-arity-okp (alt-merge$netlist 64))))

;; Recognizer for alt-merge

(defund alt-merge& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (and (equal (assoc (si 'alt-merge data-width) netlist)
              (alt-merge* data-width))
       (b* ((netlist (delete-to-eq (si 'alt-merge data-width) netlist)))
         (and (joint-cntl& netlist)
              (tv-if& netlist (make-tree data-width))))))

;; Sanity check

(defthm check-alt-merge$netlist-64
  (alt-merge& (alt-merge$netlist 64) 64))

(defconst *alt-merge$lselect*     0)
(defconst *alt-merge$select*      1)
(defconst *alt-merge$lselect-buf* 2)
(defconst *alt-merge$select-buf*  3)

;; Constraints on the state of alt-merge

(defund alt-merge$valid-st (st)
  (b* ((lselect (get-field *alt-merge$lselect* st))
       (select  (get-field *alt-merge$select* st))
       (lselect-buf (get-field *alt-merge$lselect-buf* st))
       (select-buf  (get-field *alt-merge$select-buf* st)))
    (and (validp lselect)
         (or (emptyp lselect)
             (booleanp (car select)))

         (validp lselect-buf)
         (or (emptyp lselect-buf)
             (booleanp (car select-buf))))))

;; alt-merge simulator

(progn
  (defun alt-merge$map-to-links (st)
    (b* ((lselect     (get-field *alt-merge$lselect* st))
         (select      (get-field *alt-merge$select* st))
         (lselect-buf (get-field *alt-merge$lselect-buf* st))
         (select-buf  (get-field *alt-merge$select-buf* st)))
      (map-to-links (list (list 'select lselect (list select))
                          (list 'select-buf lselect-buf (list select-buf))))))

  (defun alt-merge$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (alt-merge$map-to-links (car x))
            (alt-merge$map-to-links-list (cdr x)))))

  (defund alt-merge$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (alt-merge$ins-len data-width))
         ((mv inputs-lst state)
          (signal-vals-gen num-signals n state nil))
         ;;(- (cw "~x0~%" inputs-lst))
         (full '(t))
         (empty '(nil))
         (st (list full '(nil)
                   empty '(x))))
      (mv (pretty-list
           (remove-dup-neighbors
            (alt-merge$map-to-links-list
             (de-sim-list (si 'alt-merge data-width)
                          inputs-lst
                          st
                          (alt-merge$netlist data-width))))
           0)
          state)))
  )

;; Extracting the 1st input data item

(defun alt-merge$data-in0 (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (take (mbe :logic (nfix data-width)
             :exec  data-width)
        (nthcdr 3 inputs)))

(defthm len-alt-merge$data-in0
  (equal (len (alt-merge$data-in0 inputs data-width))
         (nfix data-width)))

(in-theory (disable alt-merge$data-in0))

;; Extracting the 2nd input data item

(defun alt-merge$data-in1 (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((width (mbe :logic (nfix data-width)
                   :exec  data-width)))
    (take width
          (nthcdr (+ 3 width) inputs))))

(defthm len-alt-merge$data-in1
  (equal (len (alt-merge$data-in1 inputs data-width))
         (nfix data-width)))

(in-theory (disable alt-merge$data-in1))

;; Extracting the "act0" signal

(defund alt-merge$act0 (inputs st data-width)
  (b* ((full-in0   (nth 0 inputs))
       (empty-out-  (nth 2 inputs))
       (go-signals (nthcdr (alt-merge$data-ins-len data-width) inputs))

       (go-alt-merge (nth 0 go-signals))

       (lselect (get-field *alt-merge$lselect* st))
       (select  (get-field *alt-merge$select* st))
       (lselect-buf (get-field *alt-merge$lselect-buf* st))

       (ready-in0 (f-and3 full-in0 (car lselect) (f-not (car select))))
       (ready-out- (f-or empty-out- (car lselect-buf))))

    (joint-act ready-in0 ready-out- go-alt-merge)))

;; Extracting the "act1" signal

(defund alt-merge$act1 (inputs st data-width)
  (b* ((full-in1   (nth 1 inputs))
       (empty-out-  (nth 2 inputs))
       (go-signals (nthcdr (alt-merge$data-ins-len data-width) inputs))

       (go-alt-merge (nth 0 go-signals))

       (lselect (get-field *alt-merge$lselect* st))
       (select  (get-field *alt-merge$select* st))
       (lselect-buf (get-field *alt-merge$lselect-buf* st))

       (ready-in1 (f-and3 full-in1 (car lselect) (car select)))
       (ready-out- (f-or empty-out- (car lselect-buf))))

    (joint-act ready-in1 ready-out- go-alt-merge)))

;; Extracting the "act" signal

(defund alt-merge$act (inputs st data-width)
  (f-or (alt-merge$act0 inputs st data-width)
        (alt-merge$act1 inputs st data-width)))

(not-primp-lemma alt-merge)

;; The value lemma for alt-merge

(defthmd alt-merge$value
  (b* ((inputs (list* full-in0 full-in1 empty-out-
                      (append data-in0 data-in1 go-signals)))
       (select (get-field *alt-merge$select* st)))
    (implies (and (posp data-width)
                  (alt-merge& netlist data-width)
                  (true-listp data-in0)
                  (equal (len data-in0) data-width)
                  (true-listp data-in1)
                  (equal (len data-in1) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *alt-merge$go-num*)
                  (alt-merge$valid-st st))
             (equal (se (si 'alt-merge data-width) inputs st netlist)
                    (list* (alt-merge$act inputs st data-width)
                           (alt-merge$act0 inputs st data-width)
                           (alt-merge$act1 inputs st data-width)
                           (fv-if (car select) data-in1 data-in0)))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :expand (se (si 'alt-merge data-width)
                       (list* full-in0 full-in1 empty-out-
                              (append data-in0 data-in1 go-signals))
                       st
                       netlist)
           :in-theory (e/d (de-rules
                            get-field
                            not-primp-alt-merge
                            alt-merge&
                            alt-merge*$destructure
                            joint-cntl$value
                            tv-if$value
                            alt-merge$valid-st
                            alt-merge$act
                            alt-merge$act0
                            alt-merge$act1)
                           ((alt-merge*)
                            validp
                            fullp
                            emptyp
                            de-module-disabled-rules)))))

;; This function specifies the next state of alt-merge.

(defun alt-merge$state-fn (inputs st data-width)
  (b* ((go-signals (nthcdr (alt-merge$data-ins-len data-width) inputs))

       (go-buf (nth 1 go-signals))

       (lselect (get-field *alt-merge$lselect* st))
       (select  (get-field *alt-merge$select* st))
       (lselect-buf (get-field *alt-merge$lselect-buf* st))
       (select-buf  (get-field *alt-merge$select-buf* st))

       (act (alt-merge$act inputs st data-width))
       (buf-act (joint-act (car lselect-buf) (car lselect) go-buf)))
    (list
     ;; Select
     (list (f-sr buf-act act (car lselect)))
     (list (f-if buf-act (car select-buf) (car select)))

     ;; Select-buf
     (list (f-sr act buf-act (car lselect-buf)))
     (list (f-if act (f-not (car select)) (car select-buf))))))

(defthm len-of-alt-merge$state-fn
  (equal (len (alt-merge$state-fn inputs st data-width))
         *alt-merge$st-len*))

;; The state lemma for alt-merge

(defthmd alt-merge$state
  (b* ((inputs (list* full-in0 full-in1 empty-out-
                      (append data-in0 data-in1 go-signals))))
    (implies (and (alt-merge& netlist data-width)
                  (equal (len data-in0) data-width)
                  (equal (len data-in1) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *alt-merge$go-num*)
                  (alt-merge$valid-st st))
             (equal (de (si 'alt-merge data-width) inputs st netlist)
                    (alt-merge$state-fn inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :expand (de (si 'alt-merge data-width)
                       (list* full-in0 full-in1 empty-out-
                              (append data-in0 data-in1 go-signals))
                       st
                       netlist)
           :in-theory (e/d (de-rules
                            get-field
                            not-primp-alt-merge
                            alt-merge&
                            alt-merge*$destructure
                            alt-merge$valid-st
                            alt-merge$act
                            alt-merge$act0
                            alt-merge$act1
                            joint-cntl$value
                            tv-if$value)
                           ((alt-merge*)
                            validp
                            fullp
                            emptyp
                            de-module-disabled-rules)))))

(in-theory (disable alt-merge$state-fn))

;; ======================================================================

;; 2. Specifying and Proving a State Invariant

;; Conditions on the inputs

(defund alt-merge$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in0   (nth 0 inputs))
       (full-in1   (nth 1 inputs))
       (empty-out-  (nth 2 inputs))
       (data-in0   (alt-merge$data-in0 inputs data-width))
       (data-in1   (alt-merge$data-in1 inputs data-width))
       (go-signals (nthcdr (alt-merge$data-ins-len data-width) inputs)))
    (and
     (booleanp full-in0)
     (booleanp full-in1)
     (booleanp empty-out-)
     (or (not full-in0) (bvp data-in0))
     (or (not full-in1) (bvp data-in1))
     (true-listp go-signals)
     (= (len go-signals) *alt-merge$go-num*)
     (equal inputs
            (list* full-in0 full-in1 empty-out-
                   (append data-in0 data-in1 go-signals))))))

(defthm alt-merge$valid-st-preserved
  (implies (and (alt-merge$input-format inputs data-width)
                (alt-merge$valid-st st))
           (alt-merge$valid-st (alt-merge$state-fn inputs st data-width)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            alt-merge$input-format
                            alt-merge$valid-st
                            alt-merge$state-fn
                            alt-merge$act
                            alt-merge$act0
                            alt-merge$act1
                            f-and3
                            f-sr)
                           (if*
                            nth
                            nthcdr
                            acl2::true-listp-append)))))

;; A state invariant

(defund alt-merge$inv (st)
  (b* ((lselect     (get-field *alt-merge$lselect* st))
       (lselect-buf (get-field *alt-merge$lselect-buf* st)))
    (not (equal lselect lselect-buf))))

(defthm alt-merge$inv-preserved
  (implies (and (alt-merge$input-format inputs data-width)
                (alt-merge$valid-st st)
                (alt-merge$inv st))
           (alt-merge$inv (alt-merge$state-fn inputs st data-width)))
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

