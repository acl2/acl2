;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; February 2018

(in-package "ADE")

(include-book "../link-joint")
(include-book "../vector-module")

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of alt-branch
;;; 2. Specifying and Proving a State Invariant

;; ======================================================================

;; 1. DE Module Generator of alt-branch
;;
;; Constructing a DE module generator for an alternate branch, alt-branch,
;; using the link-joint model. Proving the value and state lemmas for this
;; module generator.

(defconst *alt-branch$go-num* 2)
(defconst *alt-branch$st-len* 4)

(defun alt-branch$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 3 (mbe :logic (nfix data-width)
            :exec  data-width)))

(defun alt-branch$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (alt-branch$data-ins-len data-width)
     *alt-branch$go-num*))

;; DE module generator of alt-branch

(module-generator
 alt-branch* (data-width)
 (si 'alt-branch data-width)
 (list* 'full-in 'empty-out0- 'empty-out1-
        (append (sis 'data-in 0 data-width)
                (sis 'go 0 *alt-branch$go-num*)))
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
  ;; Alt-Branch
  '(g0 (ready-in) b-and (full-in select-status))
  '(g1 (ready-out0-) b-or3 (empty-out0- select-buf-status select-out))
  '(g2 (ready-out1-) b-or3 (empty-out1- select-buf-status select-out~))
  (list 'alt-branch-cntl0
        '(act0)
        'joint-cntl
        (list 'ready-in 'ready-out0- (si 'go 0)))
  (list 'alt-branch-cntl1
        '(act1)
        'joint-cntl
        (list 'ready-in 'ready-out1- (si 'go 0)))
  '(alt-branch-cntl (act) b-or (act0 act1))

  (list 'alt-branch-op0
        (sis 'data-out 0 data-width)
        (si 'v-buf data-width)
        (sis 'data-in 0 data-width))
  '(alt-branch-op1 (select-buf-in) b-not (select-out))

  ;; Buffer
  (list 'buf-cntl
        '(buf-act)
        'joint-cntl
        (list 'select-buf-status 'select-status (si 'go 1)))
  '(buf-op (select-in) b-buf (select-buf-out)))

 :guard (natp data-width))

;; DE netlist generator. A generated netlist will contain an instance of alt-branch.

(defun alt-branch$netlist (data-width)
  (declare (xargs :guard (natp data-width)))
  (cons (alt-branch* data-width)
        (union$ (v-buf$netlist data-width)
                *joint-cntl*
                :test 'equal)))

;; Sanity syntactic check

(defthmd alt-branch$netlist-64-okp
  (and (net-syntax-okp (alt-branch$netlist 64))
       (net-arity-okp (alt-branch$netlist 64))))

;; Recognizer for alt-branch

(defund alt-branch& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width))))
  (and (equal (assoc (si 'alt-branch data-width) netlist)
              (alt-branch* data-width))
       (b* ((netlist (delete-to-eq (si 'alt-branch data-width) netlist)))
         (and (joint-cntl& netlist)
              (v-buf& netlist data-width)))))

;; Sanity check

(defthm check-alt-branch$netlist-64
  (alt-branch& (alt-branch$netlist 64) 64))

(defconst *alt-branch$lselect*     0)
(defconst *alt-branch$select*      1)
(defconst *alt-branch$lselect-buf* 2)
(defconst *alt-branch$select-buf*  3)

;; Constraints on the state of alt-branch

(defund alt-branch$valid-st (st)
  (b* ((lselect     (get-field *alt-branch$lselect* st))
       (select      (get-field *alt-branch$select* st))
       (lselect-buf (get-field *alt-branch$lselect-buf* st))
       (select-buf  (get-field *alt-branch$select-buf* st)))
    (and (validp lselect)
         (or (emptyp lselect)
             (booleanp (car select)))

         (validp lselect-buf)
         (or (emptyp lselect-buf)
             (booleanp (car select-buf))))))

;; alt-branch simulator

(progn
  (defun alt-branch$map-to-links (st)
    (b* ((lselect (get-field *alt-branch$lselect* st))
         (select  (get-field *alt-branch$select* st))
         (lselect-buf (get-field *alt-branch$lselect-buf* st))
         (select-buf  (get-field *alt-branch$select-buf* st)))
      (map-to-links (list (list 'select lselect (list select))
                          (list 'select-buf lselect-buf (list select-buf))))))

  (defun alt-branch$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (alt-branch$map-to-links (car x))
            (alt-branch$map-to-links-list (cdr x)))))

  (defund alt-branch$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (alt-branch$ins-len data-width))
         ((mv inputs-lst state)
          (signal-vals-gen num-signals n state nil))
         ;;(- (cw "~x0~%" inputs-lst))
         (full '(t))
         (empty '(nil))
         (st (list full '(nil)
                   empty '(x))))
      (mv (pretty-list
           (remove-dup-neighbors
            (alt-branch$map-to-links-list
             (de-sim-list (si 'alt-branch data-width)
                          inputs-lst
                          st
                          (alt-branch$netlist data-width))))
           0)
          state)))
  )

;; Extracting the input data

(defun alt-branch$data-in (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (take (mbe :logic (nfix data-width)
             :exec  data-width)
        (nthcdr 3 inputs)))

(defthm len-alt-branch$data-in
  (equal (len (alt-branch$data-in inputs data-width))
         (nfix data-width)))

(in-theory (disable alt-branch$data-in))

;; Extracting the "act0" signal

(defund alt-branch$act0 (inputs st data-width)
  (b* ((full-in    (nth 0 inputs))
       (empty-out0- (nth 1 inputs))
       (go-signals (nthcdr (alt-branch$data-ins-len data-width) inputs))

       (go-alt-branch (nth 0 go-signals))

       (lselect (get-field *alt-branch$lselect* st))
       (select  (get-field *alt-branch$select* st))
       (lselect-buf (get-field *alt-branch$lselect-buf* st))

       (ready-in (f-and full-in (car lselect)))
       (ready-out0- (f-or3 empty-out0- (car lselect-buf) (car select))))

    (joint-act ready-in ready-out0- go-alt-branch)))

;; Extracting the "act1" signal

(defund alt-branch$act1 (inputs st data-width)
  (b* ((full-in    (nth 0 inputs))
       (empty-out1- (nth 2 inputs))
       (go-signals (nthcdr (alt-branch$data-ins-len data-width) inputs))

       (go-alt-branch (nth 0 go-signals))

       (lselect (get-field *alt-branch$lselect* st))
       (select  (get-field *alt-branch$select* st))
       (lselect-buf (get-field *alt-branch$lselect-buf* st))

       (ready-in (f-and full-in (car lselect)))
       (ready-out1- (f-or3 empty-out1-
                           (car lselect-buf)
                           (f-not (car select)))))

    (joint-act ready-in ready-out1- go-alt-branch)))

;; Extracting the "act" signal

(defund alt-branch$act (inputs st data-width)
  (f-or (alt-branch$act0 inputs st data-width)
        (alt-branch$act1 inputs st data-width)))

(not-primp-lemma alt-branch)

;; The value lemma for alt-branch

(defthmd alt-branch$value
  (b* ((inputs (list* full-in empty-out0- empty-out1-
                      (append data-in go-signals))))
    (implies (and (alt-branch& netlist data-width)
                  (true-listp data-in)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *alt-branch$go-num*)
                  (alt-branch$valid-st st))
             (equal (se (si 'alt-branch data-width) inputs st netlist)
                    (list* (alt-branch$act inputs st data-width)
                           (alt-branch$act0 inputs st data-width)
                           (alt-branch$act1 inputs st data-width)
                           (v-threefix data-in)))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :expand (se (si 'alt-branch data-width)
                       (list* full-in empty-out0- empty-out1-
                              (append data-in go-signals))
                       st
                       netlist)
           :in-theory (e/d (de-rules
                            get-field
                            not-primp-alt-branch
                            alt-branch&
                            alt-branch*$destructure
                            joint-cntl$value
                            v-buf$value
                            alt-branch$valid-st
                            alt-branch$act
                            alt-branch$act0
                            alt-branch$act1)
                           ((alt-branch*)
                            validp
                            fullp
                            emptyp
                            de-module-disabled-rules)))))

;; This function specifies the next state of alt-branch.

(defun alt-branch$state-fn (inputs st data-width)
  (b* ((go-signals (nthcdr (alt-branch$data-ins-len data-width) inputs))

       (go-buf (nth 1 go-signals))

       (lselect (get-field *alt-branch$lselect* st))
       (select  (get-field *alt-branch$select* st))
       (lselect-buf (get-field *alt-branch$lselect-buf* st))
       (select-buf  (get-field *alt-branch$select-buf* st))

       (act (alt-branch$act inputs st data-width))
       (buf-act (joint-act (car lselect-buf) (car lselect) go-buf)))
    (list
     ;; Select
     (list (f-sr buf-act act (car lselect)))
     (list (f-if buf-act (car select-buf) (car select)))

     ;; Select-buf
     (list (f-sr act buf-act (car lselect-buf)))
     (list (f-if act (f-not (car select)) (car select-buf))))))

(defthm len-of-alt-branch$state-fn
  (equal (len (alt-branch$state-fn inputs st data-width))
         *alt-branch$st-len*))

;; The state lemma for alt-branch

(defthmd alt-branch$state
  (b* ((inputs (list* full-in empty-out0- empty-out1-
                      (append data-in go-signals))))
    (implies (and (alt-branch& netlist data-width)
                  (equal (len data-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *alt-branch$go-num*)
                  (alt-branch$valid-st st))
             (equal (de (si 'alt-branch data-width) inputs st netlist)
                    (alt-branch$state-fn inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :expand (de (si 'alt-branch data-width)
                       (list* full-in empty-out0- empty-out1-
                              (append data-in go-signals))
                       st
                       netlist)
           :in-theory (e/d (de-rules
                            get-field
                            not-primp-alt-branch
                            alt-branch&
                            alt-branch*$destructure
                            alt-branch$valid-st
                            alt-branch$act
                            alt-branch$act0
                            alt-branch$act1
                            joint-cntl$value
                            v-buf$value)
                           ((alt-branch*)
                            validp
                            fullp
                            emptyp
                            de-module-disabled-rules)))))

(in-theory (disable alt-branch$state-fn))

;; ======================================================================

;; 2. Specifying and Proving a State Invariant

;; Conditions on the inputs

(defund alt-branch$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out0- (nth 1 inputs))
       (empty-out1- (nth 2 inputs))
       (data-in    (alt-branch$data-in inputs data-width))
       (go-signals (nthcdr (alt-branch$data-ins-len data-width) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out0-)
     (booleanp empty-out1-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *alt-branch$go-num*)
     (equal inputs
            (list* full-in empty-out0- empty-out1-
                   (append data-in go-signals))))))

(defthm alt-branch$valid-st-preserved
  (implies (and (alt-branch$input-format inputs data-width)
                (alt-branch$valid-st st))
           (alt-branch$valid-st
            (alt-branch$state-fn inputs st data-width)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            alt-branch$input-format
                            alt-branch$valid-st
                            alt-branch$state-fn
                            alt-branch$act
                            alt-branch$act0
                            alt-branch$act1
                            f-sr)
                           (if*
                            nth
                            nthcdr
                            acl2::true-listp-append)))))

;; A state invariant

(defund alt-branch$inv (st)
  (b* ((lselect     (get-field *alt-branch$lselect* st))
       (lselect-buf (get-field *alt-branch$lselect-buf* st)))
    (not (equal lselect lselect-buf))))

(defthm alt-branch$inv-preserved
  (implies (and (alt-branch$input-format inputs data-width)
                (alt-branch$valid-st st)
                (alt-branch$inv st))
           (alt-branch$inv (alt-branch$state-fn inputs st data-width)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            alt-branch$input-format
                            alt-branch$valid-st
                            alt-branch$inv
                            alt-branch$state-fn
                            alt-branch$act
                            alt-branch$act0
                            alt-branch$act1
                            f-sr)
                           (if*
                            nth
                            nthcdr
                            acl2::true-listp-append)))))

