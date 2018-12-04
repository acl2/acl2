;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; November 2018

(in-package "ADE")

(include-book "piso2-sreg")
(include-book "sipo-sreg")

(local (include-book "../list-rewrites"))

(local (include-book "arithmetic-5/top" :dir :system))

(local (in-theory (disable nth)))

(local
 (deftheory serial-sub$disabled-rules
   '(acl2::default-plus-1
     acl2::default-plus-2
     acl2::normalize-terms-such-as-a/a+b-+-b/a+b
     acl2::acl2-numberp-x
     acl2::default-less-than-1
     acl2::default-less-than-2
     acl2::prefer-positive-addends-<
     acl2::simplify-products-gather-exponents-<
     acl2::len-when-prefixp
     acl2::take-when-prefixp
     take-redefinition
     not
     default-car
     default-cdr
     true-listp
     bv-is-true-list)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of SERIAL-SUB
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of SERIAL-SUB
;;
;; Construct a DE module generator that generates self-timed serial subtractor
;; modules.  Prove the value and state lemmas for this module generator.

(defconst *serial-sub$prim-go-num* 2)
(defconst *serial-sub$go-num* (+ *serial-sub$prim-go-num*
                                 *piso2-sreg$go-num*
                                 *sipo-sreg$go-num*))
(defconst *serial-sub$st-len* 8)

(defun serial-sub$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun serial-sub$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (serial-sub$data-ins-len data-width)
     *serial-sub$go-num*))

;; DE module generator of SERIAL-SUB

(module-generator
 serial-sub* (data-width cnt-width)
 (si 'serial-sub data-width)
 (list* 'full-in 'empty-out-
        (append (sis 'data0-in 0 data-width)
                (sis 'data1-in 0 data-width)
                (sis 'go 0 *serial-sub$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-width))
 '(a b ci s co done piso2 sipo)
 (list
  ;; LINKS
  ;; A
  '(a (a-status a-out)
      link1
      (piso2-out0-act sub-act piso2-bit0-out))

  ;; B
  '(b (b-status b-out)
      link1
      (piso2-out1-act sub-act piso2-bit1-out))

  ;; CI
  '(ci (ci-status ci-out)
       link1
       (c-buf-act sub-act ci-in))

  ;; S
  '(s (s-status s-out)
      link1
      (sub-act sipo-in-act s-in))

  ;; CO
  '(co (co-status co-out)
       link1
       (sub-act c-buf-act co-in))

  ;; DONE
  '(done (done-status done-out)
         link1
         (sipo-in-act c-buf-act cnt-out<2))

  ;; JOINTS
  ;; PISO2
  (list 'piso2
        '(in-act piso2-out0-act piso2-out1-act
                 piso2-bit0-out piso2-bit1-out)
        (si 'piso2-sreg data-width)
        (list* 'full-in 'a-status 'b-status
               (append (sis 'data0-in 0 data-width)
                       (sis 'data1-in 0 data-width)
                       (sis 'go
                            *serial-sub$prim-go-num*
                            *piso2-sreg$go-num*))))

  ;; SIPO
  '(g0 (done-status~) b-not (done-status))
  '(g1 (sipo-full-in) b-and (s-status done-status~))
  (list 'sipo
        (list* 'sipo-in-act 'out-act (append (sis 'data-out 0 data-width)
                                             (sis 'cnt-out 0 cnt-width)))
        (si 'sipo-sreg data-width)
        (list* 'sipo-full-in 'empty-out- 's-out
               (sis 'go
                    (+ *serial-sub$prim-go-num*
                       *piso2-sreg$go-num*)
                    *sipo-sreg$go-num*)))
  (list 'cnt-out<2?
        '(cnt-out<2)
        (si 'fast-zero (1- cnt-width))
        (sis 'cnt-out 1 (1- cnt-width)))

  ;; SUB
  '(g3 (sub-full-in) b-and3 (a-status b-status ci-status))
  '(g4 (sub-empty-out-) b-or (s-status co-status))
  '(g5 (b-out~) b-not (b-out))
  (list 'sub-cntl
        '(sub-act)
        'joint-cntl
        (list 'sub-full-in 'sub-empty-out- (si 'go 0)))
  '(sub-op (s-in co-in) full-adder (ci-out a-out b-out~))

  ;; C-BUF
  '(g6 (high) vdd ())
  '(g7 (c-buf-full-in) b-and (co-status done-status))
  (list 'c-buf-cntl
        '(c-buf-act)
        'joint-cntl
        (list 'c-buf-full-in 'ci-status (si 'go 1)))
  '(c-buf-op (ci-in) b-if (done-out high co-out)))

 (declare (xargs :guard (and (posp data-width) (posp cnt-width)))))

(make-event
 `(progn
    ,@(state-accessors-gen 'serial-sub
                           '(a b ci s co done piso2 sipo)
                           0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; SERIAL-SUB.

(defund serial-sub$netlist (data-width cnt-width)
  (declare (xargs :guard (and (posp data-width)
                              (natp cnt-width)
                              (<= 3 cnt-width))))
  (cons (serial-sub* data-width cnt-width)
        (union$ (link1$netlist)
                (fast-zero$netlist (1- cnt-width))
                (piso2-sreg$netlist data-width cnt-width)
                (sipo-sreg$netlist data-width cnt-width)
                :test 'equal)))

;; Recognizer for SERIAL-SUB

(defund serial-sub& (netlist data-width cnt-width)
  (declare (xargs :guard (and (alistp netlist)
                              (posp data-width)
                              (natp cnt-width)
                              (<= 3 cnt-width))))
  (b* ((subnetlist (delete-to-eq (si 'serial-sub data-width) netlist)))
    (and (equal (assoc (si 'serial-sub data-width) netlist)
                (serial-sub* data-width cnt-width))
         (link1& subnetlist)
         (joint-cntl& subnetlist)
         (fast-zero& subnetlist (1- cnt-width))
         (full-adder& subnetlist)
         (piso2-sreg& subnetlist data-width cnt-width)
         (sipo-sreg& subnetlist data-width cnt-width))))

;; Sanity check

(local
 (defthmd check-serial-sub$netlist-64-7
   (and (net-syntax-okp (serial-sub$netlist 64 7))
        (net-arity-okp (serial-sub$netlist 64 7))
        (serial-sub& (serial-sub$netlist 64 7) 64 7))))

;; Constraints on the state of SERIAL-SUB

(defund serial-sub$st-format (st data-width cnt-width)
  (b* ((piso2 (get-field *serial-sub$piso2* st))
       (sipo (get-field *serial-sub$sipo* st)))
    (and (<= 4 cnt-width)
         (piso2-sreg$st-format piso2 data-width cnt-width)
         (sipo-sreg$st-format sipo data-width cnt-width))))

(defthm serial-sub$st-format=>contraints
  (implies (serial-sub$st-format st data-width cnt-width)
           (and (posp data-width)
                (natp cnt-width)
                (<= 4 cnt-width)))
  :hints (("Goal" :in-theory (enable serial-sub$st-format)))
  :rule-classes :forward-chaining)

(defund serial-sub$valid-st (st data-width cnt-width)
  (b* ((a (get-field *serial-sub$a* st))
       (b (get-field *serial-sub$b* st))
       (ci (get-field *serial-sub$ci* st))
       (s (get-field *serial-sub$s* st))
       (co (get-field *serial-sub$co* st))
       (done (get-field *serial-sub$done* st))
       (piso2 (get-field *serial-sub$piso2* st))
       (sipo (get-field *serial-sub$sipo* st)))
    (and (<= 4 cnt-width)
         (link1$valid-st a)
         (link1$valid-st b)
         (link1$valid-st ci)
         (link1$valid-st s)
         (link1$valid-st co)
         (link1$valid-st done)
         (piso2-sreg$valid-st piso2 data-width cnt-width)
         (sipo-sreg$valid-st sipo data-width cnt-width))))

(local
 (defthm expt-linear-lower-<=-instance
   (implies (and (<= 3 n)
                 (integerp n))
            (<= 8 (expt 2 n)))
   :rule-classes :linear))

(defthmd serial-sub$valid-st=>constraints
  (implies (serial-sub$valid-st st data-width cnt-width)
           (and (natp data-width)
                (<= 8 data-width)
                (natp cnt-width)
                (<= 4 cnt-width)))
  :hints (("Goal"
           :in-theory (enable piso2-sreg$valid-st=>constraints
                              sipo-sreg$valid-st
                              serial-sub$valid-st)))
  :rule-classes :forward-chaining)

(defthmd serial-sub$valid-st=>st-format
  (implies (serial-sub$valid-st st data-width cnt-width)
           (serial-sub$st-format st data-width cnt-width))
  :hints (("Goal" :in-theory (enable piso2-sreg$valid-st=>st-format
                                     sipo-sreg$valid-st=>st-format
                                     serial-sub$st-format
                                     serial-sub$valid-st))))

;; Extract the input and output signals for SERIAL-SUB

(progn
  ;; Extract the 1st input operand

  (defun serial-sub$data0-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 2 inputs)))

  (defthm len-serial-sub$data0-in
    (equal (len (serial-sub$data0-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable serial-sub$data0-in))

  ;; Extract the 2nd input operand

  (defun serial-sub$data1-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (b* ((width (mbe :logic (nfix data-width)
                     :exec  data-width)))
      (take width
            (nthcdr (+ 2 width) inputs))))

  (defthm len-serial-sub$data1-in
    (equal (len (serial-sub$data1-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable serial-sub$data1-in))

  ;; Extract the inputs for joint PISO2

  (defund serial-sub$piso2-inputs (inputs st data-width)
    (b* ((full-in0 (nth 0 inputs))
         (data0-in (serial-sub$data0-in inputs data-width))
         (data1-in (serial-sub$data1-in inputs data-width))
         (go-signals (nthcdr (serial-sub$data-ins-len data-width) inputs))

         (piso2-go-signals (take *piso2-sreg$go-num*
                                  (nthcdr *serial-sub$prim-go-num*
                                          go-signals)))

         (a (get-field *serial-sub$a* st))
         (a.s (get-field *link1$s* a))
         (b (get-field *serial-sub$b* st))
         (b.s (get-field *link1$s* b)))

      (list* full-in0 (f-buf (car a.s)) (f-buf (car b.s))
             (append data0-in data1-in piso2-go-signals))))

  ;; Extract the inputs for joint SIPO

  (defund serial-sub$sipo-inputs (inputs st data-width)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (serial-sub$data-ins-len data-width) inputs))

         (sipo-go-signals (take *sipo-sreg$go-num*
                                (nthcdr (+ *serial-sub$prim-go-num*
                                           *piso2-sreg$go-num*)
                                        go-signals)))

         (s (get-field *serial-sub$s* st))
         (s.s (get-field *link1$s* s))
         (s.d (get-field *link1$d* s))
         (done (get-field *serial-sub$done* st))
         (done.s (get-field *link1$s* done))

         (sipo-full-in (f-and (car s.s) (f-not (car done.s)))))

      (list* sipo-full-in empty-out- (f-buf (car s.d))
             sipo-go-signals)))

  ;; Extract the "in-act" signal

  (defund serial-sub$in-act (inputs st data-width)
    (b* ((piso2-inputs (serial-sub$piso2-inputs inputs st data-width))
         (piso2 (get-field *serial-sub$piso2* st)))
      (piso2-sreg$in-act piso2-inputs piso2 data-width)))

  (defthm serial-sub$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (serial-sub$in-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable serial-sub$piso2-inputs
                                       serial-sub$in-act))))

  ;; Extract the "out-act" signal

  (defund serial-sub$out-act (inputs st data-width)
    (b* ((sipo-inputs (serial-sub$sipo-inputs inputs st data-width))
         (sipo (get-field *serial-sub$sipo* st)))
      (sipo-sreg$out-act sipo-inputs sipo)))

  (defthm serial-sub$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (serial-sub$out-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable serial-sub$sipo-inputs
                                       serial-sub$out-act))))

  ;; Extract the output data

  (defund serial-sub$data-out (st)
    (b* ((sipo (get-field *serial-sub$sipo* st)))
      (sipo-sreg$data-out sipo)))

  (defthm len-serial-sub$data-out-1
    (implies (serial-sub$st-format st data-width cnt-width)
             (equal (len (serial-sub$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable serial-sub$st-format
                                       serial-sub$data-out))))

  (defthm len-serial-sub$data-out-2
    (implies (serial-sub$valid-st st data-width cnt-width)
             (equal (len (serial-sub$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable serial-sub$valid-st
                                       serial-sub$data-out))))

  (defthm bvp-serial-sub$data-out
    (implies (and (serial-sub$valid-st st data-width cnt-width)
                  (serial-sub$out-act inputs st data-width))
             (bvp (serial-sub$data-out st)))
    :hints (("Goal" :in-theory (e/d (serial-sub$valid-st
                                     serial-sub$out-act
                                     serial-sub$data-out)
                                    (sipo-sreg$extract-lemma)))))

  (defun serial-sub$outputs (inputs st data-width)
    (list* (serial-sub$in-act inputs st data-width)
           (serial-sub$out-act inputs st data-width)
           (serial-sub$data-out st)))
  )

;; The value lemma for SERIAL-SUB

(defthm serial-sub$value
  (b* ((inputs (list* full-in empty-out-
                      (append data0-in data1-in go-signals))))
    (implies (and (serial-sub& netlist data-width cnt-width)
                  (true-listp data0-in)
                  (equal (len data0-in) data-width)
                  (true-listp data1-in)
                  (equal (len data1-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *serial-sub$go-num*)
                  (serial-sub$st-format st data-width cnt-width))
             (equal (se (si 'serial-sub data-width) inputs st netlist)
                    (serial-sub$outputs inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'serial-sub data-width)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            serial-sub&
                            serial-sub*$destructure
                            serial-sub$data0-in
                            serial-sub$data1-in
                            serial-sub$piso2-inputs
                            serial-sub$sipo-inputs
                            serial-sub$st-format
                            serial-sub$in-act
                            serial-sub$out-act
                            serial-sub$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of SERIAL-SUB.

(defun serial-sub$step (inputs st data-width cnt-width)
  (b* ((go-signals (nthcdr (serial-sub$data-ins-len data-width)
                           inputs))
       (go-sub (nth 0 go-signals))
       (go-c-buf (nth 1 go-signals))

       (a (get-field *serial-sub$a* st))
       (b (get-field *serial-sub$b* st))
       (ci (get-field *serial-sub$ci* st))
       (s (get-field *serial-sub$s* st))
       (co (get-field *serial-sub$co* st))
       (done (get-field *serial-sub$done* st))
       (piso2 (get-field *serial-sub$piso2* st))
       (sipo (get-field *serial-sub$sipo* st))

       (piso2-inputs (serial-sub$piso2-inputs inputs st data-width))
       (sipo-inputs (serial-sub$sipo-inputs inputs st data-width))

       (a.s (get-field *link1$s* a))
       (a.d (get-field *link1$d* a))
       (b.s (get-field *link1$s* b))
       (b.d (get-field *link1$d* b))
       (ci.s (get-field *link1$s* ci))
       (ci.d (get-field *link1$d* ci))
       (s.s (get-field *link1$s* s))
       (co.s (get-field *link1$s* co))
       (co.d (get-field *link1$d* co))
       (done.s (get-field *link1$s* done))
       (done.d (get-field *link1$d* done))

       (piso2-out0-act
        (piso2-sreg$out0-act piso2-inputs piso2 data-width))
       (piso2-out1-act
        (piso2-sreg$out1-act piso2-inputs piso2 data-width))
       (piso2-bit0-out (piso2-sreg$bit0-out piso2))
       (piso2-bit1-out (piso2-sreg$bit1-out piso2))
       (sipo-in-act
        (sipo-sreg$in-act sipo-inputs sipo))
       (cnt-out (sipo-sreg$cnt-out sipo))
       (cnt-out<2 (f$fast-zero (nthcdr 1 cnt-out)))
       (sub-act (joint-act (f-and3 (car a.s) (car b.s) (car ci.s))
                           (f-or (car s.s) (car co.s))
                           go-sub))
       (s-in (f-xor3 (car ci.d) (car a.d) (f-not (car b.d))))
       (co-in (f-or (f-and (car a.d) (f-not (car b.d)))
                    (f-and (f-xor (car a.d) (f-not (car b.d)))
                           (car ci.d))))
       (c-buf-act (joint-act (f-and (car co.s) (car done.s))
                             (car ci.s)
                             go-c-buf))
       (ci-in (f-if (car done.d) t (car co.d)))

       (a-inputs (list piso2-out0-act sub-act piso2-bit0-out))
       (b-inputs (list piso2-out1-act sub-act piso2-bit1-out))
       (ci-inputs (list c-buf-act sub-act ci-in))
       (s-inputs (list sub-act sipo-in-act s-in))
       (co-inputs (list sub-act c-buf-act co-in))
       (done-inputs (list sipo-in-act c-buf-act cnt-out<2)))
    (list
     ;; A
     (link1$step a-inputs a)
     ;; B
     (link1$step b-inputs b)
     ;; CI
     (link1$step ci-inputs ci)
     ;; S
     (link1$step s-inputs s)
     ;; CO
     (link1$step co-inputs co)
     ;; DONE
     (link1$step done-inputs done)
     ;; Joint PISO2
     (piso2-sreg$step piso2-inputs piso2 data-width cnt-width)
     ;; Joint SIPO
     (sipo-sreg$step sipo-inputs sipo data-width cnt-width))))

(defthm len-of-serial-sub$step
  (equal (len (serial-sub$step inputs st data-width cnt-width))
         *serial-sub$st-len*))

(local
 (defthm len-cdr
   (implies (< 0 (len x))
            (equal (len (cdr x))
                   (1- (len x))))))

;; The state lemma for SERIAL-SUB

(defthm serial-sub$state
  (b* ((inputs (list* full-in empty-out-
                      (append data0-in data1-in go-signals))))
    (implies
     (and (serial-sub& netlist data-width cnt-width)
          (true-listp data0-in)
          (equal (len data0-in) data-width)
          (true-listp data1-in)
          (equal (len data1-in) data-width)
          (true-listp go-signals)
          (equal (len go-signals) *serial-sub$go-num*)
          (serial-sub$st-format st data-width cnt-width))
     (equal (de (si 'serial-sub data-width) inputs st netlist)
            (serial-sub$step inputs st data-width cnt-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'serial-sub data-width)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            serial-sub&
                            serial-sub*$destructure
                            serial-sub$data0-in
                            serial-sub$data1-in
                            serial-sub$piso2-inputs
                            serial-sub$sipo-inputs
                            serial-sub$st-format)
                           (de-module-disabled-rules)))))

(in-theory (disable serial-sub$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund serial-sub$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data0-in   (serial-sub$data0-in inputs data-width))
       (data1-in   (serial-sub$data1-in inputs data-width))
       (go-signals (nthcdr (serial-sub$data-ins-len data-width) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in)
         (and (bvp data0-in) (bvp data1-in)))
     (true-listp go-signals)
     (= (len go-signals) *serial-sub$go-num*)
     (equal inputs
            (list* full-in empty-out-
                   (append data0-in data1-in go-signals))))))

(local
 (defthm serial-sub$input-format=>piso2$input-format
   (implies (and (serial-sub$input-format inputs data-width)
                 (serial-sub$valid-st st data-width cnt-width))
            (piso2-sreg$input-format
             (serial-sub$piso2-inputs inputs st data-width)
             data-width))
   :hints (("Goal"
            :in-theory (e/d (piso2-sreg$input-format
                             piso2-sreg$data0-in
                             piso2-sreg$data1-in
                             serial-sub$input-format
                             serial-sub$valid-st
                             serial-sub$piso2-inputs)
                            (acl2::simplify-products-gather-exponents-<
                             nfix))))))

(local
 (defthm serial-sub$input-format=>sipo$input-format
   (implies (and (serial-sub$input-format inputs data-width)
                 (serial-sub$valid-st st data-width cnt-width))
            (sipo-sreg$input-format
             (serial-sub$sipo-inputs inputs st data-width)))
   :hints (("Goal"
            :in-theory (e/d (bvp
                             sipo-sreg$input-format
                             sipo-sreg$bit-in
                             serial-sub$input-format
                             serial-sub$valid-st
                             serial-sub$sipo-inputs)
                            (nfix))))))

(defthm booleanp-serial-sub$in-act
  (implies (and (serial-sub$input-format inputs data-width)
                (serial-sub$valid-st st data-width cnt-width))
           (booleanp (serial-sub$in-act inputs st data-width)))
  :hints (("Goal"
           :use serial-sub$input-format=>piso2$input-format
           :in-theory (e/d (serial-sub$valid-st
                            serial-sub$in-act)
                           (serial-sub$input-format=>piso2$input-format
                            link1$valid-st))))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-serial-sub$out-act
  (implies (and (serial-sub$input-format inputs data-width)
                (serial-sub$valid-st st data-width cnt-width))
           (booleanp (serial-sub$out-act inputs st data-width)))
  :hints (("Goal"
           :use serial-sub$input-format=>sipo$input-format
           :in-theory (e/d (serial-sub$valid-st
                            serial-sub$out-act)
                           (serial-sub$input-format=>sipo$input-format
                            link1$valid-st))))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma serial-sub :sizes (data-width cnt-width))

;; ======================================================================

;; 3. Single-Step-Update Property

;; Specify the functionality of SERIAL-SUB

(defun serial-sub$op (c a b)
  (take (len a)
        (v-adder c a (v-not b))))

(defthm bvp-serial-sub$op
  (bvp (serial-sub$op c a b)))

(defthm len-serial-sub$op
  (equal (len (serial-sub$op c a b))
         (len a)))

(in-theory (disable serial-sub$op))

;; The operation of SERIAL-SUB over a data sequence

(defun serial-sub$op-map (x)
  (if (atom x)
      nil
    (cons (serial-sub$op t (caar x) (cdar x))
          (serial-sub$op-map (cdr x)))))

(defthm serial-sub$op-map-of-append
  (equal (serial-sub$op-map (append x y))
         (append (serial-sub$op-map x)
                 (serial-sub$op-map y))))

;; The extraction function for SERIAL-SUB that extracts the future
;; output sequence from the current state.

(defund serial-sub$extract (st data-width)
  (b* ((a (get-field *serial-sub$a* st))
       (b (get-field *serial-sub$b* st))
       (ci (get-field *serial-sub$ci* st))
       (s (get-field *serial-sub$s* st))
       (co (get-field *serial-sub$co* st))
       (piso2 (get-field *serial-sub$piso2* st))
       (sipo (get-field *serial-sub$sipo* st))

       (a.s (get-field *link1$s* a))
       (a.d (get-field *link1$d* a))
       (b.s (get-field *link1$s* b))
       (b.d (get-field *link1$d* b))
       (ci.s (get-field *link1$s* ci))
       (ci.d (get-field *link1$d* ci))
       (s.s (get-field *link1$s* s))
       (s.d (get-field *link1$d* s))
       (co.d (get-field *link1$d* co))

       (a.valid-d (if (fullp a.s) a.d nil))
       (b.valid-d (if (fullp b.s) b.d nil))
       (c (if (fullp ci.s) (car ci.d) (car co.d)))
       (s.valid-d (if (fullp s.s) s.d nil))
       (sipo0.valid-data (piso2-sreg$extract0 piso2))
       (sipo1.valid-data (piso2-sreg$extract1 piso2))
       (sipo.valid-data (sipo-sreg$extract sipo)))
    (cond
     ((equal (+ (len (append a.valid-d sipo0.valid-data))
                (len (append sipo.valid-data s.valid-d)))
             (* 2 data-width))
      (cond
       ((< (len (append sipo.valid-data s.valid-d))
           data-width)
        (list
         (serial-sub$op t
                        sipo0.valid-data
                        sipo1.valid-data)
         (append
          sipo.valid-data
          s.valid-d
          (list (b-xor3 c (car a.valid-d) (b-not (car b.valid-d)))))))
       ((equal (len (append sipo.valid-data s.valid-d))
               data-width)
        (list
         (serial-sub$op t
                        (append a.valid-d sipo0.valid-data)
                        (append b.valid-d sipo1.valid-data))
         (append sipo.valid-data s.valid-d)))
       (t (list
           (append s.valid-d
                   (serial-sub$op c
                                  (append a.valid-d sipo0.valid-data)
                                  (append b.valid-d sipo1.valid-data)))
           sipo.valid-data))))
     ((equal (+ (len (append a.valid-d sipo0.valid-data))
                (len (append sipo.valid-data s.valid-d)))
             data-width)
      (cond
       ((equal (len (append sipo.valid-data s.valid-d))
               0)
        (list (serial-sub$op t
                             (append a.valid-d sipo0.valid-data)
                             (append b.valid-d sipo1.valid-data))))
       ((< (len (append sipo.valid-data s.valid-d))
           data-width)
        (list
         (append
          sipo.valid-data
          s.valid-d
          (serial-sub$op c
                         (append a.valid-d sipo0.valid-data)
                         (append b.valid-d sipo1.valid-data)))))
       (t (list (append sipo.valid-data s.valid-d)))))
     (t nil))))

;; Specify and prove a state invariant

(progn
  (defund serial-sub$inv (st data-width)
    (b* ((a (get-field *serial-sub$a* st))
         (b (get-field *serial-sub$b* st))
         (ci (get-field *serial-sub$ci* st))
         (s (get-field *serial-sub$s* st))
         (co (get-field *serial-sub$co* st))
         (done (get-field *serial-sub$done* st))
         (piso2 (get-field *serial-sub$piso2* st))
         (sipo (get-field *serial-sub$sipo* st))

         (a.s (get-field *link1$s* a))
         (a.d (get-field *link1$d* a))
         (b.s (get-field *link1$s* b))
         (b.d (get-field *link1$d* b))
         (ci.s (get-field *link1$s* ci))
         (ci.d (get-field *link1$d* ci))
         (s.s (get-field *link1$s* s))
         (s.d (get-field *link1$d* s))
         (co.s (get-field *link1$s* co))
         (done.s (get-field *link1$s* done))
         (done.d (get-field *link1$d* done))

         (a.valid-d (if (fullp a.s) a.d nil))
         (b.valid-d (if (fullp b.s) b.d nil))
         (s.valid-d (if (fullp s.s) s.d nil))
         (sipo0.valid-data (piso2-sreg$extract0 piso2))
         (sipo1.valid-data (piso2-sreg$extract1 piso2))
         (sipo.valid-data (sipo-sreg$extract sipo)))
      (and (not (equal ci.s co.s))
           (or (emptyp ci.s) (emptyp done.s))
           (or (emptyp co.s)
               (not (equal s.s done.s)))
           (or (emptyp s.s) (fullp co.s))
           (not (and (fullp s.s) (fullp done.s)))
           (or (emptyp ci.s)
               (and (not (equal (len (append a.valid-d sipo0.valid-data))
                                0))
                    (not (equal (len (append a.valid-d sipo0.valid-data))
                                data-width)))
               (car ci.d))
           (or (emptyp done.s)
               (equal (car done.d)
                      (or (equal (len sipo.valid-data)
                                 0)
                          (equal (len sipo.valid-data)
                                 data-width))))
           (equal (len (append a.valid-d sipo0.valid-data))
                  (len (append b.valid-d sipo1.valid-data)))
           (or (equal (+ (len (append a.valid-d sipo0.valid-data))
                         (len (append sipo.valid-data s.valid-d)))
                      0)
               (equal (+ (len (append a.valid-d sipo0.valid-data))
                         (len (append sipo.valid-data s.valid-d)))
                      data-width)
               (equal (+ (len (append a.valid-d sipo0.valid-data))
                         (len (append sipo.valid-data s.valid-d)))
                      (* 2 data-width)))
           (piso2-sreg$inv piso2)
           (sipo-sreg$inv sipo))))

  (defthm serial-sub$extract-not-empty
    (implies (and (serial-sub$out-act inputs st data-width)
                  (serial-sub$valid-st st data-width cnt-width)
                  (serial-sub$inv st data-width))
             (< 0 (len (serial-sub$extract st data-width))))
    :hints (("Goal"
             :in-theory (e/d (serial-sub$valid-st
                              serial-sub$inv
                              serial-sub$extract
                              serial-sub$out-act)
                             (b-gates
                              serial-sub$disabled-rules))))
    :rule-classes :linear)

  (local
   (defthm serial-sub$piso2-out0-act-inactive
     (b* ((a (nth *serial-sub$a* st))
          (a.s (nth *link1$s* a))
          (piso2-inputs (serial-sub$piso2-inputs inputs st data-width))
          (piso2 (nth *serial-sub$piso2* st)))
       (implies (fullp a.s)
                (not (piso2-sreg$out0-act piso2-inputs
                                                    piso2
                                                    data-width))))
     :hints (("Goal" :in-theory (enable get-field
                                        serial-sub$piso2-inputs)))))

  (local
   (defthm serial-sub$piso2-out1-act-inactive
     (b* ((b (nth *serial-sub$b* st))
          (b.s (nth *link1$s* b))
          (piso2-inputs (serial-sub$piso2-inputs inputs st data-width))
          (piso2 (nth *serial-sub$piso2* st)))
       (implies (fullp b.s)
                (not (piso2-sreg$out1-act piso2-inputs
                                                    piso2
                                                    data-width))))
     :hints (("Goal" :in-theory (enable get-field
                                        serial-sub$piso2-inputs)))))

  (local
   (defthm serial-sub$sipo-in-act-inactive
     (b* ((s (nth *serial-sub$s* st))
          (s.s (nth *link1$s* s))
          (done (nth *serial-sub$done* st))
          (done.s (nth *link1$s* done))
          (sipo-inputs (serial-sub$sipo-inputs inputs st data-width))
          (sipo (nth *serial-sub$sipo* st)))
       (implies (or (emptyp s.s)
                    (fullp done.s))
                (not (sipo-sreg$in-act sipo-inputs sipo))))
     :hints (("Goal" :in-theory (enable get-field
                                        serial-sub$sipo-inputs)))))

  (local
   (defthm v-to-nat-of-v-zp
     (equal (v-zp x)
            (equal (v-to-nat x) 0))
     :hints (("Goal" :in-theory (enable v-zp v-nzp v-to-nat)))))

  (local
   (defthm bvp-of-cdr-sipo-sreg$cnt-out
     (implies (and (sipo-sreg$valid-st st data-width cnt-width)
                   (sipo-sreg$in-act inputs st))
              (bvp (cdr (sipo-sreg$cnt-out st))))
     :hints (("Goal" :in-theory (enable f-and4
                                        bvp
                                        sipo-sreg$valid-st
                                        sipo-sreg$in-act
                                        sipo-sreg$cnt-out)))))

  (encapsulate
    ()

    (local
     (defthm v-to-nat-of-sipo-sreg$cnt-out
       (implies (and (sipo-sreg$in-act inputs st)
                     (sipo-sreg$valid-st st data-width cnt-width)
                     (sipo-sreg$inv st))
                (equal (v-to-nat (sipo-sreg$cnt-out st))
                       (- data-width
                          (len (sipo-sreg$extract st)))))
       :hints (("Goal" :in-theory (enable sipo-sreg$in-act
                                          sipo-sreg$valid-st
                                          sipo-sreg$inv
                                          sipo-sreg$cnt-out
                                          sipo-sreg$extract)))))

    (local
     (defthm v-to-nat-of-cdr
       (implies (< 0 (len x))
                (equal (v-to-nat (cdr x))
                       (/ (- (v-to-nat x)
                             (if (integerp (/ (v-to-nat x) 2)) 0 1))
                          2)))
       :hints (("Goal" :in-theory (enable v-to-nat)))))

    (local
     (defthm serial-sub$inv-preserved-aux
       (implies (and (equal (1+ x) y)
                     (integerp x))
                (not (integerp (+ (* 1/2 y) (* -1/2 x)))))))

    (defthm serial-sub$inv-preserved
      (implies (and (serial-sub$input-format inputs data-width)
                    (serial-sub$valid-st st data-width cnt-width)
                    (serial-sub$inv st data-width))
               (serial-sub$inv
                (serial-sub$step inputs st data-width cnt-width)
                data-width))
      :hints (("Goal"
               :use (serial-sub$input-format=>piso2$input-format
                     serial-sub$input-format=>sipo$input-format)
               :in-theory (e/d (get-field
                                f-sr
                                pos-len=>cons
                                sipo-sreg$valid-st=>constraints
                                piso2-sreg$extracted0-step
                                piso2-sreg$extracted1-step
                                sipo-sreg$extracted-step
                                serial-sub$valid-st
                                serial-sub$inv
                                serial-sub$step)
                               (serial-sub$input-format=>piso2$input-format
                                serial-sub$input-format=>sipo$input-format
                                sipo-sreg$out-act-inactive
                                serial-sub$disabled-rules)))))
    )
  )

;; The extracted next-state function for SERIAL-SUB.  Note that this function
;; avoids exploring the internal computation of SERIAL-SUB.

(defund serial-sub$extracted-step (inputs st data-width)
  (b* ((data0 (serial-sub$data0-in inputs data-width))
       (data1 (serial-sub$data1-in inputs data-width))
       (extracted-st (serial-sub$extract st data-width))
       (n (1- (len extracted-st))))
    (cond
     ((equal (serial-sub$out-act inputs st data-width) t)
      (cond
       ((equal (serial-sub$in-act inputs st data-width) t)
        (cons (serial-sub$op t data0 data1)
              (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (serial-sub$in-act inputs st data-width) t)
          (cons (serial-sub$op t data0 data1)
                extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm serial-sub-aux-1
     (b* ((piso2-inputs (serial-sub$piso2-inputs inputs st data-width)))
       (equal (piso2-sreg$data0-in piso2-inputs data-width)
              (serial-sub$data0-in inputs data-width)))
     :hints (("Goal" :in-theory (enable piso2-sreg$data0-in
                                        serial-sub$piso2-inputs
                                        serial-sub$data0-in)))))

  (local
   (defthm serial-sub-aux-2
     (b* ((piso2-inputs (serial-sub$piso2-inputs inputs st data-width)))
       (equal (piso2-sreg$data1-in piso2-inputs data-width)
              (serial-sub$data1-in inputs data-width)))
     :hints (("Goal" :in-theory (enable piso2-sreg$data1-in
                                        serial-sub$piso2-inputs
                                        serial-sub$data1-in)))))

  (local
   (defthm serial-sub-aux-3
     (b* ((s (get-field *serial-sub$s* st))
          (s.d (get-field *link1$d* s))
          (sipo-inputs (serial-sub$sipo-inputs inputs st data-width)))
       (equal (sipo-sreg$bit-in sipo-inputs)
              (f-buf (car s.d))))
     :hints (("Goal" :in-theory (enable sipo-sreg$bit-in
                                        serial-sub$sipo-inputs)))))

  (local
   (defthmd consp-is-pos-len
     (equal (consp x)
            (< 0 (len x)))))

  (local
   (defthm append-of-len-0
     (implies (equal (len x) 0)
              (equal (append x y) y))))

  (local
   (defthm append-of-len-1
     (implies (equal (len x) 1)
              (equal (append x y)
                     (cons (car x) y)))))

  (local
   (defthm nth-0-is-car
     (equal (nth 0 l)
            (car l))
     :hints (("Goal" :in-theory (enable nth)))))

  (defthm serial-sub$extracted-step-correct
    (b* ((next-st (serial-sub$step inputs st data-width cnt-width)))
      (implies (and (serial-sub$input-format inputs data-width)
                    (serial-sub$valid-st st data-width cnt-width)
                    (serial-sub$inv st data-width))
               (equal (serial-sub$extract next-st data-width)
                      (serial-sub$extracted-step inputs st data-width))))
    :hints (("Goal"
             :use (serial-sub$input-format=>piso2$input-format
                   serial-sub$input-format=>sipo$input-format)
             :in-theory (e/d (get-field
                              f-sr
                              list-rewrite-1
                              consp-is-pos-len
                              v-adder
                              v-not
                              sipo-sreg$valid-st=>constraints
                              piso2-sreg$extracted0-step
                              piso2-sreg$extracted1-step
                              sipo-sreg$extracted-step
                              serial-sub$extracted-step
                              serial-sub$valid-st
                              serial-sub$inv
                              serial-sub$step
                              serial-sub$in-act
                              serial-sub$out-act
                              serial-sub$extract
                              serial-sub$op)
                             (serial-sub$input-format=>piso2$input-format
                              serial-sub$input-format=>sipo$input-format
                              sipo-sreg$out-act-inactive
                              car-cdr-elim
                              serial-sub$disabled-rules)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that serial-sub$valid-st is an invariant.

(defthm serial-sub$valid-st-preserved
  (implies (and (serial-sub$input-format inputs data-width)
                (serial-sub$valid-st st data-width cnt-width))
           (serial-sub$valid-st
            (serial-sub$step inputs st data-width cnt-width)
            data-width
            cnt-width))
  :hints (("Goal"
           :use (serial-sub$input-format=>piso2$input-format
                 serial-sub$input-format=>sipo$input-format)
           :in-theory (e/d (get-field
                            f-sr
                            sipo-sreg$valid-st=>constraints
                            serial-sub$valid-st
                            serial-sub$step)
                           (serial-sub$input-format=>piso2$input-format
                            serial-sub$input-format=>sipo$input-format
                            b-gates
                            serial-sub$disabled-rules)))))

(defthm serial-sub$extract-lemma
  (implies (and (serial-sub$valid-st st data-width cnt-width)
                (serial-sub$inv st data-width)
                (serial-sub$out-act inputs st data-width))
           (equal (list (serial-sub$data-out st))
                  (nthcdr (1- (len (serial-sub$extract st data-width)))
                          (serial-sub$extract st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (get-field
                            serial-sub$valid-st
                            serial-sub$inv
                            serial-sub$extract
                            serial-sub$out-act
                            serial-sub$data-out)
                           (serial-sub$disabled-rules)))))

;; Extract the accepted input sequence

(seq-gen serial-sub in in-act 0
         (cons (serial-sub$data0-in inputs data-width)
               (serial-sub$data1-in inputs data-width))
         :sizes (data-width cnt-width))

;; Extract the valid output sequence

(seq-gen serial-sub out out-act 1
         (serial-sub$data-out st)
         :netlist-data (nthcdr 2 outputs)
         :sizes (data-width cnt-width))

;; The multi-step input-output relationship

(encapsulate
  ()

  (local
   (defthm serial-sub$dataflow-correct-aux
     (implies (equal (append x y1)
                     (append (serial-sub$op-map seq) y2))
              (equal (append x y1 z)
                     (append (serial-sub$op-map seq)
                             y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (associativity-of-append))))))

  (defthmd serial-sub$dataflow-correct
    (b* ((extracted-st (serial-sub$extract st data-width))
         (final-st (serial-sub$run
                    inputs-seq st data-width cnt-width n))
         (final-extracted-st (serial-sub$extract final-st data-width)))
      (implies
       (and (serial-sub$input-format-n inputs-seq data-width n)
            (serial-sub$valid-st st data-width cnt-width)
            (serial-sub$inv st data-width))
       (equal (append final-extracted-st
                      (serial-sub$out-seq
                       inputs-seq st data-width cnt-width n))
              (append (serial-sub$op-map
                       (serial-sub$in-seq
                        inputs-seq st data-width cnt-width n))
                      extracted-st))))
    :hints (("Goal"
             :in-theory (enable serial-sub$extracted-step))))

  (defthmd serial-sub$functionally-correct
    (b* ((extracted-st (serial-sub$extract st data-width))
         (final-st (de-n (si 'serial-sub data-width)
                         inputs-seq st netlist n))
         (final-extracted-st (serial-sub$extract final-st data-width)))
      (implies
       (and (serial-sub& netlist data-width cnt-width)
            (serial-sub$input-format-n inputs-seq data-width n)
            (serial-sub$valid-st st data-width cnt-width)
            (serial-sub$inv st data-width))
       (equal (append final-extracted-st
                      (serial-sub$netlist-out-seq
                       inputs-seq st netlist data-width n))
              (append (serial-sub$op-map
                       (serial-sub$netlist-in-seq
                        inputs-seq st netlist data-width n))
                      extracted-st))))
    :hints (("Goal"
             :use serial-sub$dataflow-correct
             :in-theory (enable serial-sub$valid-st=>st-format
                                serial-sub$de-n))))
  )

