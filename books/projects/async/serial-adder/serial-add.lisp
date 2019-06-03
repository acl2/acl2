;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "piso2-sreg")
(include-book "sipo-sreg")

(local (include-book "../list-rewrites"))

(local (include-book "arithmetic-5/top" :dir :system))

(local (in-theory (disable nth)))

(local
 (deftheory serial-add$disabled-rules
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
     take
     not
     default-car
     default-cdr
     true-listp
     bv-is-true-list)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of SERIAL-ADD
;;; 2. Multi-Step State Lemma
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of SERIAL-ADD
;;
;; Construct a DE module generator that generates self-timed serial adder
;; modules.  Prove the value and state lemmas for this module generator.

(defconst *serial-add$prim-go-num* 2)
(defconst *serial-add$go-num* (+ *serial-add$prim-go-num*
                                 *piso2-sreg$go-num*
                                 *sipo-sreg$go-num*))

(defun serial-add$data-ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (* 2 (mbe :logic (nfix data-size)
                 :exec  data-size))))

(defun serial-add$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ (serial-add$data-ins-len data-size)
     *serial-add$go-num*))

;; DE module generator of SERIAL-ADD

(module-generator
 serial-add* (data-size)
 (si 'serial-add data-size)
 (list* 'full-in 'empty-out-
        (append (sis 'data0-in 0 data-size)
                (sis 'data1-in 0 data-size)
                (sis 'go 0 *serial-add$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-size))
 '(a b ci s co done piso2 sipo)
 (list
  ;; LINKS
  ;; A
  '(a (a-status a-out)
      link1
      (piso2-out0-act add-act piso2-bit0-out))

  ;; B
  '(b (b-status b-out)
      link1
      (piso2-out1-act add-act piso2-bit1-out))

  ;; CI
  '(ci (ci-status ci-out)
       link1
       (c-buf-act add-act ci-in))

  ;; S
  '(s (s-status s-out)
      link1
      (add-act sipo-in-act s-in))

  ;; CO
  '(co (co-status co-out)
       link1
       (add-act c-buf-act co-in))

  ;; DONE
  '(done (done-status done-out)
         link1
         (sipo-in-act c-buf-act cnt-out=1))

  ;; JOINTS
  ;; PISO2
  (list 'piso2
        '(in-act piso2-out0-act piso2-out1-act
                 piso2-bit0-out piso2-bit1-out)
        (si 'piso2-sreg data-size)
        (list* 'full-in 'a-status 'b-status
               (append (sis 'data0-in 0 data-size)
                       (sis 'data1-in 0 data-size)
                       (sis 'go
                            *serial-add$prim-go-num*
                            *piso2-sreg$go-num*))))

  ;; SIPO
  '(g0 (done-status~) b-not (done-status))
  '(g1 (sipo-full-in) b-and (s-status done-status~))
  (list 'sipo
        (list* 'sipo-in-act 'out-act 'cnt-out=1 (sis 'data-out 0 data-size))
        (si 'sipo-sreg data-size)
        (list* 'sipo-full-in 'empty-out- 's-out
               (sis 'go
                    (+ *serial-add$prim-go-num*
                       *piso2-sreg$go-num*)
                    *sipo-sreg$go-num*)))

  ;; ADD
  '(g3 (add-full-in) b-and3 (a-status b-status ci-status))
  '(g4 (add-empty-out-) b-or (s-status co-status))
  (list 'add-cntl
        '(add-act)
        'joint-cntl
        (list 'add-full-in 'add-empty-out- (si 'go 0)))
  '(add-op (s-in co-in) full-adder (ci-out a-out b-out))

  ;; C-BUF
  '(g5 (low) vss ())
  '(g6 (c-buf-full-in) b-and (co-status done-status))
  (list 'c-buf-cntl
        '(c-buf-act)
        'joint-cntl
        (list 'c-buf-full-in 'ci-status (si 'go 1)))
  '(c-buf-op (ci-in) b-if (done-out low co-out)))

 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'serial-add
                           '(a b ci s co done piso2 sipo)
                           0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; SERIAL-ADD.

(defund serial-add$netlist (data-size cnt-size)
  (declare (xargs :guard (and (posp data-size)
                              (natp cnt-size)
                              (<= 3 cnt-size))))
  (cons (serial-add* data-size)
        (union$ (link1$netlist)
                (piso2-sreg$netlist data-size cnt-size)
                (sipo-sreg$netlist data-size cnt-size)
                :test 'equal)))

;; Recognizer for SERIAL-ADD

(defund serial-add& (netlist data-size cnt-size)
  (declare (xargs :guard (and (alistp netlist)
                              (posp data-size)
                              (natp cnt-size)
                              (<= 3 cnt-size))))
  (b* ((subnetlist (delete-to-eq (si 'serial-add data-size) netlist)))
    (and (equal (assoc (si 'serial-add data-size) netlist)
                (serial-add* data-size))
         (link1& subnetlist)
         (joint-cntl& subnetlist)
         (full-adder& subnetlist)
         (piso2-sreg& subnetlist data-size cnt-size)
         (sipo-sreg& subnetlist data-size cnt-size))))

;; Sanity check

(local
 (defthmd check-serial-add$netlist-64-7
   (and (net-syntax-okp (serial-add$netlist 64 7))
        (net-arity-okp (serial-add$netlist 64 7))
        (serial-add& (serial-add$netlist 64 7) 64 7))))

;; Constraints on the state of SERIAL-ADD

(defund serial-add$st-format (st data-size cnt-size)
  (b* ((piso2 (nth *serial-add$piso2* st))
       (sipo (nth *serial-add$sipo* st)))
    (and (piso2-sreg$st-format piso2 data-size cnt-size)
         (sipo-sreg$st-format sipo data-size cnt-size))))

(defthm serial-add$st-format=>constraint
  (implies (serial-add$st-format st data-size cnt-size)
           (and (posp data-size)
                (natp cnt-size)
                (<= 4 cnt-size)))
  :hints (("Goal" :in-theory (enable serial-add$st-format)))
  :rule-classes :forward-chaining)

(defund serial-add$valid-st (st data-size cnt-size)
  (b* ((a (nth *serial-add$a* st))
       (b (nth *serial-add$b* st))
       (ci (nth *serial-add$ci* st))
       (s (nth *serial-add$s* st))
       (co (nth *serial-add$co* st))
       (done (nth *serial-add$done* st))
       (piso2 (nth *serial-add$piso2* st))
       (sipo (nth *serial-add$sipo* st)))
    (and (link1$valid-st a)
         (link1$valid-st b)
         (link1$valid-st ci)
         (link1$valid-st s)
         (link1$valid-st co)
         (link1$valid-st done)
         (piso2-sreg$valid-st piso2 data-size cnt-size)
         (sipo-sreg$valid-st sipo data-size cnt-size))))

(defthmd serial-add$valid-st=>constraint
  (implies (serial-add$valid-st st data-size cnt-size)
           (and (natp data-size)
                (<= 8 data-size)
                (natp cnt-size)
                (<= 4 cnt-size)))
  :hints (("Goal"
           :in-theory (enable sipo-sreg$valid-st=>constraint
                              serial-add$valid-st)))
  :rule-classes :forward-chaining)

(defthmd serial-add$valid-st=>st-format
  (implies (serial-add$valid-st st data-size cnt-size)
           (serial-add$st-format st data-size cnt-size))
  :hints (("Goal" :in-theory (enable piso2-sreg$valid-st=>st-format
                                     sipo-sreg$valid-st=>st-format
                                     serial-add$st-format
                                     serial-add$valid-st))))

;; Extract the input and output signals for SERIAL-ADD

(progn
  ;; Extract the 1st input operand

  (defun serial-add$data0-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (take (mbe :logic (nfix data-size)
               :exec  data-size)
          (nthcdr 2 inputs)))

  (defthm len-serial-add$data0-in
    (equal (len (serial-add$data0-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable serial-add$data0-in))

  ;; Extract the 2nd input operand

  (defun serial-add$data1-in (inputs data-size)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-size))))
    (b* ((size (mbe :logic (nfix data-size)
                     :exec  data-size)))
      (take size
            (nthcdr (+ 2 size) inputs))))

  (defthm len-serial-add$data1-in
    (equal (len (serial-add$data1-in inputs data-size))
           (nfix data-size)))

  (in-theory (disable serial-add$data1-in))

  ;; Extract the inputs for joint PISO2

  (defund serial-add$piso2-inputs (inputs st data-size)
    (b* ((full-in0 (nth 0 inputs))
         (data0-in (serial-add$data0-in inputs data-size))
         (data1-in (serial-add$data1-in inputs data-size))
         (go-signals (nthcdr (serial-add$data-ins-len data-size) inputs))

         (piso2-go-signals (take *piso2-sreg$go-num*
                                  (nthcdr *serial-add$prim-go-num*
                                          go-signals)))

         (a (nth *serial-add$a* st))
         (a.s (nth *link1$s* a))
         (b (nth *serial-add$b* st))
         (b.s (nth *link1$s* b)))

      (list* full-in0 (f-buf (car a.s)) (f-buf (car b.s))
             (append data0-in data1-in piso2-go-signals))))

  ;; Extract the inputs for joint SIPO

  (defund serial-add$sipo-inputs (inputs st data-size)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (serial-add$data-ins-len data-size) inputs))

         (sipo-go-signals (take *sipo-sreg$go-num*
                                (nthcdr (+ *serial-add$prim-go-num*
                                           *piso2-sreg$go-num*)
                                        go-signals)))

         (s (nth *serial-add$s* st))
         (s.s (nth *link1$s* s))
         (s.d (nth *link1$d* s))
         (done (nth *serial-add$done* st))
         (done.s (nth *link1$s* done))

         (sipo-full-in (f-and (car s.s) (f-not (car done.s)))))

      (list* sipo-full-in empty-out- (f-buf (car s.d))
             sipo-go-signals)))

  ;; Extract the "in-act" signal

  (defund serial-add$in-act (inputs st data-size)
    (b* ((piso2-inputs (serial-add$piso2-inputs inputs st data-size))
         (piso2 (nth *serial-add$piso2* st)))
      (piso2-sreg$in-act piso2-inputs piso2 data-size)))

  (defthm serial-add$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (serial-add$in-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable serial-add$piso2-inputs
                                       serial-add$in-act))))

  ;; Extract the "out-act" signal

  (defund serial-add$out-act (inputs st data-size)
    (b* ((sipo-inputs (serial-add$sipo-inputs inputs st data-size))
         (sipo (nth *serial-add$sipo* st)))
      (sipo-sreg$out-act sipo-inputs sipo)))

  (defthm serial-add$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (serial-add$out-act inputs st data-size)))
    :hints (("Goal" :in-theory (enable serial-add$sipo-inputs
                                       serial-add$out-act))))

  ;; Extract the output data

  (defund serial-add$data-out (st)
    (b* ((sipo (nth *serial-add$sipo* st)))
      (sipo-sreg$data-out sipo)))

  (defthm len-serial-add$data-out-1
    (implies (serial-add$st-format st data-size cnt-size)
             (equal (len (serial-add$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable serial-add$st-format
                                       serial-add$data-out))))

  (defthm len-serial-add$data-out-2
    (implies (serial-add$valid-st st data-size cnt-size)
             (equal (len (serial-add$data-out st))
                    data-size))
    :hints (("Goal" :in-theory (enable serial-add$valid-st
                                       serial-add$data-out))))

  (defthm bvp-serial-add$data-out
    (implies (and (serial-add$valid-st st data-size cnt-size)
                  (serial-add$out-act inputs st data-size))
             (bvp (serial-add$data-out st)))
    :hints (("Goal" :in-theory (e/d (serial-add$valid-st
                                     serial-add$out-act
                                     serial-add$data-out)
                                    (sipo-sreg$extract-lemma)))))

  (defun serial-add$outputs (inputs st data-size)
    (list* (serial-add$in-act inputs st data-size)
           (serial-add$out-act inputs st data-size)
           (serial-add$data-out st)))
  )

;; The value lemma for SERIAL-ADD

(defthm serial-add$value
  (b* ((inputs (list* full-in empty-out-
                      (append data0-in data1-in go-signals))))
    (implies (and (serial-add& netlist data-size cnt-size)
                  (true-listp data0-in)
                  (equal (len data0-in) data-size)
                  (true-listp data1-in)
                  (equal (len data1-in) data-size)
                  (true-listp go-signals)
                  (equal (len go-signals) *serial-add$go-num*)
                  (serial-add$st-format st data-size cnt-size))
             (equal (se (si 'serial-add data-size) inputs st netlist)
                    (serial-add$outputs inputs st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (se (si 'serial-add data-size)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            serial-add&
                            serial-add*$destructure
                            serial-add$data0-in
                            serial-add$data1-in
                            serial-add$piso2-inputs
                            serial-add$sipo-inputs
                            serial-add$st-format
                            serial-add$in-act
                            serial-add$out-act
                            serial-add$data-out)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of SERIAL-ADD.

(defun serial-add$step (inputs st data-size cnt-size)
  (b* ((go-signals (nthcdr (serial-add$data-ins-len data-size)
                           inputs))
       (go-add (nth 0 go-signals))
       (go-c-buf (nth 1 go-signals))

       (a (nth *serial-add$a* st))
       (b (nth *serial-add$b* st))
       (ci (nth *serial-add$ci* st))
       (s (nth *serial-add$s* st))
       (co (nth *serial-add$co* st))
       (done (nth *serial-add$done* st))
       (piso2 (nth *serial-add$piso2* st))
       (sipo (nth *serial-add$sipo* st))

       (piso2-inputs (serial-add$piso2-inputs inputs st data-size))
       (sipo-inputs (serial-add$sipo-inputs inputs st data-size))

       (a.s (nth *link1$s* a))
       (a.d (nth *link1$d* a))
       (b.s (nth *link1$s* b))
       (b.d (nth *link1$d* b))
       (ci.s (nth *link1$s* ci))
       (ci.d (nth *link1$d* ci))
       (s.s (nth *link1$s* s))
       (co.s (nth *link1$s* co))
       (co.d (nth *link1$d* co))
       (done.s (nth *link1$s* done))
       (done.d (nth *link1$d* done))

       (piso2-out0-act
        (piso2-sreg$out0-act piso2-inputs piso2 data-size))
       (piso2-out1-act
        (piso2-sreg$out1-act piso2-inputs piso2 data-size))
       (piso2-bit0-out (piso2-sreg$bit0-out piso2))
       (piso2-bit1-out (piso2-sreg$bit1-out piso2))
       (sipo-in-act
        (sipo-sreg$in-act sipo-inputs sipo))
       (cnt-out=1 (sipo-sreg$cnt-out=1 sipo))
       (add-act (joint-act (f-and3 (car a.s) (car b.s) (car ci.s))
                           (f-or (car s.s) (car co.s))
                           go-add))
       (s-in (f-xor3 (car ci.d) (car a.d) (car b.d)))
       (co-in (f-or (f-and (car a.d) (car b.d))
                    (f-and (f-xor (car a.d) (car b.d)) (car ci.d))))
       (c-buf-act (joint-act (f-and (car co.s) (car done.s))
                             (car ci.s)
                             go-c-buf))
       (ci-in (f-if (car done.d) nil (car co.d)))

       (a-inputs (list piso2-out0-act add-act piso2-bit0-out))
       (b-inputs (list piso2-out1-act add-act piso2-bit1-out))
       (ci-inputs (list c-buf-act add-act ci-in))
       (s-inputs (list add-act sipo-in-act s-in))
       (co-inputs (list add-act c-buf-act co-in))
       (done-inputs (list sipo-in-act c-buf-act cnt-out=1)))
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
     (piso2-sreg$step piso2-inputs piso2 data-size cnt-size)
     ;; Joint SIPO
     (sipo-sreg$step sipo-inputs sipo data-size cnt-size))))

;; The state lemma for SERIAL-ADD

(defthm serial-add$state
  (b* ((inputs (list* full-in empty-out-
                      (append data0-in data1-in go-signals))))
    (implies
     (and (serial-add& netlist data-size cnt-size)
          (true-listp data0-in)
          (equal (len data0-in) data-size)
          (true-listp data1-in)
          (equal (len data1-in) data-size)
          (true-listp go-signals)
          (equal (len go-signals) *serial-add$go-num*)
          (serial-add$st-format st data-size cnt-size))
     (equal (de (si 'serial-add data-size) inputs st netlist)
            (serial-add$step inputs st data-size cnt-size))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-size)
                          (de (si 'serial-add data-size)
                              inputs st netlist))
           :in-theory (e/d (de-rules
                            serial-add&
                            serial-add*$destructure
                            serial-add$data0-in
                            serial-add$data1-in
                            serial-add$piso2-inputs
                            serial-add$sipo-inputs
                            serial-add$st-format)
                           (de-module-disabled-rules)))))

(in-theory (disable serial-add$step))

;; ======================================================================

;; 2. Multi-Step State Lemma

;; Conditions on the inputs

(defund serial-add$input-format (inputs data-size)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-size))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data0-in   (serial-add$data0-in inputs data-size))
       (data1-in   (serial-add$data1-in inputs data-size))
       (go-signals (nthcdr (serial-add$data-ins-len data-size) inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in)
         (and (bvp data0-in) (bvp data1-in)))
     (true-listp go-signals)
     (= (len go-signals) *serial-add$go-num*)
     (equal inputs
            (list* full-in empty-out-
                   (append data0-in data1-in go-signals))))))

(local
 (defthm serial-add$input-format=>piso2$input-format
   (implies (and (serial-add$input-format inputs data-size)
                 (serial-add$valid-st st data-size cnt-size))
            (piso2-sreg$input-format
             (serial-add$piso2-inputs inputs st data-size)
             data-size))
   :hints (("Goal"
            :in-theory (e/d (piso2-sreg$input-format
                             piso2-sreg$data0-in
                             piso2-sreg$data1-in
                             serial-add$input-format
                             serial-add$valid-st
                             serial-add$piso2-inputs)
                            (acl2::simplify-products-gather-exponents-<
                             nfix))))))

(local
 (defthm serial-add$input-format=>sipo$input-format
   (implies (and (serial-add$input-format inputs data-size)
                 (serial-add$valid-st st data-size cnt-size))
            (sipo-sreg$input-format
             (serial-add$sipo-inputs inputs st data-size)))
   :hints (("Goal"
            :in-theory (e/d (bvp
                             sipo-sreg$input-format
                             sipo-sreg$bit-in
                             serial-add$input-format
                             serial-add$valid-st
                             serial-add$sipo-inputs)
                            (nfix))))))

(defthm booleanp-serial-add$in-act
  (implies (and (serial-add$input-format inputs data-size)
                (serial-add$valid-st st data-size cnt-size))
           (booleanp (serial-add$in-act inputs st data-size)))
  :hints (("Goal"
           :use serial-add$input-format=>piso2$input-format
           :in-theory (e/d (serial-add$valid-st
                            serial-add$in-act)
                           (serial-add$input-format=>piso2$input-format
                            link1$valid-st))))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-serial-add$out-act
  (implies (and (serial-add$input-format inputs data-size)
                (serial-add$valid-st st data-size cnt-size))
           (booleanp (serial-add$out-act inputs st data-size)))
  :hints (("Goal"
           :use serial-add$input-format=>sipo$input-format
           :in-theory (e/d (serial-add$valid-st
                            serial-add$out-act)
                           (serial-add$input-format=>sipo$input-format
                            link1$valid-st))))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma serial-add :sizes (data-size cnt-size))

;; ======================================================================

;; 3. Single-Step-Update Property

;; The operation of SERIAL-ADD over a data sequence

(defun serial-add$op-map (x)
  (if (atom x)
      nil
    (cons (v-adder-output nil (caar x) (cdar x))
          (serial-add$op-map (cdr x)))))

(defthm serial-add$op-map-of-append
  (equal (serial-add$op-map (append x y))
         (append (serial-add$op-map x)
                 (serial-add$op-map y))))

;; The extraction function for SERIAL-ADD that extracts the future output
;; sequence from the current state.

(defund serial-add$extract (st data-size)
  (b* ((a (nth *serial-add$a* st))
       (b (nth *serial-add$b* st))
       (ci (nth *serial-add$ci* st))
       (s (nth *serial-add$s* st))
       (co (nth *serial-add$co* st))
       (piso2 (nth *serial-add$piso2* st))
       (sipo (nth *serial-add$sipo* st))

       (a.s (nth *link1$s* a))
       (a.d (nth *link1$d* a))
       (b.s (nth *link1$s* b))
       (b.d (nth *link1$d* b))
       (ci.s (nth *link1$s* ci))
       (ci.d (nth *link1$d* ci))
       (s.s (nth *link1$s* s))
       (s.d (nth *link1$d* s))
       (co.d (nth *link1$d* co))

       (a.valid-d (if (fullp a.s) a.d nil))
       (b.valid-d (if (fullp b.s) b.d nil))
       (c (if (fullp ci.s) (car ci.d) (car co.d)))
       (s.valid-d (if (fullp s.s) s.d nil))
       (piso0.valid-d (piso2-sreg$extract0 piso2))
       (piso1.valid-d (piso2-sreg$extract1 piso2))
       (sipo.valid-d (sipo-sreg$extract sipo))
       (in0 (append a.valid-d piso0.valid-d))
       (in1 (append b.valid-d piso1.valid-d))
       (out (append sipo.valid-d s.valid-d)))
    (cond
     ((equal (+ (len in0) (len out))
             (* 2 data-size))
      (cond
       ((< (len out) data-size)
        (list (v-adder-output nil piso0.valid-d piso1.valid-d)
              (append
               out
               (list (b-xor3 c (car a.valid-d) (car b.valid-d))))))
       ((equal (len out) data-size)
        (list (v-adder-output nil in0 in1)
              out))
       (t (list (append s.valid-d
                        (v-adder-output c in0 in1))
                sipo.valid-d))))
     ((equal (+ (len in0) (len out))
             data-size)
      (cond
       ((equal (len out) 0)
        (list (v-adder-output nil in0 in1)))
       ((< (len out) data-size)
        (list (append out
                      (v-adder-output c in0 in1))))
       (t (list out))))
     (t nil))))

;; Specify and prove a state invariant

(progn
  (defund serial-add$inv (st data-size)
    (b* ((a (nth *serial-add$a* st))
         (b (nth *serial-add$b* st))
         (ci (nth *serial-add$ci* st))
         (s (nth *serial-add$s* st))
         (co (nth *serial-add$co* st))
         (done (nth *serial-add$done* st))
         (piso2 (nth *serial-add$piso2* st))
         (sipo (nth *serial-add$sipo* st))

         (a.s (nth *link1$s* a))
         (a.d (nth *link1$d* a))
         (b.s (nth *link1$s* b))
         (b.d (nth *link1$d* b))
         (ci.s (nth *link1$s* ci))
         (ci.d (nth *link1$d* ci))
         (s.s (nth *link1$s* s))
         (s.d (nth *link1$d* s))
         (co.s (nth *link1$s* co))
         (done.s (nth *link1$s* done))
         (done.d (nth *link1$d* done))

         (a.valid-d (if (fullp a.s) a.d nil))
         (b.valid-d (if (fullp b.s) b.d nil))
         (s.valid-d (if (fullp s.s) s.d nil))
         (piso0.valid-d (piso2-sreg$extract0 piso2))
         (piso1.valid-d (piso2-sreg$extract1 piso2))
         (sipo.valid-d (sipo-sreg$extract sipo))
         (in0 (append a.valid-d piso0.valid-d))
         (in1 (append b.valid-d piso1.valid-d))
         (out (append sipo.valid-d s.valid-d)))
      (and (not (equal ci.s co.s))
           (or (emptyp ci.s) (emptyp done.s))
           (or (emptyp co.s)
               (not (equal s.s done.s)))
           (or (emptyp s.s)
               (and (fullp co.s) (emptyp done.s)))
           (or (emptyp ci.s)
               (and (not (equal (len in0) 0))
                    (not (equal (len in0) data-size)))
               (not (car ci.d)))
           (or (emptyp done.s)
               (equal (car done.d)
                      (or (equal (len sipo.valid-d) 0)
                          (equal (len sipo.valid-d) data-size))))
           (equal (len in0) (len in1))
           (or (equal (+ (len in0) (len out))
                      0)
               (equal (+ (len in0) (len out))
                      data-size)
               (equal (+ (len in0) (len out))
                      (* 2 data-size)))
           (piso2-sreg$inv piso2)
           (sipo-sreg$inv sipo))))

  (defthm serial-add$extract-not-empty
    (implies (and (serial-add$out-act inputs st data-size)
                  (serial-add$valid-st st data-size cnt-size)
                  (serial-add$inv st data-size))
             (< 0 (len (serial-add$extract st data-size))))
    :hints (("Goal"
             :in-theory (e/d (serial-add$valid-st
                              serial-add$inv
                              serial-add$extract
                              serial-add$out-act)
                             (b-gates
                              serial-add$disabled-rules))))
    :rule-classes :linear)

  (local
   (defthm serial-add$piso2-out0-act-inactive
     (b* ((a (nth *serial-add$a* st))
          (a.s (nth *link1$s* a))
          (piso2-inputs (serial-add$piso2-inputs inputs st data-size))
          (piso2 (nth *serial-add$piso2* st)))
       (implies (fullp a.s)
                (not (piso2-sreg$out0-act piso2-inputs
                                          piso2
                                          data-size))))
     :hints (("Goal" :in-theory (enable serial-add$piso2-inputs)))))

  (local
   (defthm serial-add$piso2-out1-act-inactive
     (b* ((b (nth *serial-add$b* st))
          (b.s (nth *link1$s* b))
          (piso2-inputs (serial-add$piso2-inputs inputs st data-size))
          (piso2 (nth *serial-add$piso2* st)))
       (implies (fullp b.s)
                (not (piso2-sreg$out1-act piso2-inputs
                                          piso2
                                          data-size))))
     :hints (("Goal" :in-theory (enable serial-add$piso2-inputs)))))

  (local
   (defthm serial-add$sipo-in-act-inactive
     (b* ((s (nth *serial-add$s* st))
          (s.s (nth *link1$s* s))
          (done (nth *serial-add$done* st))
          (done.s (nth *link1$s* done))
          (sipo-inputs (serial-add$sipo-inputs inputs st data-size))
          (sipo (nth *serial-add$sipo* st)))
       (implies (or (emptyp s.s)
                    (fullp done.s))
                (not (sipo-sreg$in-act sipo-inputs sipo))))
     :hints (("Goal" :in-theory (enable serial-add$sipo-inputs)))))

  (local
   (defthm v-to-nat-of-v-zp
     (equal (v-zp x)
            (equal (v-to-nat x) 0))
     :hints (("Goal" :in-theory (enable v-zp v-nzp v-to-nat)))))

  (local
   (defthm len-cdr
     (implies (< 0 (len x))
              (equal (len (cdr x))
                     (1- (len x))))))

  (encapsulate
    ()

    (local
     (defthm sipo-sreg$cnt-out=1-rewrite
       (implies (and (sipo-sreg$in-act inputs st)
                     (sipo-sreg$valid-st st data-size cnt-size)
                     (sipo-sreg$inv st))
                (equal (sipo-sreg$cnt-out=1 st)
                       (equal (len (sipo-sreg$extract st))
                              (1- data-size))))
       :hints (("Goal" :in-theory (enable bvp
                                          v-to-nat
                                          sipo-sreg$in-act
                                          sipo-sreg$valid-st
                                          sipo-sreg$inv
                                          sipo-sreg$cnt-out=1
                                          sipo-sreg$extract)))))

    (defthm serial-add$inv-preserved
      (implies (and (serial-add$input-format inputs data-size)
                    (serial-add$valid-st st data-size cnt-size)
                    (serial-add$inv st data-size))
               (serial-add$inv
                (serial-add$step inputs st data-size cnt-size)
                data-size))
      :hints (("Goal"
               :use (serial-add$input-format=>piso2$input-format
                     serial-add$input-format=>sipo$input-format)
               :in-theory (e/d (f-sr
                                pos-len=>cons
                                sipo-sreg$valid-st=>constraint
                                piso2-sreg$extracted0-step
                                piso2-sreg$extracted1-step
                                sipo-sreg$extracted-step
                                serial-add$valid-st
                                serial-add$inv
                                serial-add$step)
                               (serial-add$input-format=>piso2$input-format
                                serial-add$input-format=>sipo$input-format
                                sipo-sreg$out-act-inactive
                                serial-add$disabled-rules)))))
    )
  )

;; The extracted next-state function for SERIAL-ADD.  Note that this function
;; avoids exploring the internal computation of SERIAL-ADD.

(defund serial-add$extracted-step (inputs st data-size)
  (b* ((data0 (serial-add$data0-in inputs data-size))
       (data1 (serial-add$data1-in inputs data-size))
       (extracted-st (serial-add$extract st data-size))
       (n (1- (len extracted-st))))
    (cond
     ((equal (serial-add$out-act inputs st data-size) t)
      (cond
       ((equal (serial-add$in-act inputs st data-size) t)
        (cons (v-adder-output nil data0 data1)
              (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (serial-add$in-act inputs st data-size) t)
          (cons (v-adder-output nil data0 data1)
                extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm serial-add-aux-1
     (b* ((piso2-inputs (serial-add$piso2-inputs inputs st data-size)))
       (equal (piso2-sreg$data0-in piso2-inputs data-size)
              (serial-add$data0-in inputs data-size)))
     :hints (("Goal" :in-theory (enable piso2-sreg$data0-in
                                        serial-add$piso2-inputs
                                        serial-add$data0-in)))))

  (local
   (defthm serial-add-aux-2
     (b* ((piso2-inputs (serial-add$piso2-inputs inputs st data-size)))
       (equal (piso2-sreg$data1-in piso2-inputs data-size)
              (serial-add$data1-in inputs data-size)))
     :hints (("Goal" :in-theory (enable piso2-sreg$data1-in
                                        serial-add$piso2-inputs
                                        serial-add$data1-in)))))

  (local
   (defthm serial-add-aux-3
     (b* ((s (nth *serial-add$s* st))
          (s.d (nth *link1$d* s))
          (sipo-inputs (serial-add$sipo-inputs inputs st data-size)))
       (equal (sipo-sreg$bit-in sipo-inputs)
              (f-buf (car s.d))))
     :hints (("Goal" :in-theory (enable sipo-sreg$bit-in
                                        serial-add$sipo-inputs)))))

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

  (defthm serial-add$extracted-step-correct
    (b* ((next-st (serial-add$step inputs st data-size cnt-size)))
      (implies (and (serial-add$input-format inputs data-size)
                    (serial-add$valid-st st data-size cnt-size)
                    (serial-add$inv st data-size))
               (equal (serial-add$extract next-st data-size)
                      (serial-add$extracted-step inputs st data-size))))
    :hints (("Goal"
             :use (serial-add$input-format=>piso2$input-format
                   serial-add$input-format=>sipo$input-format)
             :in-theory (e/d (f-sr
                              list-rewrite-1
                              consp-is-pos-len
                              v-adder
                              v-adder-output
                              sipo-sreg$valid-st=>constraint
                              piso2-sreg$extracted0-step
                              piso2-sreg$extracted1-step
                              sipo-sreg$extracted-step
                              serial-add$extracted-step
                              serial-add$valid-st
                              serial-add$inv
                              serial-add$step
                              serial-add$in-act
                              serial-add$out-act
                              serial-add$extract)
                             (serial-add$input-format=>piso2$input-format
                              serial-add$input-format=>sipo$input-format
                              sipo-sreg$out-act-inactive
                              car-cdr-elim
                              serial-add$disabled-rules)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

;; Prove that serial-add$valid-st is an invariant.

(defthm serial-add$valid-st-preserved
  (implies (and (serial-add$input-format inputs data-size)
                (serial-add$valid-st st data-size cnt-size))
           (serial-add$valid-st
            (serial-add$step inputs st data-size cnt-size)
            data-size
            cnt-size))
  :hints (("Goal"
           :use (serial-add$input-format=>piso2$input-format
                 serial-add$input-format=>sipo$input-format)
           :in-theory (e/d (f-sr
                            sipo-sreg$valid-st=>constraint
                            serial-add$valid-st
                            serial-add$step)
                           (serial-add$input-format=>piso2$input-format
                            serial-add$input-format=>sipo$input-format
                            b-gates
                            serial-add$disabled-rules)))))

(defthm serial-add$extract-lemma
  (implies (and (serial-add$valid-st st data-size cnt-size)
                (serial-add$inv st data-size)
                (serial-add$out-act inputs st data-size))
           (equal (list (serial-add$data-out st))
                  (nthcdr (1- (len (serial-add$extract st data-size)))
                          (serial-add$extract st data-size))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (serial-add$valid-st
                            serial-add$inv
                            serial-add$extract
                            serial-add$out-act
                            serial-add$data-out)
                           (serial-add$disabled-rules)))))

;; Extract the accepted input sequence

(seq-gen serial-add in in-act 0
         (cons (serial-add$data0-in inputs data-size)
               (serial-add$data1-in inputs data-size))
         :sizes (data-size cnt-size))

;; Extract the valid output sequence

(seq-gen serial-add out out-act 1
         (serial-add$data-out st)
         :netlist-data (nthcdr 2 outputs)
         :sizes (data-size cnt-size))

;; The multi-step input-output relationship

(encapsulate
  ()

  (local
   (defthm serial-add$dataflow-correct-aux
     (implies (equal (append x y1)
                     (append (serial-add$op-map seq) y2))
              (equal (append x y1 z)
                     (append (serial-add$op-map seq)
                             y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (associativity-of-append))))))

  (defthmd serial-add$dataflow-correct
    (b* ((extracted-st (serial-add$extract st data-size))
         (final-st (serial-add$run
                    inputs-seq st data-size cnt-size n))
         (final-extracted-st (serial-add$extract final-st data-size)))
      (implies
       (and (serial-add$input-format-n inputs-seq data-size n)
            (serial-add$valid-st st data-size cnt-size)
            (serial-add$inv st data-size))
       (equal (append final-extracted-st
                      (serial-add$out-seq
                       inputs-seq st data-size cnt-size n))
              (append (serial-add$op-map
                       (serial-add$in-seq
                        inputs-seq st data-size cnt-size n))
                      extracted-st))))
    :hints (("Goal"
             :in-theory (enable serial-add$extracted-step))))

  (defthmd serial-add$functionally-correct
    (b* ((extracted-st (serial-add$extract st data-size))
         (final-st (de-n (si 'serial-add data-size)
                         inputs-seq st netlist n))
         (final-extracted-st (serial-add$extract final-st data-size)))
      (implies
       (and (serial-add& netlist data-size cnt-size)
            (serial-add$input-format-n inputs-seq data-size n)
            (serial-add$valid-st st data-size cnt-size)
            (serial-add$inv st data-size))
       (equal (append final-extracted-st
                      (serial-add$out-seq-netlist
                       inputs-seq st netlist data-size n))
              (append (serial-add$op-map
                       (serial-add$in-seq-netlist
                        inputs-seq st netlist data-size n))
                      extracted-st))))
    :hints (("Goal"
             :use serial-add$dataflow-correct
             :in-theory (enable serial-add$valid-st=>st-format
                                serial-add$de-n))))
  )
