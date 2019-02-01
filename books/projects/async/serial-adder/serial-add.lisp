;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; December 2018

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
     take-redefinition
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
(defconst *serial-add$st-len* 8)

(defun serial-add$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun serial-add$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (serial-add$data-ins-len data-width)
     *serial-add$go-num*))

;; DE module generator of SERIAL-ADD

(module-generator
 serial-add* (data-width)
 (si 'serial-add data-width)
 (list* 'full-in 'empty-out-
        (append (sis 'data0-in 0 data-width)
                (sis 'data1-in 0 data-width)
                (sis 'go 0 *serial-add$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-width))
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
        (si 'piso2-sreg data-width)
        (list* 'full-in 'a-status 'b-status
               (append (sis 'data0-in 0 data-width)
                       (sis 'data1-in 0 data-width)
                       (sis 'go
                            *serial-add$prim-go-num*
                            *piso2-sreg$go-num*))))

  ;; SIPO
  '(g0 (done-status~) b-not (done-status))
  '(g1 (sipo-full-in) b-and (s-status done-status~))
  (list 'sipo
        (list* 'sipo-in-act 'out-act 'cnt-out=1 (sis 'data-out 0 data-width))
        (si 'sipo-sreg data-width)
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

 (declare (xargs :guard (natp data-width))))

(make-event
 `(progn
    ,@(state-accessors-gen 'serial-add
                           '(a b ci s co done piso2 sipo)
                           0)))

;; DE netlist generator.  A generated netlist will contain an instance of
;; SERIAL-ADD.

(defund serial-add$netlist (data-width cnt-width)
  (declare (xargs :guard (and (posp data-width)
                              (natp cnt-width)
                              (<= 3 cnt-width))))
  (cons (serial-add* data-width)
        (union$ (link1$netlist)
                (piso2-sreg$netlist data-width cnt-width)
                (sipo-sreg$netlist data-width cnt-width)
                :test 'equal)))

;; Recognizer for SERIAL-ADD

(defund serial-add& (netlist data-width cnt-width)
  (declare (xargs :guard (and (alistp netlist)
                              (posp data-width)
                              (natp cnt-width)
                              (<= 3 cnt-width))))
  (b* ((subnetlist (delete-to-eq (si 'serial-add data-width) netlist)))
    (and (equal (assoc (si 'serial-add data-width) netlist)
                (serial-add* data-width))
         (link1& subnetlist)
         (joint-cntl& subnetlist)
         (full-adder& subnetlist)
         (piso2-sreg& subnetlist data-width cnt-width)
         (sipo-sreg& subnetlist data-width cnt-width))))

;; Sanity check

(local
 (defthmd check-serial-add$netlist-64-7
   (and (net-syntax-okp (serial-add$netlist 64 7))
        (net-arity-okp (serial-add$netlist 64 7))
        (serial-add& (serial-add$netlist 64 7) 64 7))))

;; Constraints on the state of SERIAL-ADD

(defund serial-add$st-format (st data-width cnt-width)
  (b* ((piso2 (get-field *serial-add$piso2* st))
       (sipo (get-field *serial-add$sipo* st)))
    (and (piso2-sreg$st-format piso2 data-width cnt-width)
         (sipo-sreg$st-format sipo data-width cnt-width))))

(defthm serial-add$st-format=>constraint
  (implies (serial-add$st-format st data-width cnt-width)
           (and (posp data-width)
                (natp cnt-width)
                (<= 4 cnt-width)))
  :hints (("Goal" :in-theory (enable serial-add$st-format)))
  :rule-classes :forward-chaining)

(defund serial-add$valid-st (st data-width cnt-width)
  (b* ((a (get-field *serial-add$a* st))
       (b (get-field *serial-add$b* st))
       (ci (get-field *serial-add$ci* st))
       (s (get-field *serial-add$s* st))
       (co (get-field *serial-add$co* st))
       (done (get-field *serial-add$done* st))
       (piso2 (get-field *serial-add$piso2* st))
       (sipo (get-field *serial-add$sipo* st)))
    (and (link1$valid-st a)
         (link1$valid-st b)
         (link1$valid-st ci)
         (link1$valid-st s)
         (link1$valid-st co)
         (link1$valid-st done)
         (piso2-sreg$valid-st piso2 data-width cnt-width)
         (sipo-sreg$valid-st sipo data-width cnt-width))))

(defthmd serial-add$valid-st=>constraint
  (implies (serial-add$valid-st st data-width cnt-width)
           (and (natp data-width)
                (<= 8 data-width)
                (natp cnt-width)
                (<= 4 cnt-width)))
  :hints (("Goal"
           :in-theory (enable sipo-sreg$valid-st=>constraint
                              serial-add$valid-st)))
  :rule-classes :forward-chaining)

(defthmd serial-add$valid-st=>st-format
  (implies (serial-add$valid-st st data-width cnt-width)
           (serial-add$st-format st data-width cnt-width))
  :hints (("Goal" :in-theory (enable piso2-sreg$valid-st=>st-format
                                     sipo-sreg$valid-st=>st-format
                                     serial-add$st-format
                                     serial-add$valid-st))))

;; Extract the input and output signals for SERIAL-ADD

(progn
  ;; Extract the 1st input operand

  (defun serial-add$data0-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (take (mbe :logic (nfix data-width)
               :exec  data-width)
          (nthcdr 2 inputs)))

  (defthm len-serial-add$data0-in
    (equal (len (serial-add$data0-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable serial-add$data0-in))

  ;; Extract the 2nd input operand

  (defun serial-add$data1-in (inputs data-width)
    (declare (xargs :guard (and (true-listp inputs)
                                (natp data-width))))
    (b* ((width (mbe :logic (nfix data-width)
                     :exec  data-width)))
      (take width
            (nthcdr (+ 2 width) inputs))))

  (defthm len-serial-add$data1-in
    (equal (len (serial-add$data1-in inputs data-width))
           (nfix data-width)))

  (in-theory (disable serial-add$data1-in))

  ;; Extract the inputs for joint PISO2

  (defund serial-add$piso2-inputs (inputs st data-width)
    (b* ((full-in0 (nth 0 inputs))
         (data0-in (serial-add$data0-in inputs data-width))
         (data1-in (serial-add$data1-in inputs data-width))
         (go-signals (nthcdr (serial-add$data-ins-len data-width) inputs))

         (piso2-go-signals (take *piso2-sreg$go-num*
                                  (nthcdr *serial-add$prim-go-num*
                                          go-signals)))

         (a (get-field *serial-add$a* st))
         (a.s (get-field *link1$s* a))
         (b (get-field *serial-add$b* st))
         (b.s (get-field *link1$s* b)))

      (list* full-in0 (f-buf (car a.s)) (f-buf (car b.s))
             (append data0-in data1-in piso2-go-signals))))

  ;; Extract the inputs for joint SIPO

  (defund serial-add$sipo-inputs (inputs st data-width)
    (b* ((empty-out- (nth 1 inputs))
         (go-signals (nthcdr (serial-add$data-ins-len data-width) inputs))

         (sipo-go-signals (take *sipo-sreg$go-num*
                                (nthcdr (+ *serial-add$prim-go-num*
                                           *piso2-sreg$go-num*)
                                        go-signals)))

         (s (get-field *serial-add$s* st))
         (s.s (get-field *link1$s* s))
         (s.d (get-field *link1$d* s))
         (done (get-field *serial-add$done* st))
         (done.s (get-field *link1$s* done))

         (sipo-full-in (f-and (car s.s) (f-not (car done.s)))))

      (list* sipo-full-in empty-out- (f-buf (car s.d))
             sipo-go-signals)))

  ;; Extract the "in-act" signal

  (defund serial-add$in-act (inputs st data-width)
    (b* ((piso2-inputs (serial-add$piso2-inputs inputs st data-width))
         (piso2 (get-field *serial-add$piso2* st)))
      (piso2-sreg$in-act piso2-inputs piso2 data-width)))

  (defthm serial-add$in-act-inactive
    (implies (not (nth 0 inputs))
             (not (serial-add$in-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable serial-add$piso2-inputs
                                       serial-add$in-act))))

  ;; Extract the "out-act" signal

  (defund serial-add$out-act (inputs st data-width)
    (b* ((sipo-inputs (serial-add$sipo-inputs inputs st data-width))
         (sipo (get-field *serial-add$sipo* st)))
      (sipo-sreg$out-act sipo-inputs sipo)))

  (defthm serial-add$out-act-inactive
    (implies (equal (nth 1 inputs) t)
             (not (serial-add$out-act inputs st data-width)))
    :hints (("Goal" :in-theory (enable serial-add$sipo-inputs
                                       serial-add$out-act))))

  ;; Extract the output data

  (defund serial-add$data-out (st)
    (b* ((sipo (get-field *serial-add$sipo* st)))
      (sipo-sreg$data-out sipo)))

  (defthm len-serial-add$data-out-1
    (implies (serial-add$st-format st data-width cnt-width)
             (equal (len (serial-add$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable serial-add$st-format
                                       serial-add$data-out))))

  (defthm len-serial-add$data-out-2
    (implies (serial-add$valid-st st data-width cnt-width)
             (equal (len (serial-add$data-out st))
                    data-width))
    :hints (("Goal" :in-theory (enable serial-add$valid-st
                                       serial-add$data-out))))

  (defthm bvp-serial-add$data-out
    (implies (and (serial-add$valid-st st data-width cnt-width)
                  (serial-add$out-act inputs st data-width))
             (bvp (serial-add$data-out st)))
    :hints (("Goal" :in-theory (e/d (serial-add$valid-st
                                     serial-add$out-act
                                     serial-add$data-out)
                                    (sipo-sreg$extract-lemma)))))

  (defun serial-add$outputs (inputs st data-width)
    (list* (serial-add$in-act inputs st data-width)
           (serial-add$out-act inputs st data-width)
           (serial-add$data-out st)))
  )

;; The value lemma for SERIAL-ADD

(defthm serial-add$value
  (b* ((inputs (list* full-in empty-out-
                      (append data0-in data1-in go-signals))))
    (implies (and (serial-add& netlist data-width cnt-width)
                  (true-listp data0-in)
                  (equal (len data0-in) data-width)
                  (true-listp data1-in)
                  (equal (len data1-in) data-width)
                  (true-listp go-signals)
                  (equal (len go-signals) *serial-add$go-num*)
                  (serial-add$st-format st data-width cnt-width))
             (equal (se (si 'serial-add data-width) inputs st netlist)
                    (serial-add$outputs inputs st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (se (si 'serial-add data-width)
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

(defun serial-add$step (inputs st data-width cnt-width)
  (b* ((go-signals (nthcdr (serial-add$data-ins-len data-width)
                           inputs))
       (go-add (nth 0 go-signals))
       (go-c-buf (nth 1 go-signals))

       (a (get-field *serial-add$a* st))
       (b (get-field *serial-add$b* st))
       (ci (get-field *serial-add$ci* st))
       (s (get-field *serial-add$s* st))
       (co (get-field *serial-add$co* st))
       (done (get-field *serial-add$done* st))
       (piso2 (get-field *serial-add$piso2* st))
       (sipo (get-field *serial-add$sipo* st))

       (piso2-inputs (serial-add$piso2-inputs inputs st data-width))
       (sipo-inputs (serial-add$sipo-inputs inputs st data-width))

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
     (piso2-sreg$step piso2-inputs piso2 data-width cnt-width)
     ;; Joint SIPO
     (sipo-sreg$step sipo-inputs sipo data-width cnt-width))))

(defthm len-of-serial-add$step
  (equal (len (serial-add$step inputs st data-width cnt-width))
         *serial-add$st-len*))

;; The state lemma for SERIAL-ADD

(defthm serial-add$state
  (b* ((inputs (list* full-in empty-out-
                      (append data0-in data1-in go-signals))))
    (implies
     (and (serial-add& netlist data-width cnt-width)
          (true-listp data0-in)
          (equal (len data0-in) data-width)
          (true-listp data1-in)
          (equal (len data1-in) data-width)
          (true-listp go-signals)
          (equal (len go-signals) *serial-add$go-num*)
          (serial-add$st-format st data-width cnt-width))
     (equal (de (si 'serial-add data-width) inputs st netlist)
            (serial-add$step inputs st data-width cnt-width))))
  :hints (("Goal"
           :do-not-induct t
           :expand (:free (inputs data-width)
                          (de (si 'serial-add data-width)
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

(defund serial-add$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data0-in   (serial-add$data0-in inputs data-width))
       (data1-in   (serial-add$data1-in inputs data-width))
       (go-signals (nthcdr (serial-add$data-ins-len data-width) inputs)))
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
   (implies (and (serial-add$input-format inputs data-width)
                 (serial-add$valid-st st data-width cnt-width))
            (piso2-sreg$input-format
             (serial-add$piso2-inputs inputs st data-width)
             data-width))
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
   (implies (and (serial-add$input-format inputs data-width)
                 (serial-add$valid-st st data-width cnt-width))
            (sipo-sreg$input-format
             (serial-add$sipo-inputs inputs st data-width)))
   :hints (("Goal"
            :in-theory (e/d (bvp
                             sipo-sreg$input-format
                             sipo-sreg$bit-in
                             serial-add$input-format
                             serial-add$valid-st
                             serial-add$sipo-inputs)
                            (nfix))))))

(defthm booleanp-serial-add$in-act
  (implies (and (serial-add$input-format inputs data-width)
                (serial-add$valid-st st data-width cnt-width))
           (booleanp (serial-add$in-act inputs st data-width)))
  :hints (("Goal"
           :use serial-add$input-format=>piso2$input-format
           :in-theory (e/d (serial-add$valid-st
                            serial-add$in-act)
                           (serial-add$input-format=>piso2$input-format
                            link1$valid-st))))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-serial-add$out-act
  (implies (and (serial-add$input-format inputs data-width)
                (serial-add$valid-st st data-width cnt-width))
           (booleanp (serial-add$out-act inputs st data-width)))
  :hints (("Goal"
           :use serial-add$input-format=>sipo$input-format
           :in-theory (e/d (serial-add$valid-st
                            serial-add$out-act)
                           (serial-add$input-format=>sipo$input-format
                            link1$valid-st))))
  :rule-classes (:rewrite :type-prescription))

(simulate-lemma serial-add :sizes (data-width cnt-width))

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

(defund serial-add$extract (st data-width)
  (b* ((a (get-field *serial-add$a* st))
       (b (get-field *serial-add$b* st))
       (ci (get-field *serial-add$ci* st))
       (s (get-field *serial-add$s* st))
       (co (get-field *serial-add$co* st))
       (piso2 (get-field *serial-add$piso2* st))
       (sipo (get-field *serial-add$sipo* st))

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
       (piso0.valid-d (piso2-sreg$extract0 piso2))
       (piso1.valid-d (piso2-sreg$extract1 piso2))
       (sipo.valid-d (sipo-sreg$extract sipo)))
    (cond
     ((equal (+ (len (append a.valid-d piso0.valid-d))
                (len (append sipo.valid-d s.valid-d)))
             (* 2 data-width))
      (cond
       ((< (len (append sipo.valid-d s.valid-d))
           data-width)
        (list
         (v-adder-output nil
                         piso0.valid-d
                         piso1.valid-d)
         (append
          sipo.valid-d
          s.valid-d
          (list (b-xor3 c (car a.valid-d) (car b.valid-d))))))
       ((equal (len (append sipo.valid-d s.valid-d))
               data-width)
        (list
         (v-adder-output nil
                         (append a.valid-d piso0.valid-d)
                         (append b.valid-d piso1.valid-d))
         (append sipo.valid-d s.valid-d)))
       (t (list
           (append s.valid-d
                   (v-adder-output c
                                   (append a.valid-d piso0.valid-d)
                                   (append b.valid-d piso1.valid-d)))
           sipo.valid-d))))
     ((equal (+ (len (append a.valid-d piso0.valid-d))
                (len (append sipo.valid-d s.valid-d)))
             data-width)
      (cond
       ((equal (len (append sipo.valid-d s.valid-d))
               0)
        (list (v-adder-output nil
                              (append a.valid-d piso0.valid-d)
                              (append b.valid-d piso1.valid-d))))
       ((< (len (append sipo.valid-d s.valid-d))
           data-width)
        (list
         (append
          sipo.valid-d
          s.valid-d
          (v-adder-output c
                          (append a.valid-d piso0.valid-d)
                          (append b.valid-d piso1.valid-d)))))
       (t (list (append sipo.valid-d s.valid-d)))))
     (t nil))))

;; Specify and prove a state invariant

(progn
  (defund serial-add$inv (st data-width)
    (b* ((a (get-field *serial-add$a* st))
         (b (get-field *serial-add$b* st))
         (ci (get-field *serial-add$ci* st))
         (s (get-field *serial-add$s* st))
         (co (get-field *serial-add$co* st))
         (done (get-field *serial-add$done* st))
         (piso2 (get-field *serial-add$piso2* st))
         (sipo (get-field *serial-add$sipo* st))

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
         (piso0.valid-d (piso2-sreg$extract0 piso2))
         (piso1.valid-d (piso2-sreg$extract1 piso2))
         (sipo.valid-d (sipo-sreg$extract sipo)))
      (and (not (equal ci.s co.s))
           (or (emptyp ci.s) (emptyp done.s))
           (or (emptyp co.s)
               (not (equal s.s done.s)))
           (or (emptyp s.s) (fullp co.s))
           (not (and (fullp s.s) (fullp done.s)))
           (or (emptyp ci.s)
               (and (not (equal (len (append a.valid-d piso0.valid-d))
                                0))
                    (not (equal (len (append a.valid-d piso0.valid-d))
                                data-width)))
               (not (car ci.d)))
           (or (emptyp done.s)
               (equal (car done.d)
                      (or (equal (len sipo.valid-d)
                                 0)
                          (equal (len sipo.valid-d)
                                 data-width))))
           (equal (len (append a.valid-d piso0.valid-d))
                  (len (append b.valid-d piso1.valid-d)))
           (or (equal (+ (len (append a.valid-d piso0.valid-d))
                         (len (append sipo.valid-d s.valid-d)))
                      0)
               (equal (+ (len (append a.valid-d piso0.valid-d))
                         (len (append sipo.valid-d s.valid-d)))
                      data-width)
               (equal (+ (len (append a.valid-d piso0.valid-d))
                         (len (append sipo.valid-d s.valid-d)))
                      (* 2 data-width)))
           (piso2-sreg$inv piso2)
           (sipo-sreg$inv sipo))))

  (defthm serial-add$extract-not-empty
    (implies (and (serial-add$out-act inputs st data-width)
                  (serial-add$valid-st st data-width cnt-width)
                  (serial-add$inv st data-width))
             (< 0 (len (serial-add$extract st data-width))))
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
          (piso2-inputs (serial-add$piso2-inputs inputs st data-width))
          (piso2 (nth *serial-add$piso2* st)))
       (implies (fullp a.s)
                (not (piso2-sreg$out0-act piso2-inputs
                                          piso2
                                          data-width))))
     :hints (("Goal" :in-theory (enable get-field
                                        serial-add$piso2-inputs)))))

  (local
   (defthm serial-add$piso2-out1-act-inactive
     (b* ((b (nth *serial-add$b* st))
          (b.s (nth *link1$s* b))
          (piso2-inputs (serial-add$piso2-inputs inputs st data-width))
          (piso2 (nth *serial-add$piso2* st)))
       (implies (fullp b.s)
                (not (piso2-sreg$out1-act piso2-inputs
                                          piso2
                                          data-width))))
     :hints (("Goal" :in-theory (enable get-field
                                        serial-add$piso2-inputs)))))

  (local
   (defthm serial-add$sipo-in-act-inactive
     (b* ((s (nth *serial-add$s* st))
          (s.s (nth *link1$s* s))
          (done (nth *serial-add$done* st))
          (done.s (nth *link1$s* done))
          (sipo-inputs (serial-add$sipo-inputs inputs st data-width))
          (sipo (nth *serial-add$sipo* st)))
       (implies (or (emptyp s.s)
                    (fullp done.s))
                (not (sipo-sreg$in-act sipo-inputs sipo))))
     :hints (("Goal" :in-theory (enable get-field
                                        serial-add$sipo-inputs)))))

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
                     (sipo-sreg$valid-st st data-width cnt-width)
                     (sipo-sreg$inv st))
                (equal (sipo-sreg$cnt-out=1 st)
                       (equal (len (sipo-sreg$extract st))
                              (1- data-width))))
       :hints (("Goal" :in-theory (enable bvp
                                          v-to-nat
                                          sipo-sreg$in-act
                                          sipo-sreg$valid-st
                                          sipo-sreg$inv
                                          sipo-sreg$cnt-out=1
                                          sipo-sreg$extract)))))

    (defthm serial-add$inv-preserved
      (implies (and (serial-add$input-format inputs data-width)
                    (serial-add$valid-st st data-width cnt-width)
                    (serial-add$inv st data-width))
               (serial-add$inv
                (serial-add$step inputs st data-width cnt-width)
                data-width))
      :hints (("Goal"
               :use (serial-add$input-format=>piso2$input-format
                     serial-add$input-format=>sipo$input-format)
               :in-theory (e/d (get-field
                                f-sr
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

(defund serial-add$extracted-step (inputs st data-width)
  (b* ((data0 (serial-add$data0-in inputs data-width))
       (data1 (serial-add$data1-in inputs data-width))
       (extracted-st (serial-add$extract st data-width))
       (n (1- (len extracted-st))))
    (cond
     ((equal (serial-add$out-act inputs st data-width) t)
      (cond
       ((equal (serial-add$in-act inputs st data-width) t)
        (cons (v-adder-output nil data0 data1)
              (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (serial-add$in-act inputs st data-width) t)
          (cons (v-adder-output nil data0 data1)
                extracted-st))
         (t extracted-st))))))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm serial-add-aux-1
     (b* ((piso2-inputs (serial-add$piso2-inputs inputs st data-width)))
       (equal (piso2-sreg$data0-in piso2-inputs data-width)
              (serial-add$data0-in inputs data-width)))
     :hints (("Goal" :in-theory (enable piso2-sreg$data0-in
                                        serial-add$piso2-inputs
                                        serial-add$data0-in)))))

  (local
   (defthm serial-add-aux-2
     (b* ((piso2-inputs (serial-add$piso2-inputs inputs st data-width)))
       (equal (piso2-sreg$data1-in piso2-inputs data-width)
              (serial-add$data1-in inputs data-width)))
     :hints (("Goal" :in-theory (enable piso2-sreg$data1-in
                                        serial-add$piso2-inputs
                                        serial-add$data1-in)))))

  (local
   (defthm serial-add-aux-3
     (b* ((s (get-field *serial-add$s* st))
          (s.d (get-field *link1$d* s))
          (sipo-inputs (serial-add$sipo-inputs inputs st data-width)))
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
    (b* ((next-st (serial-add$step inputs st data-width cnt-width)))
      (implies (and (serial-add$input-format inputs data-width)
                    (serial-add$valid-st st data-width cnt-width)
                    (serial-add$inv st data-width))
               (equal (serial-add$extract next-st data-width)
                      (serial-add$extracted-step inputs st data-width))))
    :hints (("Goal"
             :use (serial-add$input-format=>piso2$input-format
                   serial-add$input-format=>sipo$input-format)
             :in-theory (e/d (get-field
                              f-sr
                              list-rewrite-1
                              consp-is-pos-len
                              v-adder
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
                              serial-add$extract
                              v-adder-output)
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
  (implies (and (serial-add$input-format inputs data-width)
                (serial-add$valid-st st data-width cnt-width))
           (serial-add$valid-st
            (serial-add$step inputs st data-width cnt-width)
            data-width
            cnt-width))
  :hints (("Goal"
           :use (serial-add$input-format=>piso2$input-format
                 serial-add$input-format=>sipo$input-format)
           :in-theory (e/d (get-field
                            f-sr
                            sipo-sreg$valid-st=>constraint
                            serial-add$valid-st
                            serial-add$step)
                           (serial-add$input-format=>piso2$input-format
                            serial-add$input-format=>sipo$input-format
                            b-gates
                            serial-add$disabled-rules)))))

(defthm serial-add$extract-lemma
  (implies (and (serial-add$valid-st st data-width cnt-width)
                (serial-add$inv st data-width)
                (serial-add$out-act inputs st data-width))
           (equal (list (serial-add$data-out st))
                  (nthcdr (1- (len (serial-add$extract st data-width)))
                          (serial-add$extract st data-width))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (get-field
                            serial-add$valid-st
                            serial-add$inv
                            serial-add$extract
                            serial-add$out-act
                            serial-add$data-out)
                           (serial-add$disabled-rules)))))

;; Extract the accepted input sequence

(seq-gen serial-add in in-act 0
         (cons (serial-add$data0-in inputs data-width)
               (serial-add$data1-in inputs data-width))
         :sizes (data-width cnt-width))

;; Extract the valid output sequence

(seq-gen serial-add out out-act 1
         (serial-add$data-out st)
         :netlist-data (nthcdr 2 outputs)
         :sizes (data-width cnt-width))

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
    (b* ((extracted-st (serial-add$extract st data-width))
         (final-st (serial-add$run
                    inputs-seq st data-width cnt-width n))
         (final-extracted-st (serial-add$extract final-st data-width)))
      (implies
       (and (serial-add$input-format-n inputs-seq data-width n)
            (serial-add$valid-st st data-width cnt-width)
            (serial-add$inv st data-width))
       (equal (append final-extracted-st
                      (serial-add$out-seq
                       inputs-seq st data-width cnt-width n))
              (append (serial-add$op-map
                       (serial-add$in-seq
                        inputs-seq st data-width cnt-width n))
                      extracted-st))))
    :hints (("Goal"
             :in-theory (enable serial-add$extracted-step))))

  (defthmd serial-add$functionally-correct
    (b* ((extracted-st (serial-add$extract st data-width))
         (final-st (de-n (si 'serial-add data-width)
                         inputs-seq st netlist n))
         (final-extracted-st (serial-add$extract final-st data-width)))
      (implies
       (and (serial-add& netlist data-width cnt-width)
            (serial-add$input-format-n inputs-seq data-width n)
            (serial-add$valid-st st data-width cnt-width)
            (serial-add$inv st data-width))
       (equal (append final-extracted-st
                      (serial-add$netlist-out-seq
                       inputs-seq st netlist data-width n))
              (append (serial-add$op-map
                       (serial-add$netlist-in-seq
                        inputs-seq st netlist data-width n))
                      extracted-st))))
    :hints (("Goal"
             :use serial-add$dataflow-correct
             :in-theory (enable serial-add$valid-st=>st-format
                                serial-add$de-n))))
  )

