;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

(in-package "FM9001")

(include-book "control-modules")
(include-book "pre-alu")
(include-book "store-resultp")
(include-book "tv-if")
(include-book "v-inc4")
(include-book "vector-module")

;; ======================================================================

;; Some preliminary definitions.

;; SET-SOME-FLAGS

(defun set-some-flags (set-flags)
  (declare (xargs :guard (true-listp set-flags)))
  (or (z-set set-flags)
      (n-set set-flags)
      (v-set set-flags)
      (c-set set-flags)))

(defthm booleanp-set-some-flags
  (implies (bvp set-flags)
           (booleanp (set-some-flags set-flags)))
  :rule-classes :type-prescription)

(defthm not-set-some-flags-make-list-4
  (not (set-some-flags (make-list 4))))

(defun flags-hyps (flags)
  (declare (xargs :guard t))
  (and (equal (len flags) 4)
       (bvp flags)))

(defthm not-set-some-flags-update-flags
  (implies (and (flags-hyps flags)
                (not (set-some-flags set-flags)))
           (equal (update-flags flags set-flags cvzbv)
                  flags))
  :hints (("Goal"
           :use (:instance equal-len-4-as-collected-nth
                           (l flags))
           :in-theory (enable update-flags bvp
                              z-flag n-flag v-flag c-flag))))

(defun f$set-some-flags (set-flags)
  (declare (xargs :guard (true-listp set-flags)))
  (f-or4 (car set-flags)
         (cadr set-flags)
         (caddr set-flags)
         (cadddr set-flags)))

(defthm f$set-some-flags=set-some=flags
  (implies (and (bvp set-flags)
                (equal (len set-flags) 4))
           (equal (f$set-some-flags set-flags)
                  (set-some-flags set-flags)))
  :hints (("Goal"
           :in-theory (enable bvp
                              c-set v-set n-set z-set))))

(defthmd b-or4$value-as-f$set-some-flags
  (equal (se 'b-or4 set-flags sts netlist)
         (list (f$set-some-flags set-flags)))
  :hints (("Goal" :in-theory (enable se-rules))))

(in-theory (disable set-some-flags f$set-some-flags))

(defun f$all-t-regs-address (regs-address)
  (declare (xargs :guard (true-listp regs-address)))
  (f-and4 (car regs-address)
          (cadr regs-address)
          (caddr regs-address)
          (cadddr regs-address)))

(defthm f$all-t-regs-address=set-some=flags
  (implies (and (bvp regs-address)
                (equal (len regs-address) 4))
           (equal (f$all-t-regs-address regs-address)
                  (equal regs-address (make-list 4 :initial-element t))))
  :hints (("Goal"
           :in-theory (enable bvp))))

(defthmd b-and4$value-as-f$all-t-regs-address
  (equal (se 'b-and4 regs-address sts netlist)
         (list (f$all-t-regs-address regs-address)))
  :hints (("Goal" :in-theory (enable se-rules))))

(in-theory (disable f$all-t-regs-address))

;; CV-HYPS rw- regs-address i-reg flags pc-reg
;; The hyps that allow the CV_state functions to be opened nicely.

(defun cv-hyps (rw- regs-address i-reg flags pc-reg)
  (declare (xargs :guard t))
  (and (booleanp rw-)
       (equal (len regs-address) 4)
       (bvp regs-address)
       (equal (len i-reg) 32)
       (bvp i-reg)
       (flags-hyps flags)
       (equal (len pc-reg) 4)
       (bvp pc-reg)))

;; ======================================================================

;; Definitions of the control states for the FM9001 control logic.

(defconst *control-states*
  '((fetch0  . *v00000*)
    (fetch1  . *v00001*)
    (fetch2  . *v00010*)
    (fetch3  . *v00011*)

    (decode  . *v00100*)
    (rega    . *v00101*)
    (regb    . *v00110*)
    (update  . *v00111*)

    (reada0  . *v01000*)
    (reada1  . *v01001*)
    (reada2  . *v01010*)
    (reada3  . *v01011*)

    (readb0  . *v01100*)
    (readb1  . *v01101*)
    (readb2  . *v01110*)
    (readb3  . *v01111*)

    (write0  . *v10000*)
    (write1  . *v10001*)
    (write2  . *v10010*)
    (write3  . *v10011*)

    (sefa0   . *v10100*)
    (sefa1   . *v10101*)
    (sefb0   . *v10110*)
    (sefb1   . *v10111*)

    (hold0   . *v11000*)
    (hold1   . *v11001*)
    (v11010  . *v11010*)
    (v11011  . *v11011*)

    (reset0  . *v11100*)
    (reset1  . *v11101*)
    (reset2  . *v11110*)
    (v11111  . *v11111*)))

(defmacro define-control-states-events ()
  `(progn
     ,@(define-control-states *control-states*)

     (deftheory vector-states
       ',(add-prefix-to-state-names "V_" *control-states*))

     (deftheory natural-states
       ',(add-prefix-to-state-names "N_" *control-states*))

     (in-theory (disable vector-states natural-states))))

(define-control-states-events)

;; ======================================================================

;; The fields of the control vector are defined by *CONTROL-TEMPLATE*. We make
;; extensive use of this database to generate lemmas.

(defconst *control-template*
  ;; Line       Type (Bit/Vector)  Default
  '((rw-                 b          t)
    (strobe-             b          t)
    (hdack-              b          t)
    (we-regs             b          nil)
    (we-a-reg            b          nil)
    (we-b-reg            b          nil)
    (we-i-reg            b          nil)
    (we-data-out         b          nil)
    (we-addr-out         b          nil)
    (we-hold-            b          nil)
    (we-pc-reg           b          nil)
    (data-in-select      b          nil)
    (dec-addr-out        b          nil)
    (select-immediate    b          nil)
    (alu-c               b          (carry-in-help
                                     (cons c (cons nil op-code))))
    (alu-zero            b          nil)
    (major-state         5          *v00000*)
    (we-flags            4          (make-list 4))
    (regs-address        4          pc-reg)
    (alu-op              4          op-code)
    (alu-mpg             7          (mpg (cons nil (cons nil op-code))))))

(defmacro define-control-vector-accessors-events ()
 `(progn
    ,@(define-control-vector-accessors 0 *control-template*)

    (deftheory control-vector-accessors
      ',(strip-cars *control-template*))

    (in-theory (disable control-vector-accessors))))

(define-control-vector-accessors-events)

;; ======================================================================

;; *STATE-TABLE*, along with *CONTROL-TEMPLATE*, forms a Common LISP encoding
;; of the FM9001 state machine. Each entry contains the state name, an
;; expression for the next state, and a set of control line assignments. If the
;; name of a control line is given, then the non-default Boolean value is
;; selected. A pair, (<control-line> <value>) assigns that value to the control
;; line in that state.

(defconst *state-table*
  '((fetch0 fetch1 we-addr-out we-a-reg (regs-address pc-reg)
            (rw- rw-) we-hold-
            alu-zero
            (alu-op (alu-inc-op))
            (alu-c (carry-in-help (cons c (cons t (alu-inc-op)))))
            (alu-mpg (mpg (cons t (cons nil (alu-inc-op))))))

    (fetch1 (if hold- fetch2 hold0))

    (fetch2 fetch3 strobe-
            we-regs (regs-address pc-reg)
            (alu-c (carry-in-help (cons c (cons nil (alu-inc-op)))))
            (alu-op (alu-inc-op))
            (alu-mpg (mpg (cons nil (cons nil (alu-inc-op))))))

    (fetch3 (if dtack- fetch3 decode) data-in-select we-i-reg strobe-)

    (decode (if (b-or store set-some-flags)
                (if direct-a
                    (if (b-or direct-b unary)
                        rega
                      readb0)
                  reada0)
              (if side-effect-a
                  sefa0
                (if side-effect-b
                    sefb0
                  fetch0))))

    (rega (if direct-b (if unary update regb) (if store write0 update))
          (regs-address rn-a) (select-immediate a-immediate-p) we-a-reg)

    (regb update (regs-address rn-b) we-b-reg)

    (update (if (b-and side-effect-b unary) sefb1 fetch0)
            (regs-address rn-b) (we-regs store) (we-flags set-flags)
            we-b-reg)

    (reada0 reada1 (regs-address rn-a) we-a-reg we-addr-out
            (dec-addr-out pre-dec-a))

    (reada1 reada2
            (alu-c (if* pre-dec-a
                        (carry-in-help (cons c (cons nil (alu-dec-op))))
                        (carry-in-help (cons c (cons nil (alu-inc-op))))))
            (alu-op (if* pre-dec-a (alu-dec-op) (alu-inc-op)))
            (alu-mpg (if* pre-dec-a
                          (mpg (cons nil (cons nil (alu-dec-op))))
                          (mpg (cons nil (cons nil (alu-inc-op))))))
            (regs-address rn-a) (we-regs side-effect-a))

    (reada2 reada3 (regs-address rn-b) we-b-reg strobe-)

    (reada3 (if dtack-
                reada3
              (if direct-b
                  update
                (if unary
                    (if store write0 update)
                  readb0)))
            data-in-select we-a-reg strobe-)

    (readb0 readb1 (regs-address rn-b) we-addr-out
            (dec-addr-out pre-dec-b) we-b-reg)

    (readb1 readb2 (regs-address rn-a) (we-a-reg direct-a)
            (select-immediate a-immediate-p))

    (readb2 readb3
            (regs-address rn-b) (we-regs (and* store- side-effect-b))
            (alu-c (if* pre-dec-b
                        (carry-in-help (cons c (cons nil (alu-dec-op))))
                        (carry-in-help (cons c (cons nil (alu-inc-op))))))
            (alu-op (if* pre-dec-b (alu-dec-op) (alu-inc-op)))
            (alu-mpg (if* pre-dec-b
                          (mpg (cons nil (cons t (alu-dec-op))))
                          (mpg (cons nil (cons t (alu-inc-op))))))
            strobe-)

    (readb3 (if dtack- readb3 (if store write0 update))
            we-b-reg data-in-select strobe-)

    (write0 write1
            (we-flags set-flags) we-data-out
            (regs-address rn-b) we-b-reg we-addr-out
            (dec-addr-out pre-dec-b))

    (write1 write2
            (regs-address rn-b) (we-regs side-effect-b)
            (alu-c (if* pre-dec-b
                        (carry-in-help (cons c (cons nil (alu-dec-op))))
                        (carry-in-help (cons c (cons nil (alu-inc-op))))))
            (alu-op (if* pre-dec-b (alu-dec-op) (alu-inc-op)))
            (alu-mpg (if* pre-dec-b
                          (mpg (cons nil (cons t (alu-dec-op))))
                          (mpg (cons nil (cons t (alu-inc-op))))))
            rw-)

    (write2 write3 strobe- rw-)

    (write3 (if dtack- write3 fetch0) rw- strobe-)

    (sefa0 sefa1 (regs-address rn-a) we-a-reg)

    (sefa1 (if side-effect-b sefb0 fetch0)
           (regs-address rn-a) we-regs
           (alu-c (if* pre-dec-a
                       (carry-in-help (cons c (cons nil (alu-dec-op))))
                       (carry-in-help (cons c (cons nil (alu-inc-op))))))
           (alu-op (if* pre-dec-a (alu-dec-op) (alu-inc-op)))
           (alu-mpg (if* pre-dec-a
                         (mpg (cons nil (cons nil (alu-dec-op))))
                         (mpg (cons nil (cons nil (alu-inc-op)))))))

    (sefb0 sefb1 (regs-address rn-b) we-b-reg)

    (sefb1 fetch0
           (regs-address rn-b) we-regs
           (alu-c (if* pre-dec-b
                       (carry-in-help (cons c (cons nil (alu-dec-op))))
                       (carry-in-help (cons c (cons nil (alu-inc-op))))))
           (alu-op (if* pre-dec-b (alu-dec-op) (alu-inc-op)))
           (alu-mpg (if* pre-dec-b
                         (mpg (cons nil (cons t (alu-dec-op))))
                         (mpg (cons nil (cons t (alu-inc-op)))))))

    (hold0 (if hold- hold1 hold0) hdack- we-pc-reg we-hold-)

    (hold1 fetch0)

    (v11010 reset0) ; Illegal
    (v11011 reset0) ; Illegal

    ;; We use (ALU-INC-OP) as the default op-code during the reset sequence so
    ;; that the control vector will be completely defined.  Recall that the
    ;; OP-CODE is irrelevant to ALU operation when it is forced to zero.  Thu
    ;; Jul 18 11:33:55 1991 BB -- With new optimizations, we depend on the
    ;; OP-CODE being set to ALU-INC-OP during zeroing!  NB: All idiomatic
    ;; expressions are necessary for later proofs; cryptic comments being
    ;; especially opaque.

    (reset0 reset1
            (regs-address (make-list 4)) we-regs we-data-out
            (we-flags (make-list 4 :initial-element t)) we-pc-reg we-hold-
            alu-zero
            (alu-op (alu-inc-op))
            (alu-c (carry-in-help (cons c (cons t (alu-inc-op)))))
            (alu-mpg (mpg (cons t (cons nil (alu-inc-op))))))

    (reset1 reset2 (regs-address (make-list 4))
            we-addr-out we-a-reg we-b-reg we-i-reg
            alu-zero
            (alu-op (alu-inc-op))
            (alu-c (carry-in-help (cons c (cons t (alu-inc-op)))))
            (alu-mpg (mpg (cons t (cons nil (alu-inc-op))))))

    (reset2 (if all-t-regs-address fetch0 reset2)
            we-regs
            alu-zero
            (alu-op (alu-inc-op))
            (alu-c (carry-in-help (cons c (cons t (alu-inc-op)))))
            (alu-mpg (mpg (cons t (cons nil (alu-inc-op)))))
            (regs-address (v-inc regs-address)))

    (v11111 reset0))) ; Illegal

(defconst *control-arglist*
  '(RW- REGS-ADDRESS I-REG FLAGS PC-REG))

(defmacro define-control-vector-functions-events ()
 `(progn
    ,@(define-control-vector-functions *state-table*
                                       *control-template*
                                       *control-arglist*)

    (deftheory cv-states
      ',(add-prefix-to-state-names "CV_" *state-table*))

    (deftheory cv-states-destructures
      ',(add-prefix-and-suffix-to-state-names "CV_"
                                              "$DESTRUCTURE"
                                              *state-table*))

    (in-theory (disable cv-states cv-states-destructures))))

(define-control-vector-functions-events)

;; ======================================================================

;; CONTROL-LET

;; CONTROL-LET computes a number of intermediate results that are used both to
;; determine the next control state, and the values of the control lines.

(defun f$control-let (i-reg flags regs-address)
  (declare (xargs :guard (and (true-listp i-reg)
                              (true-listp flags)
                              (true-listp regs-address))))
  (b* ((a-immediate-p (a-immediate-p i-reg))
       (mode-a        (mode-a        i-reg))
       (?rn-a         (rn-a          i-reg))
       (mode-b        (mode-b        i-reg))
       (?rn-b         (rn-b          i-reg))
       (set-flags     (set-flags     i-reg))
       (store-cc      (store-cc      i-reg))
       (op-code       (op-code       i-reg)))
    (let
        ((a-immediate-p (identity a-immediate-p)))
      (let
          ((a-immediate-p- (f-not a-immediate-p))
           (store (f$b-store-resultp store-cc flags))
           (set-some-flags (f$set-some-flags set-flags))
           (decode-reg-a-mode (f$decode-reg-mode mode-a))
           (decode-reg-b-mode (f$decode-reg-mode mode-b)))
        (let
            ((almost-direct-a (car decode-reg-a-mode))
             (pre-dec-a (cadr decode-reg-a-mode))
             (almost-side-effect-a (caddr decode-reg-a-mode))
             (direct-b (car decode-reg-b-mode))
             (pre-dec-b (cadr decode-reg-b-mode))
             (side-effect-b (caddr decode-reg-b-mode))
             (unary (f$unary-op-code-p op-code))
             (c (identity (c-flag flags)))
             (all-t-regs-address (f$all-t-regs-address regs-address)))
          (let
              ((side-effect-a (f-and a-immediate-p- almost-side-effect-a))
               (direct-a (f-or a-immediate-p almost-direct-a)))
            (list a-immediate-p store set-some-flags direct-a direct-b unary
                  pre-dec-a pre-dec-b c all-t-regs-address
                  side-effect-a side-effect-b)))))))

(defun control-let* ()
  (declare (xargs :guard t))
  (let ((i-reg (sis 'i-reg 0 32))
        (flags (sis 'flags 0 4))
        (regs-address (sis 'regs-address 0 4)))
    (b* ((a-immediate-p (a-immediate-p i-reg))
         (mode-a        (mode-a        i-reg))
         (?rn-a         (rn-a          i-reg))
         (mode-b        (mode-b        i-reg))
         (?rn-b         (rn-b          i-reg))
         (set-flags     (set-flags     i-reg))
         (store-cc      (store-cc      i-reg))
         (op-code       (op-code       i-reg)))
      (list
       'control-let
       (append i-reg (append flags regs-address))
       '(a-immediate-p store set-some-flags direct-a direct-b unary
                       pre-dec-a pre-dec-b c all-t-regs-address
                       side-effect-a side-effect-b)
       nil
       (list
        (list 'g0 '(a-immediate-p) 'id (list a-immediate-p))
        (list 'g1 '(a-immediate-p-) 'b-not '(a-immediate-p))
        (list 'g2 '(store) 'b-store-resultp (append store-cc flags))
        (list 'g3 '(set-some-flags) 'b-or4 set-flags)
        (list 'g4 '(almost-direct-a pre-dec-a almost-side-effect-a)
              'decode-reg-mode mode-a)
        (list 'g5 '(direct-b pre-dec-b side-effect-b) 'decode-reg-mode mode-b)
        (list 'g6 '(unary) 'unary-op-code-p op-code)
        (list 'g7 '(c) 'id (list (c-flag flags)))
        (list 'g8 '(all-t-regs-address) 'b-and4 regs-address)
        (list 'g9 '(side-effect-a) 'b-and
              '(a-immediate-p- almost-side-effect-a))
        (list 'ga '(direct-a) 'b-or '(a-immediate-p almost-direct-a)))))))

(defund control-let& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (and (equal (assoc 'control-let netlist)
              (control-let*))
       (b* ((netlist (delete-to-eq 'control-let netlist)))
         (and (b-store-resultp& netlist)
              (decode-reg-mode& netlist)
              (unary-op-code-p& netlist)))))

(defun control-let$netlist ()
  (declare (xargs :guard t))
  (cons (control-let*)
        (union$ *b-store-resultp*
                *decode-reg-mode*
                *unary-op-code-p*
                :test 'equal)))

(defthmd control-let$netlist-okp
  (and (net-syntax-okp (control-let$netlist))
       (net-arity-okp (control-let$netlist))))

(defthmd control-let$value
  (implies (and (control-let& netlist)
                (true-listp i-reg) (equal (len i-reg) 32)
                (true-listp flags) (equal (len flags) 4)
                (true-listp regs-address) (equal (len regs-address) 4))
           (equal (se 'control-let
                      (append i-reg (append flags regs-address))
                      sts
                      netlist)
                  (f$control-let i-reg flags regs-address)))
  :hints (("Goal"
           :in-theory (e/d (se-rules
                             control-let&
                             b-or4$value-as-f$set-some-flags
                             b-and4$value-as-f$all-t-regs-address
                             a-immediate-p
                             mode-a
                             mode-b
                             store-cc
                             c-flag
                             set-flags
                             op-code
                             assoc-eq-value-nth-pairlis$
                             b-store-resultp$value
                             decode-reg-mode$value
                             unary-op-code-p$value)
                            (tv-disabled-rules
                             (control-let*)
                             (si)
                             (sis))))))

(defmacro f$control-let=control-let-lemma ()
  `(defthm f$control-let=control-let
     (implies (and (bvp i-reg) (equal (len i-reg) 32)
                   (bvp flags) (equal (len flags) 4)
                   (bvp regs-address) (equal (len regs-address) 4))
              (equal (f$control-let i-reg flags regs-address)
                     ,(control-let
                       '(list a-immediate-p store set-some-flags
                              direct-a direct-b unary
                              pre-dec-a pre-dec-b c all-t-regs-address
                              side-effect-a side-effect-b))))
     :hints (("Goal"
              :in-theory (enable binary-and* binary-or*)))))

(f$control-let=control-let-lemma)

(in-theory (disable f$control-let))

;; ======================================================================

;; The NEXT-STATE logic is synthesized from the *STATE-TABLE*.

(defmacro define-next-state-events ()
 `(progn
    ,@(define-next-state *state-table*)

    (defthm bvp-next-state
      (implies (bvp decoded-state)
               (bvp (next-state
                     decoded-state store set-some-flags unary
                     direct-a direct-b
                     side-effect-a side-effect-b all-t-regs-address
                     dtack- hold-)))
      :hints (("Goal" :in-theory (enable bvp next-state)))
      :rule-classes (:rewrite :type-prescription))

    (defthm len-next-state
      (equal (len (next-state
                   decoded-state store set-some-flags unary
                   direct-a direct-b
                   side-effect-a side-effect-b all-t-regs-address
                   dtack- hold-))
             32)
      :hints (("Goal" :in-theory (enable next-state))))

    (defthm len-f$next-state
      (equal (len (f$next-state
                   decoded-state store set-some-flags unary
                   direct-a direct-b
                   side-effect-a side-effect-b all-t-regs-address
                   dtack- hold-))
             32)
      :hints (("Goal" :in-theory (enable f$next-state))))

    (defthmd next-state$value
      (implies (and (next-state& netlist)
                    (true-listp decoded-state)
                    (equal (len decoded-state) 32))
               (equal (se 'next-state
                          (append decoded-state
                                  (list store set-some-flags
                                        unary direct-a direct-b
                                        side-effect-a side-effect-b
                                        all-t-regs-address
                                        dtack- hold-))
                          sts
                          netlist)
                      (f$next-state decoded-state store set-some-flags
                                    unary direct-a direct-b
                                    side-effect-a side-effect-b
                                    all-t-regs-address
                                    dtack- hold-)))
      :hints (("Goal"
               :in-theory (e/d (se-rules
                                 next-state&
                                 f$next-state)
                                ((next-state*)
                                 (si)
                                 (sis)
                                 tv-disabled-rules)))))

    ))

(define-next-state-events)

;; ======================================================================

;; CV

;; CV computes the 40-bit control vector.

(defmacro cv-fns ()
  (declare (xargs :guard t))
  (b* ((state-names (strip-cars *control-states*)))
    `(progn

       (defund cv (decoded-state
                   rn-a rn-b op-code
                   pc-reg regs-address set-flags
                   store c a-immediate-p rw-
                   direct-a side-effect-a side-effect-b
                   pre-dec-a pre-dec-b)
         (declare (xargs :guard (and (true-listp decoded-state)
                                     (true-listp rn-a)
                                     (true-listp rn-b)
                                     (true-listp op-code)
                                     (true-listp pc-reg)
                                     (true-listp regs-address)
                                     (true-listp set-flags))))
         (b* ,(bind-values state-names 0 'decoded-state)
           (let ((store- (b-not store)))
             (let ((alu-zero  (b-or4 fetch0 reset0 reset1 reset2))
                   (alu-swap  (b-or3 readb2 write1 sefb1))
                   (incdeca   (b-or reada1 sefa1)))
               (let ((alu-op (v-if (b-nor4 fetch2 incdeca alu-swap alu-zero)
                                   op-code
                                   (v-if (b-nand (b-nand incdeca pre-dec-a)
                                                 (b-nand alu-swap pre-dec-b))
                                         (alu-dec-op)
                                         (alu-inc-op)))))
                 (list*
                  ;;rw-
                  (b-and (b-nand (b-not rw-) fetch0)
                         (b-nor3 write1 write2 write3))
                  ;;strobe-
                  (b-nor8 fetch2 fetch3 reada2 reada3
                          readb2 readb3 write2 write3)
                  ;;hdack-
                  (b-not hold0)
                  ;;we-regs
                  (b-nand5 (b-nand store update)
                           (b-nand side-effect-a reada1)
                           (b-nand3 store- side-effect-b readb2)
                           (b-nand side-effect-b write1)
                           (b-nor5 fetch2 sefa1 sefb1 reset0 reset2))
                  ;;we-a-reg
                  (b-nand (b-nand direct-a readb1)
                          (b-nor6 fetch0 rega reada0 reada3 sefa0 reset1))
                  ;;we-b-reg
                  (b-nand (b-nor4 regb update reada2 readb0)
                          (b-nor4 readb3 write0 sefb0 reset1))
                  ;;we-i-reg
                  (b-or fetch3 reset1)
                  ;;we-data-out
                  (b-or write0 reset0)
                  ;;we-addr-out
                  (b-nand (b-nor3 fetch0 reada0 readb0)
                          (b-nor write0 reset1))
                  ;;we-hold-
                  (b-or3 fetch0 hold0 reset0)
                  ;;we-pc-reg
                  (b-or hold0 reset0)
                  ;;data-in-select
                  (b-or3 fetch3 reada3 readb3)
                  ;;dec-addr-out
                  (b-nand (b-nand pre-dec-a reada0)
                          (b-nand pre-dec-b (b-or readb0 write0)))
                  ;;select-immediate
                  (b-and a-immediate-p (b-or rega readb1))
                  ;;alu-c
                  (carry-in-help (cons c (cons alu-zero alu-op)))
                  ;;alu-zero
                  alu-zero
                  (append
                   ;;state
                   (encode-32 ,@state-names)
                   (append
                    ;;we-flags
                    (v-if (b-nor update write0)
                          (v-if reset0
                                (make-list 4 :initial-element t)
                                (make-list 4))
                          set-flags)
                    (append
                     ;;regs-address
                     (v-if (b-nand (b-nor3 rega reada0 reada1)
                                   (b-nor3 readb1 sefa0 sefa1))
                           rn-a
                           (v-if (b-nand (b-nor5 regb update reada2 readb0 readb2)
                                         (b-nor4 write0 write1 sefb0 sefb1))
                                 rn-b
                                 (v-if (b-or reset0 reset1)
                                       (make-list 4)
                                       (v-if reset2
                                             (v-inc regs-address)
                                             pc-reg))))

                     (append
                      ;;alu-op
                      alu-op
                      ;;alu-mpg
                      (mpg (cons alu-zero (cons alu-swap alu-op)))))))))))))

       (defund f$cv (decoded-state
                     rn-a rn-b op-code
                     pc-reg regs-address set-flags
                     store c a-immediate-p rw-
                     direct-a side-effect-a side-effect-b
                     pre-dec-a pre-dec-b)
         (declare (xargs :guard (and (true-listp decoded-state)
                                     (true-listp rn-a)
                                     (true-listp rn-b)
                                     (true-listp op-code)
                                     (true-listp pc-reg)
                                     (true-listp regs-address)
                                     (true-listp set-flags))))
         (b* ,(bind-values state-names 0 'decoded-state)
           (let ((store- (f-not store)))
             (let ((alu-zero  (f-or4 fetch0 reset0 reset1 reset2))
                   (alu-swap  (f-or3 readb2 write1 sefb1))
                   (incdeca   (f-or reada1 sefa1)))
               (let ((alu-op (f$select-op-code
                              (f-nor4 fetch2 incdeca alu-swap alu-zero)
                              (f-nand (f-nand incdeca pre-dec-a)
                                      (f-nand alu-swap pre-dec-b))
                              op-code)))

                 (list*
                  ;;rw-
                  (f-and (f-nand (f-not rw-) fetch0)
                         (f-nor3 write1 write2 write3))
                  ;;strobe-
                  (f-nor8 fetch2 fetch3 reada2 reada3
                          readb2 readb3 write2 write3)
                  ;;hdack-
                  (f-not hold0)
                  ;;we-regs
                  (f-nand5 (f-nand store update)
                           (f-nand side-effect-a reada1)
                           (f-nand3 store- side-effect-b readb2)
                           (f-nand side-effect-b write1)
                           (f-nor5 fetch2 sefa1 sefb1 reset0 reset2))
                  ;;we-a-reg
                  (f-nand (f-nand direct-a readb1)
                          (f-nor6 fetch0 rega reada0 reada3 sefa0 reset1))
                  ;;we-b-reg
                  (f-nand (f-nor4 regb update reada2 readb0)
                          (f-nor4 readb3 write0 sefb0 reset1))
                  ;;we-i-reg
                  (f-or fetch3 reset1)
                  ;;we-data-out
                  (f-or write0 reset0)
                  ;;we-addr-out
                  (f-nand (f-nor3 fetch0 reada0 readb0)
                          (f-nor write0 reset1))
                  ;;we-hold-
                  (f-or3 fetch0 hold0 reset0)
                  ;;we-pc-reg
                  (f-or hold0 reset0)
                  ;;data-in-select
                  (f-or3 fetch3 reada3 readb3)
                  ;;dec-addr-out
                  (f-nand (f-nand pre-dec-a reada0)
                          (f-nand pre-dec-b (f-or readb0 write0)))
                  ;;select-immediate
                  (f-and a-immediate-p (f-or rega readb1))
                  ;;alu-c
                  (f$carry-in-help (cons c (cons alu-zero alu-op)))
                  ;;alu-zero
                  alu-zero
                  (append
                   ;;state
                   (f$encode-32 ,@state-names)
                   (append
                    ;;we-flags
                    (fv-if (f-nor update write0)
                           (make-list 4 :initial-element (3v-fix reset0))
                           set-flags)
                    (append
                     ;;regs-address
                     (fv-if (f-nand (f-nor3 rega reada0 reada1)
                                    (f-nor3 readb1 sefa0 sefa1))
                            rn-a
                            (fv-if
                             (f-nand (f-nor5 regb update reada2 readb0 readb2)
                                     (f-nor4 write0 write1 sefb0 sefb1))
                             rn-b
                             (f$v-if-f-4 (f-or reset0 reset1)
                                         (fv-if reset2
                                                (f$v-inc4$v regs-address)
                                                pc-reg))))

                     (append
                      ;;alu-op
                      alu-op
                      ;;alu-mpg
                      (f$mpg (cons alu-zero (cons alu-swap alu-op)))))))))))))
       )))

(cv-fns)

(defthmd make-list-crock-for-f$cv=cv
  (implies (booleanp v)
           (equal (make-list 4 :initial-element v)
                  (if v (list t t t t) (list nil nil nil nil)))))

(defthm f$cv=cv
  (implies (and (bvp decoded-state) (equal (len decoded-state) 32)
                (bvp rn-a) (equal (len rn-a) 4)
                (bvp rn-b) (equal (len rn-b) 4)
                (bvp op-code) (equal (len op-code) 4)
                (bvp pc-reg) (equal (len pc-reg) 4)
                (bvp regs-address) (equal (len regs-address) 4)
                (bvp set-flags) (equal (len set-flags) 4)
                (booleanp store) (booleanp c)
                (booleanp a-immediate-p) (booleanp rw-)
                (booleanp direct-a)
                (booleanp side-effect-a) (booleanp side-effect-b)
                (booleanp pre-dec-a) (booleanp pre-dec-b))
           (equal (f$cv decoded-state
                        rn-a rn-b op-code
                        pc-reg regs-address set-flags
                        store c a-immediate-p rw-
                        direct-a side-effect-a side-effect-b
                        pre-dec-a pre-dec-b)
                  (cv decoded-state
                      rn-a rn-b op-code
                      pc-reg regs-address set-flags
                      store c a-immediate-p rw-
                      direct-a side-effect-a side-effect-b
                      pre-dec-a pre-dec-b)))
  :hints (("Goal"
           :in-theory (e/d (f$cv cv
                                  bvp booleanp-car-of-bvp)
                            (b-gates)))))

(defthm bvp-cv
  (let ((cv (cv decoded-state
                rn-a rn-b op-code
                pc-reg regs-address set-flags
                store c a-immediate-p rw-
                direct-a side-effect-a side-effect-b
                pre-dec-a pre-dec-b)))
    (implies
     (bvp decoded-state)
     (bvp cv)))
  :hints (("Goal" :in-theory (e/d (bvp cv)
                                   (b-gates))))
  :rule-classes (:rewrite :type-prescription))

(defthm len-cv
  (let ((cv (cv decoded-state
                rn-a rn-b op-code
                pc-reg regs-address set-flags
                store c a-immediate-p rw-
                direct-a side-effect-a side-effect-b
                pre-dec-a pre-dec-b)))
    (implies
     (and (equal (len rn-a) 4)
          (equal (len op-code) 4))
     (equal (len cv) 40)))
  :hints (("Goal" :in-theory (e/d (cv) (b-gates)))))

(defthm len-f$cv
  (let ((f$cv (f$cv decoded-state
                    rn-a rn-b op-code
                    pc-reg regs-address set-flags
                    store c a-immediate-p rw-
                    direct-a side-effect-a side-effect-b
                    pre-dec-a pre-dec-b)))
    (implies
     (equal (len rn-a) 4)
     (equal (len f$cv) 40)))
  :hints (("Goal" :in-theory (enable f$cv))))

(defmacro cv*-gen ()
  (declare (xargs :guard t))
  (b* ((state-names (strip-cars *control-states*)))

    `(DEFUN CV* ()
       (declare (xargs :guard t))
       (LIST
        'CV
        ;; Inputs
        (APPEND (sis 'DECODED-STATE 0 32)
                (sis 'RN-A 0 4)
                (sis 'RN-B 0 4)
                (sis 'OP-CODE 0 4)
                (sis 'PC-REG 0 4)
                (sis 'REGS-ADDRESS 0 4)
                (sis 'SET-FLAGS 0 4)
                '(STORE C A-IMMEDIATE-P RW- DIRECT-A SIDE-EFFECT-A SIDE-EFFECT-B
                        PRE-DEC-A PRE-DEC-B))
        ;; Outputs
        (APPEND '(NEW-RW- STROBE- HDACK-
                          WE-REGS WE-A-REG WE-B-REG WE-I-REG
                          WE-DATA-OUT WE-ADDR-OUT WE-HOLD- WE-PC-REG
                          DATA-IN-SELECT DEC-ADDR-OUT SELECT-IMMEDIATE
                          ALU-C ALU-ZERO)
                (sis 'STATE 0 5)
                (sis 'WE-FLAGS 0 4)
                (sis 'NEW-REGS-ADDRESS 0 4)
                (sis 'ALU-OP 0 4)
                (sis 'ALU-MPG 0 7))
        ;; Statelist
        NIL
        ;; Occurences
        (list
         ;;  Decoded state
         ,@(id-occs-from-decoded-state state-names 0)
         ;;  Common subexpressions
         '(g0 (store-) b-not (store))
         '(g1 (alu-zero) b-or4 (fetch0 reset0 reset1 reset2))
         '(g2 (alu-swap) b-or3 (readb2 write1 sefb1))
         '(g3 (incdeca) b-or (reada1 sefa1))
         ;;  ALU-OP
         '(g4 (s4) b-nor4 (fetch2 incdeca alu-swap alu-zero))
         '(g5 (s5) b-nand (incdeca pre-dec-a))
         '(g6 (s6) b-nand (alu-swap pre-dec-b))
         '(g7 (s7) b-nand (s5 s6))
         (list 'g8 (sis 'alu-op 0 4) 'select-op-code (list* 's4 's7 (sis 'op-code 0 4)))
         ;;G9 was optimized away.
         ;;RW-
         '(g10 (s10) b-not (rw-))
         '(g11 (s11) b-nand (s10 fetch0))
         '(g12 (s12) b-nor3 (write1 write2 write3))
         '(g13 (new-rw-) b-and (s11 s12))
         ;;STROBE-
         '(g14 (strobe-) b-nor8
               (fetch2 fetch3 reada2 reada3 readb2 readb3 write2 write3))
         ;;HDACK-
         '(g15 (hdack-) b-not (hold0))
         ;;G 16 was the old DRIVE-ADDR-OUT.
         ;;WE-REGS
         '(g17 (s17) b-nand (store update))
         '(g18 (s18) b-nand (side-effect-a reada1))
         '(g19 (s19) b-nand3 (store- side-effect-b readb2))
         '(g20 (s20) b-nand (side-effect-b write1))
         '(g21 (s21) b-nor5 (fetch2 sefa1 sefb1 reset0 reset2))
         '(g22 (we-regs) b-nand5 (s17 s18 s19 s20 s21))
         ;;WE-A-REG
         '(g23 (s23) b-nand (direct-a readb1))
         '(g24 (s24) b-nor6 (fetch0 rega reada0 reada3 sefa0 reset1))
         '(g25 (we-a-reg) b-nand (s23 s24))
         ;;WE-B-REG
         '(g26 (s26) b-nor4 (regb update reada2 readb0))
         '(g27 (s27) b-nor4 (readb3 write0 sefb0 reset1))
         '(g28 (we-b-reg) b-nand (s26 s27))
         ;;WE-I-REG
         '(g29 (we-i-reg) b-or (fetch3 reset1))
         ;;WE-DATA-OUT
         '(g30 (we-data-out) b-or (write0 reset0))
         ;;WE-ADDR-OUT
         '(g31 (s31) b-nor3 (fetch0 reada0 readb0))
         '(g32 (s32) b-nor (write0 reset1))
         '(g33 (we-addr-out) b-nand (s31 s32))
         ;;WE-HOLD-
         '(g34 (we-hold-) b-or3 (fetch0 hold0 reset0))
         ;;WE-PC-REG
         '(g35 (we-pc-reg) b-or (hold0 reset0))
         ;;DATA-IN-SELECT
         '(g36 (data-in-select) b-or3 (fetch3 reada3 readb3))
         ;;DEC-ADDR-OUT
         '(g37 (s37) b-nand (pre-dec-a reada0))
         '(g38 (s38) b-or (readb0 write0))
         '(g39 (s39) b-nand (pre-dec-b s38))
         '(g40 (dec-addr-out) b-nand (s37 s39))
         ;;SELECT-IMMEDIATE
         '(g41 (s41) b-or (rega readb1))
         '(g42 (select-immediate) b-and (a-immediate-p s41))
         ;;ALU-C
         (list 'g43 '(alu-c) 'carry-in-help
               (cons 'c (cons 'alu-zero (sis 'alu-op 0 4))))
         ;;ALU-ZERO (above)
         ;;STATE
         (list 'g44 (sis 'state 0 5) 'encode-32 (sis 'decoded-state 0 32))
         ;;WE-FLAGS
         (list 'g45 (sis 'fanout-reset0 0 4) 'fanout-4 '(reset0))
         '(g46 (s46) b-nor (update write0))
         (list 'g47 (sis 'we-flags 0 4) (si 'tv-if (tree-number (make-tree 4)))
               (cons 's46 (append (sis 'fanout-reset0 0 4) (sis 'set-flags 0 4))))
         ;;REGS-ADDRESS
         '(g48 (s48) b-nor3 (rega reada0 reada1))
         '(g49 (s49) b-nor3 (readb1 sefa0 sefa1))
         '(g50 (select-rn-a) b-nand (s48 s49))
         '(g51 (s51) b-nor5 (regb update reada2 readb0 readb2))
         '(g52 (s52) b-nor4 (write0 write1 sefb0 sefb1))
         '(g53 (select-rn-b) b-nand (s51 s52))
         '(g54 (select-all-f) b-or (reset0 reset1))
         (list 'g55 (sis 'v-inc-regs-address 0 4) 'v-inc4 (sis 'regs-address 0 4))
         (list 'g56 (sis 's56 0 4) (si 'tv-if (tree-number (make-tree 4)))
               (cons 'reset2 (append (sis 'v-inc-regs-address 0 4) (sis 'pc-reg 0 4))))
         (list 'g57 (sis 's57 0 4) 'v-if-f-4 (cons 'select-all-f (sis 's56 0 4)))
         (list 'g58 (sis 's58 0 4) (si 'tv-if (tree-number (make-tree 4)))
               (cons 'select-rn-b (append (sis 'rn-b 0 4) (sis 's57 0 4))))
         (list 'g59 (sis 'new-regs-address 0 4) (si 'tv-if (tree-number (make-tree 4)))
               (cons 'select-rn-a (append (sis 'rn-a 0 4) (sis 's58 0 4))))
         ;;ALU-OP (above)
         ;;ALU-MPG
         (list 'g60 (sis 'alu-mpg 0 7) 'mpg
               (list* 'alu-zero 'alu-swap (sis 'alu-op 0 4))))))
    ))

(cv*-gen)

(defund cv& (netlist)
  (and (equal (assoc 'cv netlist)
              (cv*))
       (let ((netlist (delete-to-eq 'cv netlist)))
         (and (select-op-code& netlist)
              (tv-if& netlist (make-tree 4))
              (carry-in-help& netlist)
              (encode-32& netlist)
              (fanout-4& netlist)
              (v-inc4& netlist)
              (v-if-f-4& netlist)
              (mpg& netlist)))))

(defun cv$netlist ()
  (cons (cv*)
        (union$ *select-op-code*
                (tv-if$netlist (make-tree 4))
                *carry-in-help*
                *encode-32*
                *fanout-4*
                *v-inc4*
                *v-if-f-4*
                *mpg*
                :test 'equal)))

(defthm check-cv$netlist
  (cv& (cv$netlist)))

(defthmd cv$value
  (implies
   (and (cv& netlist)
        (true-listp decoded-state) (equal (len decoded-state) 32)
        (true-listp rn-a) (equal (len rn-a) 4)
        (true-listp rn-b) (equal (len rn-b) 4)
        (true-listp op-code) (equal (len op-code) 4)
        (true-listp pc-reg) (equal (len pc-reg) 4)
        (true-listp regs-address) (equal (len regs-address) 4)
        (true-listp set-flags) (equal (len set-flags) 4))
   (equal (se 'cv
              (append
               decoded-state
               (append
                rn-a
                (append
                 rn-b
                 (append
                  op-code
                  (append
                   pc-reg
                   (append
                    regs-address
                    (append
                     set-flags
                     (list store c a-immediate-p rw- direct-a
                           side-effect-a side-effect-b
                           pre-dec-a pre-dec-b))))))))
              sts netlist)
          (f$cv decoded-state
                rn-a rn-b op-code
                pc-reg regs-address set-flags
                store c a-immediate-p rw-
                direct-a side-effect-a side-effect-b
                pre-dec-a pre-dec-b)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (se-rules
                             cv&
                             v-if-f-4&
                             f$v-if-f-4
                             select-op-code$value
                             tv-if$value
                             carry-in-help$value
                             encode-32$value-on-a-vector
                             fanout-4$value
                             v-inc4$value
                             v-if-f-4$value
                             mpg$value
                             f$cv
                             cv)
                            ((cv*)
                             (make-tree)
                             (si)
                             (sis)
                             tv-disabled-rules)))))

;; ======================================================================

;; NEXT-CNTL-STATE

;; The control logic.

(defmacro next-cntl-state-gen ()
  (declare (xargs :guard t))
  `(defun next-cntl-state (reset- dtack- hold- rw-
                                  st i-reg flags pc-reg regs-address)
     (declare (xargs :guard (and (true-listp st)
                                 (true-listp i-reg)
                                 (true-listp flags)
                                 (true-listp pc-reg)
                                 (true-listp regs-address))))
     ,(control-let
       ;; This forces an illegal state if RESET- is asserted, thus sending the
       ;; machine to RESET0.
       '(let ((decoded-state (decode-5 (v-if reset- st (v_v11111)))))
          (let ((next-state
                 (next-state decoded-state store set-some-flags unary direct-a
                             direct-b side-effect-a side-effect-b
                             all-t-regs-address dtack- hold-)))
            (cv next-state
                rn-a rn-b op-code
                pc-reg regs-address set-flags
                store c a-immediate-p rw-
                direct-a side-effect-a side-effect-b
                pre-dec-a pre-dec-b))))))

(next-cntl-state-gen)

(defthm bvp-next-cntl-state
  (bvp (next-cntl-state
        reset- dtack- hold- rw-
        st i-reg flags pc-reg regs-address))
  :rule-classes (:rewrite :type-prescription))

(defthm len-next-cntl-state
  (equal (len (next-cntl-state
               reset- dtack- hold- rw-
               state i-reg flags pc-reg regs-address))
         40))

(defun f$next-cntl-state (reset- dtack- hold- rw-
                                 st i-reg flags pc-reg regs-address)
  (declare (xargs :guard (and (true-listp st)
                              (true-listp i-reg)
                              (true-listp flags)
                              (true-listp pc-reg)
                              (true-listp regs-address))))
  (let ((control-let (f$control-let i-reg flags regs-address))
        (set-flags (set-flags i-reg))
        (op-code (op-code i-reg))
        (rn-a (rn-a i-reg))
        (rn-b (rn-b i-reg)))
    (let
        ((a-immediate-p      (car control-let))
         (store              (cadr control-let))
         (set-some-flags     (caddr control-let))
         (direct-a           (cadddr control-let))
         (direct-b           (car (cddddr control-let)))
         (unary              (cadr (cddddr control-let)))
         (pre-dec-a          (caddr (cddddr control-let)))
         (pre-dec-b          (cadddr (cddddr control-let)))
         (c                  (car (cddddr (cddddr control-let))))
         (all-t-regs-address (cadr (cddddr (cddddr control-let))))
         (side-effect-a      (caddr (cddddr (cddddr control-let))))
         (side-effect-b      (cadddr (cddddr (cddddr control-let)))))
      ;; This forces an illegal state if reset- is asserted, thus sending the
      ;; machine to reset0.
      (let ((decoded-state (f$decode-5 (fv-or
                                        (make-list 5
                                                   :initial-element
                                                   (f-not reset-))
                                        st))))
        (let ((next-state
               (f$next-state decoded-state store set-some-flags unary
                             direct-a direct-b
                             side-effect-a side-effect-b
                             all-t-regs-address dtack- hold-)))
          (f$cv next-state
                rn-a rn-b op-code
                pc-reg regs-address set-flags
                store c a-immediate-p rw-
                direct-a side-effect-a side-effect-b
                pre-dec-a pre-dec-b))))))

(defthm len-f$next-cntl-state
  (equal (len (f$next-cntl-state
               reset- dtack- hold- rw-
               st i-reg flags pc-reg regs-address))
         40))

(defthm v-or-crock-for-f$next-cntl-state
  (implies (and (equal (len st) 5)
                (bvp st))
           (and (equal (v-or (list nil nil nil nil nil) st)
                       st)
                (equal (v-or (list t t t t t) st)
                       (list t t t t t))))
  :hints (("Goal" :in-theory (enable bvp v-or))))

(defthm f$next-cntl-state=next-cntl-state
  (implies (and (booleanp reset-) (booleanp dtack-)
                (booleanp hold-) (booleanp rw-)
                (bvp st) (equal (len st) 5)
                (bvp i-reg) (equal (len i-reg) 32)
                (bvp flags) (equal (len flags) 4)
                (bvp pc-reg) (equal (len pc-reg) 4)
                (bvp regs-address) (equal (len regs-address) 4))
           (equal (f$next-cntl-state
                   reset- dtack- hold- rw-
                   st i-reg flags pc-reg regs-address)
                  (next-cntl-state
                   reset- dtack- hold- rw-
                   st i-reg flags pc-reg regs-address))))

(in-theory (disable next-cntl-state
                    f$next-cntl-state
                    v-or-crock-for-f$next-cntl-state))

(defun next-cntl-state* ()
  (declare (xargs :guard t))
  (list
   'next-cntl-state
   (append '(reset- dtack- hold- rw-)
           (sis 'state 0 5)
           (sis 'i-reg 0 32)
           (sis 'flags 0 4)
           (sis 'pc-reg 0 4)
           (sis 'regs-address 0 4))
   (sis 'next-cntl-state 0 40)
   nil
   (list
    ;;  Decoded control lines
    (list 'control-signals
          '(a-immediate-p store set-some-flags direct-a direct-b unary
                          pre-dec-a pre-dec-b c all-t-regs-address
                          side-effect-a side-effect-b)
          'control-let
          (append (sis 'i-reg 0 32) (append (sis 'flags 0 4) (sis 'regs-address 0 4))))
    ;;  Illegal state on RESET
    (list 'not-reset
          '(reset)
          'b-not
          '(reset-))
    (list 'reset5x
          (sis 'reset5x 0 5)
          'fanout-5
          '(reset))
    (list 'xstate
          (sis 'xstate 0 5)
          (si 'v-or 5)
          (append (sis 'reset5x 0 5) (sis 'state 0 5)))
    ;;  The decoded state
    (list 'dstate
          (sis 'decoded-state 0 32)
          'decode-5
          (sis 'xstate 0 5))
    ;;  The next state
    (list 'nxstate
          (sis 'next-state 0 32)
          'next-state
          (append (sis 'decoded-state 0 32)
                  '(store set-some-flags unary direct-a direct-b
                          side-effect-a side-effect-b all-t-regs-address
                          dtack- hold-)))
    ;;  The control vector
    (list 'cvector
          (sis 'next-cntl-state 0 40)
          'cv
          (append (sis 'next-state 0 32)
                  (rn-a (sis 'i-reg 0 32))
                  (rn-b (sis 'i-reg 0 32))
                  (op-code (sis 'i-reg 0 32))
                  (sis 'pc-reg 0 4)
                  (sis 'regs-address 0 4)
                  (set-flags (sis 'i-reg 0 32))
                  '(store c a-immediate-p rw- direct-a
                          side-effect-a side-effect-b
                          pre-dec-a pre-dec-b))))))

(defund next-cntl-state& (netlist)
  (and (equal (assoc 'next-cntl-state netlist)
              (next-cntl-state*))
       (let ((netlist (delete-to-eq 'next-cntl-state netlist)))
         (and (control-let& netlist)
              (fanout-5& netlist)
              (v-or& netlist 5)
              (decode-5& netlist)
              (next-state& netlist)
              (cv& netlist)))))

(defun next-cntl-state$netlist ()
  (cons (next-cntl-state*)
        (union$ (control-let$netlist)
                *fanout-5*
                (v-or$netlist 5)
                *decode-5*
                (next-state$netlist)
                (cv$netlist)
                :test 'equal)))

(defthm check-next-cntl-state$netlist
  (next-cntl-state& (next-cntl-state$netlist)))

(defthmd next-cntl-state$value
  (implies (and (next-cntl-state& netlist)
                (true-listp st) (equal (len st) 5)
                (true-listp i-reg) (equal (len i-reg) 32)
                (true-listp flags) (equal (len flags) 4)
                (true-listp pc-reg) (equal (len pc-reg) 4)
                (true-listp regs-address) (equal (len regs-address) 4))
           (equal (se 'next-cntl-state
                      (list* reset- dtack- hold- rw-
                             (append
                              st
                              (append
                               i-reg
                               (append flags (append pc-reg regs-address)))))
                      sts netlist)
                  (f$next-cntl-state reset- dtack- hold- rw-
                                     st i-reg flags pc-reg regs-address)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (se-rules
                             next-cntl-state&
                             control-let$value
                             fanout-5$value
                             v-or$value
                             decode-5$value
                             next-state$value
                             cv$value
                             rn-a
                             rn-b
                             set-flags
                             op-code
                             f-not
                             f$next-cntl-state)
                            ((next-cntl-state*)
                             (si)
                             (sis)
                             tv-disabled-rules)))))

;; This macro generates lemmas proving that the control logic produces the
;; desired control vectors.

(defmacro generate-next-cntl-state-lemmas-events ()
  (generate-next-cntl-state-lemmas *state-table* *control-arglist*))

(generate-next-cntl-state-lemmas-events)

