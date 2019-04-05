;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau (derived from the FM9001 work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; The ACL2 source code for the FM9001 work is available at
;; https://github.com/acl2/acl2/tree/master/books/projects/fm9001.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; January 2019

(in-package "ADE")

(include-book "de")
(include-book "fm9001-spec")
(include-book "macros")
(include-book "../../list-rewrites")

;; ======================================================================

;; UNARY-OP-CODE-P

(defun f$unary-op-code-p (op)
  (declare (xargs :guard (true-listp op)))
  (let ((op0 (car op))
        (op1 (cadr op))
        (op2 (caddr op))
        (op3 (cadddr op)))
    (let ((op0- (f-not op0))
          (op1- (f-not op1))
          (op2- (f-not op2))
          (op3- (f-not op3)))
      (let ((s0 (f-nand op3- op1-))
            (s1 (f-nand op2- op1-))
            (s2 (f-nand3 op3 op1 op0-))
            (s3 (f-nand3 op3 op2 op1)))
        (f-nand4 s0 s1 s2 s3)))))

(defthm f$unary-op-code-p=unary-op-code-p
  (implies (and (bvp op)
                (equal (len op) 4))
           (equal (f$unary-op-code-p op)
                  (unary-op-code-p op)))
  :hints (("Goal" :in-theory (enable f-gates bvp unary-op-code-p))))

(defconst *unary-op-code-p*
  '((unary-op-code-p
     (op0 op1 op2 op3)
     (z)
     ()
     ((g0 (op0-) b-not   (op0))
      (g1 (op1-) b-not   (op1))
      (g2 (op2-) b-not   (op2))
      (g3 (op3-) b-not   (op3))
      (g4 (s0)   b-nand  (op3- op1-))
      (g5 (s1)   b-nand  (op2- op1-))
      (g6 (s2)   b-nand3 (op3 op1 op0-))
      (g7 (s3)   b-nand3 (op3 op2 op1))
      (g8 (z)    b-nand4 (s0 s1 s2 s3))))))

(assert-event (net-syntax-okp *unary-op-code-p*) :on-skip-proofs t)
(assert-event (net-arity-okp *unary-op-code-p*) :on-skip-proofs t)

(defund unary-op-code-p& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (netlist-hyps netlist unary-op-code-p))

(defthm unary-op-code-p$value
  (implies (unary-op-code-p& netlist)
           (equal (se 'unary-op-code-p op-code st netlist)
                  (list (f$unary-op-code-p op-code))))
  :hints (("Goal"
           :expand (se 'unary-op-code-p op-code st netlist)
           :in-theory (enable de-rules
                              unary-op-code-p&))))

(in-theory (disable f$unary-op-code-p))

;; ======================================================================

;; DECODE-REG-MODE

(defun f$decode-reg-mode (m)
  (declare (xargs :guard (true-listp m)))
  (let ((m0 (car m))
        (m1 (cadr m)))
    (list (f-nor m0 m1)
          (f-nor m0 (f-not m1))
          (identity m1))))

(defconst *decode-reg-mode*
  '((decode-reg-mode
     (m0 m1)
     (direct pre-dec side-effect)
     ()
     ((g0 (direct) b-nor (m0 m1))
      (g1 (m1-) b-not (m1))
      (g2 (pre-dec) b-nor (m0 m1-))
      (g3 (side-effect) wire (m1))))))

(assert-event (net-syntax-okp *decode-reg-mode*) :on-skip-proofs t)
(assert-event (net-arity-okp *decode-reg-mode*) :on-skip-proofs t)

(defund decode-reg-mode& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (netlist-hyps netlist decode-reg-mode))

(defthm decode-reg-mode$value
  (implies (decode-reg-mode& netlist)
           (equal (se 'decode-reg-mode mode st netlist)
                  (f$decode-reg-mode mode)))
  :hints (("Goal"
           :expand (se 'decode-reg-mode mode st netlist)
           :in-theory (enable de-rules
                              decode-reg-mode&))))

(defthm f$decode-reg-mode-as-reg-mode
  (implies (and (bvp mode)
                (equal (len mode) 2))
           (equal (f$decode-reg-mode mode)
                  (list (reg-direct-p mode)
                        (pre-dec-p mode)
                        (or (pre-dec-p mode)
                            (post-inc-p mode)))))
  :hints (("Goal" :in-theory (enable bvp
                                     reg-direct-p
                                     pre-dec-p
                                     post-inc-p))))

(in-theory (disable f$decode-reg-mode))

;; ======================================================================

;; SELECT-OP-CODE

(defun f$select-op-code (select dec op)
  (declare (xargs :guard (true-listp op)))
  (let ((op0 (car op))
        (op1 (cadr op))
        (op2 (caddr op))
        (op3 (cadddr op)))
    (list (f-nand select (f-not op0))
          (f-and select op1)
          (f-if select op2 dec)
          (f-and select op3))))

(defthm len-f$select-op-code
  (equal (len (f$select-op-code select dec op))
         4))

(defthm f$select-op-code-selects
  (implies (and (booleanp select)
                (booleanp dec)
                (bvp op)
                (equal (len op) 4))
           (equal (f$select-op-code select dec op)
                  (v-if select
                        op
                        (v-if dec
                              (alu-dec-op)
                              (alu-inc-op)))))
  :hints (("Goal" :in-theory (enable bvp))))

(defconst *select-op-code*
  '((select-op-code
     (select dec op0 op1 op2 op3)
     (z0 z1 z2 z3)
     ()
     ((i0 (op0-) b-not (op0))
      (g0 (z0)   b-nand (select op0-))
      (g1 (z1)   b-and  (select op1))
      (g2 (z2)   b-if   (select op2 dec))
      (g3 (z3)   b-and  (select op3))))))

(assert-event (net-syntax-okp *select-op-code*) :on-skip-proofs t)
(assert-event (net-arity-okp *select-op-code*) :on-skip-proofs t)

(defund select-op-code& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (netlist-hyps netlist select-op-code))

(defthm select-op-code$value
  (implies (select-op-code& netlist)
           (equal (se 'select-op-code (list* select dec op) st netlist)
                  (f$select-op-code select dec op)))
  :hints (("Goal"
           :expand (se 'select-op-code (list* select dec op) st netlist)
           :in-theory (enable de-rules
                              select-op-code&))))

(in-theory (disable f$select-op-code))

;; ======================================================================

;; V-IF-F-4

(defun f$v-if-f-4 (c a)
  (declare (xargs :guard (true-listp a)))
  (list (f-and (f-not c) (car a))
        (f-and (f-not c) (cadr a))
        (f-and (f-not c) (caddr a))
        (f-and (f-not c) (cadddr a))))

(defconst *v-if-f-4*
  '((v-if-f-4
     (c a0 a1 a2 a3)
     (z0 z1 z2 z3)
     ()
     ((cb (c-) b-not (c))
      (g0 (z0) b-and (c- a0))
      (g1 (z1) b-and (c- a1))
      (g2 (z2) b-and (c- a2))
      (g3 (z3) b-and (c- a3))))))

(assert-event (net-syntax-okp *v-if-f-4*) :on-skip-proofs t)
(assert-event (net-arity-okp *v-if-f-4*) :on-skip-proofs t)

(defthm len-f$v-if-f-4
  (equal (len (f$v-if-f-4 c a))
         4))

(defthm v-if-f-4$value
  (equal (se 'v-if-f-4 (list* c a) st *v-if-f-4*)
         (f$v-if-f-4 c a))
  :hints (("Goal"
           :expand (se 'v-if-f-4 (list* c a) st *v-if-f-4*)
           :in-theory (enable de-rules))))

(defthm f$v-if-f-4=fv-if
  (implies (and (booleanp c)
                (equal (len a) 4))
           (equal (f$v-if-f-4 c a)
                  (fv-if c (make-list 4) a)))
  :hints (("Goal" :in-theory (enable fv-if))))

(defund v-if-f-4& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (netlist-hyps netlist v-if-f-4))

(defthm v-if-f-4$reset-value
  (implies (v-if-f-4& netlist)
           (equal (se 'v-if-f-4 (list* t a) st netlist)
                  (make-list 4)))
  :hints (("Goal"
           :expand (se 'v-if-f-4 (list* t a) st netlist)
           :in-theory (enable de-rules
                              v-if-f-4&))))

(in-theory (disable f$v-if-f-4))

;; ======================================================================

;; FANOUT-4
;; FANOUT-5
;; FANOUT-32

(defconst *fanout-4*
  '((fanout-4
     (a)
     (z0 z1 z2 z3)
     ()
     ((aa (aa) b-buf (a))
      (g0 (z0) wire (aa))
      (g1 (z1) wire (aa))
      (g2 (z2) wire (aa))
      (g3 (z3) wire (aa))))))

(assert-event (net-syntax-okp *fanout-4*) :on-skip-proofs t)
(assert-event (net-arity-okp *fanout-4*) :on-skip-proofs t)

(defund fanout-4& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (netlist-hyps netlist fanout-4))

(defthm fanout-4$value
  (implies (fanout-4& netlist)
           (equal (se 'fanout-4 (list a) st netlist)
                  (make-list 4 :initial-element (3v-fix a))))
  :hints (("Goal"
           :expand (se 'fanout-4 (list a) st netlist)
           :in-theory (enable de-rules fanout-4& 3vp))))

(defconst *fanout-5*
  '((fanout-5
     (a)
     (z0 z1 z2 z3 z4)
     ()
     ((aa (aa) b-buf (a))
      (g0 (z0) wire (aa))
      (g1 (z1) wire (aa))
      (g2 (z2) wire (aa))
      (g3 (z3) wire (aa))
      (g4 (z4) wire (aa))))))

(assert-event (net-syntax-okp *fanout-5*) :on-skip-proofs t)
(assert-event (net-arity-okp *fanout-5*) :on-skip-proofs t)

(defund fanout-5& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (netlist-hyps netlist fanout-5))

(defthm fanout-5$value
  (implies (fanout-5& netlist)
           (equal (se 'fanout-5 (list a) st netlist)
                  (make-list 5 :initial-element (3v-fix a))))
  :hints (("Goal"
           :expand (se 'fanout-5 (list a) st netlist)
           :in-theory (enable de-rules fanout-5& 3vp))))

;; (defconst *fanout-32*
;;   (cons
;;   '(fanout-32
;;     (a)
;;     (s0 s1 s2 s3 s4 s5 s6 s7
;;         s8 s9 s10 s11 s12 s13 s14 s15
;;         s16 s17 s18 s19 s20 s21 s22 s23
;;         s24 s25 s26 s27 s28 s29 s30 s31)
;;     ()
;;     ((ga (aa) b-buf-pwr (a))
;;      (g0 (s0) wire (aa))
;;      (g1 (s1) wire (aa))
;;      (g2 (s2) wire (aa))
;;      (g3 (s3) wire (aa))
;;      (g4 (s4) wire (aa))
;;      (g5 (s5) wire (aa))
;;      (g6 (s6) wire (aa))
;;      (g7 (s7) wire (aa))
;;      (g8 (s8) wire (aa))
;;      (g9 (s9) wire (aa))
;;      (g10 (s10) wire (aa))
;;      (g11 (s11) wire (aa))
;;      (g12 (s12) wire (aa))
;;      (g13 (s13) wire (aa))
;;      (g14 (s14) wire (aa))
;;      (g15 (s15) wire (aa))
;;      (g16 (s16) wire (aa))
;;      (g17 (s17) wire (aa))
;;      (g18 (s18) wire (aa))
;;      (g19 (s19) wire (aa))
;;      (g20 (s20) wire (aa))
;;      (g21 (s21) wire (aa))
;;      (g22 (s22) wire (aa))
;;      (g23 (s23) wire (aa))
;;      (g24 (s24) wire (aa))
;;      (g25 (s25) wire (aa))
;;      (g26 (s26) wire (aa))
;;      (g27 (s27) wire (aa))
;;      (g28 (s28) wire (aa))
;;      (g29 (s29) wire (aa))
;;      (g30 (s30) wire (aa))
;;      (g31 (s31) wire (aa))))

;;   *b-buf-pwr*))

;; (assert-event (net-syntax-okp *fanout-32*) :on-skip-proofs t)
;; (assert-event (net-arity-okp *fanout-32*) :on-skip-proofs t)

;; (defund fanout-32& (netlist)
;;   (declare (xargs :guard (alistp netlist)))
;;   (and (netlist-hyps netlist fanout-32)
;;        (b-buf-pwr& (delete-to-eq 'fanout-32 netlist))))

;; (defthm fanout-32$value
;;   (implies (fanout-32& netlist)
;;            (equal (se 'fanout-32 (list a) st netlist)
;;                   (make-list 32 :initial-element (3v-fix a))))
;;   :hints (("Goal"
;;            :expand (se 'fanout-32 (list a) st netlist)
;;            :in-theory (enable de-rules
;;                               fanout-32&
;;                               3vp))))

;; ======================================================================

;; DECODE-5
;; A 5-to-32, one-hot decoder

(defun f$decode-5 (s)
  (declare (xargs :guard (true-listp s)))
  (let ((s0 (car s))
        (s1 (cadr s))
        (s2 (caddr s))
        (s3 (cadddr s))
        (s4 (car (cddddr s))))
    (let ((s0- (f-not s0))
          (s1- (f-not s1))
          (s2- (f-not s2))
          (s3- (f-not s3))
          (s4- (f-not s4)))
      (let ((s0 (f-not s0-))
            (s1 (f-not s1-))
            (s2 (f-not s2-))
            (s3 (f-not s3-))
            (s4 (f-not s4-)))
        (let ((l0 (f-nand s0- s1-))
              (l1 (f-nand s0 s1-))
              (l2 (f-nand s0- s1))
              (l3 (f-nand s0 s1))
              (h0 (f-nand3 s2- s3- s4-))
              (h1 (f-nand3 s2 s3- s4-))
              (h2 (f-nand3 s2- s3 s4-))
              (h3 (f-nand3 s2 s3 s4-))
              (h4 (f-nand3 s2- s3- s4))
              (h5 (f-nand3 s2 s3- s4))
              (h6 (f-nand3 s2- s3 s4))
              (h7 (f-nand3 s2 s3 s4)))
          (let ((x00 (f-nor l0 h0))
                (x10 (f-nor l1 h0))
                (x20 (f-nor l2 h0))
                (x30 (f-nor l3 h0))
                (x01 (f-nor l0 h1))
                (x11 (f-nor l1 h1))
                (x21 (f-nor l2 h1))
                (x31 (f-nor l3 h1))
                (x02 (f-nor l0 h2))
                (x12 (f-nor l1 h2))
                (x22 (f-nor l2 h2))
                (x32 (f-nor l3 h2))
                (x03 (f-nor l0 h3))
                (x13 (f-nor l1 h3))
                (x23 (f-nor l2 h3))
                (x33 (f-nor l3 h3))
                (x04 (f-nor l0 h4))
                (x14 (f-nor l1 h4))
                (x24 (f-nor l2 h4))
                (x34 (f-nor l3 h4))
                (x05 (f-nor l0 h5))
                (x15 (f-nor l1 h5))
                (x25 (f-nor l2 h5))
                (x35 (f-nor l3 h5))
                (x06 (f-nor l0 h6))
                (x16 (f-nor l1 h6))
                (x26 (f-nor l2 h6))
                (x36 (f-nor l3 h6))
                (x07 (f-nor l0 h7))
                (x17 (f-nor l1 h7))
                (x27 (f-nor l2 h7))
                (x37 (f-nor l3 h7)))
            (list x00 x10 x20 x30 x01 x11 x21 x31 x02 x12 x22 x32 x03 x13 x23
                  x33 x04 x14 x24 x34 x05 x15 x25 x35 x06 x16 x26 x36 x07 x17
                  x27 x37)))))))

(defthm len-f$decode-5
  (equal (len (f$decode-5 s)) 32))

(defun decode-5 (s)
  (declare (xargs :guard (true-listp s)))
  (let ((s0 (car s))
        (s1 (cadr s))
        (s2 (caddr s))
        (s3 (cadddr s))
        (s4 (car (cddddr s))))
    (let ((s0- (b-not s0))
          (s1- (b-not s1))
          (s2- (b-not s2))
          (s3- (b-not s3))
          (s4- (b-not s4)))
      (let ((s0 (b-not s0-))
            (s1 (b-not s1-))
            (s2 (b-not s2-))
            (s3 (b-not s3-))
            (s4 (b-not s4-)))
        (let ((l0 (b-nand s0- s1-))
              (l1 (b-nand s0 s1-))
              (l2 (b-nand s0- s1))
              (l3 (b-nand s0 s1))
              (h0 (b-nand3 s2- s3- s4-))
              (h1 (b-nand3 s2 s3- s4-))
              (h2 (b-nand3 s2- s3 s4-))
              (h3 (b-nand3 s2 s3 s4-))
              (h4 (b-nand3 s2- s3- s4))
              (h5 (b-nand3 s2 s3- s4))
              (h6 (b-nand3 s2- s3 s4))
              (h7 (b-nand3 s2 s3 s4)))
          (let ((x00 (b-nor l0 h0))
                (x10 (b-nor l1 h0))
                (x20 (b-nor l2 h0))
                (x30 (b-nor l3 h0))
                (x01 (b-nor l0 h1))
                (x11 (b-nor l1 h1))
                (x21 (b-nor l2 h1))
                (x31 (b-nor l3 h1))
                (x02 (b-nor l0 h2))
                (x12 (b-nor l1 h2))
                (x22 (b-nor l2 h2))
                (x32 (b-nor l3 h2))
                (x03 (b-nor l0 h3))
                (x13 (b-nor l1 h3))
                (x23 (b-nor l2 h3))
                (x33 (b-nor l3 h3))
                (x04 (b-nor l0 h4))
                (x14 (b-nor l1 h4))
                (x24 (b-nor l2 h4))
                (x34 (b-nor l3 h4))
                (x05 (b-nor l0 h5))
                (x15 (b-nor l1 h5))
                (x25 (b-nor l2 h5))
                (x35 (b-nor l3 h5))
                (x06 (b-nor l0 h6))
                (x16 (b-nor l1 h6))
                (x26 (b-nor l2 h6))
                (x36 (b-nor l3 h6))
                (x07 (b-nor l0 h7))
                (x17 (b-nor l1 h7))
                (x27 (b-nor l2 h7))
                (x37 (b-nor l3 h7)))
            (list x00 x10 x20 x30 x01 x11 x21 x31 x02 x12 x22 x32 x03 x13 x23
                  x33 x04 x14 x24 x34 x05 x15 x25 x35 x06 x16 x26 x36 x07 x17
                  x27 x37)))))))

(defthm bvp-decode-5
  (bvp (decode-5 s))
  :rule-classes (:rewrite :type-prescription))

(defthm len-decode-5
  (equal (len (decode-5 s)) 32))

(defconst *decode-5*
  '((decode-5
     (s0 s1 s2 s3 s4)
     (x00 x10 x20 x30 x01 x11 x21 x31 x02 x12 x22 x32
          x03 x13 x23 x33 x04 x14 x24 x34 x05 x15 x25 x35
          x06 x16 x26 x36 x07 x17 x27 x37)
     ()
     ((gs0- (s0-) b-not   (s0))
      (gs1- (s1-) b-not   (s1))
      (gs2- (s2-) b-not   (s2))
      (gs3- (s3-) b-not   (s3))
      (gs4- (s4-) b-not   (s4))
      (gs0  (bs0) b-not   (s0-))
      (gs1  (bs1) b-not   (s1-))
      (gs2  (bs2) b-not   (s2-))
      (gs3  (bs3) b-not   (s3-))
      (gs4  (bs4) b-not   (s4-))
      (gl0  (l0)  b-nand  (s0- s1-))
      (gl1  (l1)  b-nand  (bs0 s1-))
      (gl2  (l2)  b-nand  (s0- bs1))
      (gl3  (l3)  b-nand  (bs0 bs1))
      (gh0  (h0)  b-nand3 (s2- s3- s4-))
      (gh1  (h1)  b-nand3 (bs2 s3- s4-))
      (gh2  (h2)  b-nand3 (s2- bs3 s4-))
      (gh3  (h3)  b-nand3 (bs2 bs3 s4-))
      (gh4  (h4)  b-nand3 (s2- s3- bs4))
      (gh5  (h5)  b-nand3 (bs2 s3- bs4))
      (gh6  (h6)  b-nand3 (s2- bs3 bs4))
      (gh7  (h7)  b-nand3 (bs2 bs3 bs4))
      (gx00 (x00) b-nor   (l0 h0))
      (gx10 (x10) b-nor   (l1 h0))
      (gx20 (x20) b-nor   (l2 h0))
      (gx30 (x30) b-nor   (l3 h0))
      (gx01 (x01) b-nor   (l0 h1))
      (gx11 (x11) b-nor   (l1 h1))
      (gx21 (x21) b-nor   (l2 h1))
      (gx31 (x31) b-nor   (l3 h1))
      (gx02 (x02) b-nor   (l0 h2))
      (gx12 (x12) b-nor   (l1 h2))
      (gx22 (x22) b-nor   (l2 h2))
      (gx32 (x32) b-nor   (l3 h2))
      (gx03 (x03) b-nor   (l0 h3))
      (gx13 (x13) b-nor   (l1 h3))
      (gx23 (x23) b-nor   (l2 h3))
      (gx33 (x33) b-nor   (l3 h3))
      (gx04 (x04) b-nor   (l0 h4))
      (gx14 (x14) b-nor   (l1 h4))
      (gx24 (x24) b-nor   (l2 h4))
      (gx34 (x34) b-nor   (l3 h4))
      (gx05 (x05) b-nor   (l0 h5))
      (gx15 (x15) b-nor   (l1 h5))
      (gx25 (x25) b-nor   (l2 h5))
      (gx35 (x35) b-nor   (l3 h5))
      (gx06 (x06) b-nor   (l0 h6))
      (gx16 (x16) b-nor   (l1 h6))
      (gx26 (x26) b-nor   (l2 h6))
      (gx36 (x36) b-nor   (l3 h6))
      (gx07 (x07) b-nor   (l0 h7))
      (gx17 (x17) b-nor   (l1 h7))
      (gx27 (x27) b-nor   (l2 h7))
      (gx37 (x37) b-nor   (l3 h7))))))

(assert-event (net-syntax-okp *decode-5*) :on-skip-proofs t)
(assert-event (net-arity-okp *decode-5*) :on-skip-proofs t)

(defund decode-5& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (netlist-hyps netlist decode-5))

(defthm decode-5$value
  (implies (decode-5& netlist)
           (equal (se 'decode-5 s st netlist)
                  (f$decode-5 s)))
  :hints (("Goal"
           :expand (se 'decode-5 s st netlist)
           :in-theory (enable de-rules decode-5&))))

(defthm f$decode-5=decode-5
  (implies (bvp s)
           (equal (f$decode-5 s)
                  (decode-5 s)))
  :hints (("Goal" :in-theory (e/d (bvp)
                                  (b-gates)))))

(in-theory (disable f$decode-5 decode-5))

;; ======================================================================

;; ENCODE-32
;; A 32-to-5 encoder, assuming a one-hot input vector

;; This encoder is optimized to eliminate encoding of the unused states S26,
;; S27, and S31.

(fn-to-module
 encode-32 (s0 s1 s2 s3 s4 s5 s6 s7
               s8 s9 s10 s11 s12 s13 s14 s15
               s16 s17 s18 s19 s20 s21 s22 s23
               s24 s25 s26 s27 s28 s29 s30 s31)
 (declare (xargs :guard t)
          (ignore s0))
 (let ((x0a (b-nor4 s1 s3 s5 s7))
       (x0b (b-nor4 s9 s11 s13 s15))
       (x0c (b-nor4 s17 s19 s21 s23))
       (x0d (b-nor4 s25 s27 s29 s31))
       (x1a (b-nor4 s2 s3 s6 s7))
       (x1b (b-nor4 s10 s11 s14 s15))
       (x1c (b-nor4 s18 s19 s22 s23))
       (x1d (b-nor4 s26 s27 s30 s31))
       (x2a (b-nor4 s4 s5 s6 s7))
       (x2b (b-nor4 s12 s13 s14 s15))
       (x2c (b-nor4 s20 s21 s22 s23))
       (x2d (b-nor4 s28 s29 s30 s31))
       (x3a (b-nor4 s8 s9 s10 s11))
       (x3b (b-nor4 s12 s13 s14 s15))
       (x3c (b-nor4 s24 s25 s26 s27))
       (x3d (b-nor4 s28 s29 s30 s31))
       (x4a (b-nor4 s16 s17 s18 s19))
       (x4b (b-nor4 s20 s21 s22 s23))
       (x4c (b-nor4 s24 s25 s26 s27))
       (x4d (b-nor4 s28 s29 s30 s31)))
   (let ((x0 (b-nand4 x0a x0b x0c x0d))
         (x1 (b-nand4 x1a x1b x1c x1d))
         (x2 (b-nand4 x2a x2b x2c x2d))
         (x3 (b-nand4 x3a x3b x3c x3d))
         (x4 (b-nand4 x4a x4b x4c x4d)))
     (list x0 x1 x2 x3 x4))))

(defthm bvp-encode-32
  (bvp (encode-32 s0 s1 s2 s3 s4 s5 s6 s7
                  s8 s9 s10 s11 s12 s13 s14 s15
                  s16 s17 s18 s19 s20 s21 s22 s23
                  s24 s25 s26 s27 s28 s29 s30 s31))
  :hints (("Goal" :in-theory (e/d (bvp encode-32)
                                  (b-gates))))
  :rule-classes (:rewrite :type-prescription))

(defthm len-encode-32
  (equal (len (encode-32 s0 s1 s2 s3 s4 s5 s6 s7
                         s8 s9 s10 s11 s12 s13 s14 s15
                         s16 s17 s18 s19 s20 s21 s22 s23
                         s24 s25 s26 s27 s28 s29 s30 s31))
         5)
  :hints (("Goal" :in-theory (e/d (encode-32)
                                  (b-gates)))))

(defthm len-f$encode-32
  (equal (len (f$encode-32 s0 s1 s2 s3 s4 s5 s6 s7
                           s8 s9 s10 s11 s12 s13 s14 s15
                           s16 s17 s18 s19 s20 s21 s22 s23
                           s24 s25 s26 s27 s28 s29 s30 s31))
         5)
  :hints (("Goal" :in-theory (e/d (f$encode-32)
                                  (b-gates)))))

(defthmd se-on-collected-nth-32
  (implies (and (equal (len ins) 32)
                (true-listp ins))
           (equal (se name ins st netlist)
                  (se name
                      (list (nth 0 ins)
                            (nth 1 ins)
                            (nth 2 ins)
                            (nth 3 ins)
                            (nth 4 ins)
                            (nth 5 ins)
                            (nth 6 ins)
                            (nth 7 ins)
                            (nth 8 ins)
                            (nth 9 ins)
                            (nth 10 ins)
                            (nth 11 ins)
                            (nth 12 ins)
                            (nth 13 ins)
                            (nth 14 ins)
                            (nth 15 ins)
                            (nth 16 ins)
                            (nth 17 ins)
                            (nth 18 ins)
                            (nth 19 ins)
                            (nth 20 ins)
                            (nth 21 ins)
                            (nth 22 ins)
                            (nth 23 ins)
                            (nth 24 ins)
                            (nth 25 ins)
                            (nth 26 ins)
                            (nth 27 ins)
                            (nth 28 ins)
                            (nth 29 ins)
                            (nth 30 ins)
                            (nth 31 ins))
                      st
                      netlist)))
  :hints (("Goal"
           :in-theory (disable nth)
           :use (:instance equal-len-32-as-collected-nth
                           (l ins))
           :do-not-induct t)))

(defthm encode-32$value-on-a-vector
  (implies (and (encode-32& netlist)
                (true-listp ins)
                (equal (len ins) 32))
           (equal (se 'encode-32 ins st netlist)
                  (f$encode-32 (nth 0 ins)
                               (nth 1 ins)
                               (nth 2 ins)
                               (nth 3 ins)
                               (nth 4 ins)
                               (nth 5 ins)
                               (nth 6 ins)
                               (nth 7 ins)
                               (nth 8 ins)
                               (nth 9 ins)
                               (nth 10 ins)
                               (nth 11 ins)
                               (nth 12 ins)
                               (nth 13 ins)
                               (nth 14 ins)
                               (nth 15 ins)
                               (nth 16 ins)
                               (nth 17 ins)
                               (nth 18 ins)
                               (nth 19 ins)
                               (nth 20 ins)
                               (nth 21 ins)
                               (nth 22 ins)
                               (nth 23 ins)
                               (nth 24 ins)
                               (nth 25 ins)
                               (nth 26 ins)
                               (nth 27 ins)
                               (nth 28 ins)
                               (nth 29 ins)
                               (nth 30 ins)
                               (nth 31 ins))))
  :hints (("Goal"
           :use (:instance se-on-collected-nth-32
                           (name 'encode-32))
           :in-theory (e/d ()
                           (nth)))))

