;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

(in-package "FM9001")

(include-book "alu-spec")
(include-book "de")
(include-book "macros")

;; ======================================================================

;; The ALU decoders, and CARRY-IN-HELP

#|

This table shows the settings of the mode, propagate, and generate lines for
each op-code that are computed by DECODE-MODE, DECODE-PROP, and DECODE-GEN
respectively.  Further, it shows carry-in, carry-out, and overflow requirements
that are implemented by CARRY-IN-HELP, CARRY-OUT-HELP, and OVERFLOW-HELP
respectively.  This table is valid assuming that the SWAP input to DECODE-MODE
and DECODE-GEN is true only when the op-code is either ALU-INC-OP or
ALU-DEC-OP.  (The SWAP input is normally F; it is set to T only in the cases
where the B operand is incremented or decremented.)  Also note that the control
logic must set the op-code to ALU-INC-OP whenever the ZERO flag is T.


 FM9001   Mode  Prop  Gen C-in  C-out  Ovfl  Comment
 opcode         aab   aab
 3210            n     nn

 0000     f     tff   ttf   x   f      f     Move
 0001     t     -f+   ttf   t   co     *     Increment
 0010     t     tft   ftt   c   co     *     AddC
 0011     t     tft   ftt   f   co     *     Add
 0100     t     ftf   ttf   t   ~co    *     Negation
 0101     t     ttf   f-+   f   ~co    *     Decrement
 0110     t     ftt   tft   ~c  ~co    *     SubB
 0111     t     ftt   tft   t   ~co    *     Sub
 1000     f     tff   ttf   c   c|a0   f     Move (ROR)
 1001     f     tff   ttf   x   a0     f     Move (ASR)
 1010     f     tff   ttf   x   a0     f     Move (LSR)
 1011     f     tff   fft   x   f      f     XOR
 1100     f     tft   ttf   x   f      f     Or
 1101     f     fff   ftt   x   f      f     And
 1110     f     ftf   ttf   x   f      f     Not
 1111     f     tff   ttf   x   f      f     Move

 ZERO     t     fff   fff   t   f      f     ZERO

+/- = swap/~swap

* -- Overflow equations.  a = A(n), b = B(n), out = out(n)

x110.a.~b.out + x110.~a.b.~out     Sub,Subb
1010.a.~out                        Dec
0010.a.out                         Neg
x100.a.b.~out + x100.~a.~b.out     Add,Addc
1000.~a.out                        Inc

|#

;; DECODE-MODE

;; Mode = T for arithmetic operations, and ZEROing.

(fn-to-module
 decode-mode (op0 op1 op2 op3)
 (declare (xargs :guard t))
 (b-nor (b-nor3 op0 op1 op2)
        op3))

(defthmd decode-mode$value-zero
  (implies (decode-mode& netlist)
           (equal (se 'decode-mode (alu-inc-op) sts netlist)
                  *v1*))
  :hints (("Goal" :in-theory (enable decode-mode$value))))

;; DECODE-PROP == (LIST PB PAN PA)

(fn-to-module
 decode-prop (zero swap op0 op1 op2 op3)
 (declare (xargs :guard t))
 (let ((zero- (b-not zero))
       (swap- (b-not swap))
       (op0-  (b-not op0))
       (op1-  (b-not op1))
       (op2-  (b-not op2))
       (op3-  (b-not op3)))
   (let (;;(zero (b-not zero-))
         (swap  (b-not swap-))
         (op0   (b-not op0-))
         (op1   (b-not op1-))
         (op2   (b-not op2-))
         (op3   (b-not op3-)))
     (let ((out0 (b-nand3 (b-nand4 op0- op1- op2 op3)
                          (b-nand op1 op3-)
                          (b-nand3 op2- op3- swap)))
           (out1 (b-nor op2- (b-nor op3- (b-nor op0 op1-))))
           (out2 (b-and (b-nand3 (b-nand op3 (b-equv op0 op1))
                                 (b-nand op2- (b-nand swap op3-))
                                 (b-nand4 op0 op1- op2 op3-))
                        zero-)))
       (list out0 out1 out2)))))

(defthmd decode-prop$value-zero
  (implies (decode-prop& netlist)
           (equal (se 'decode-prop (list* t nil (alu-inc-op)) sts netlist)
                  *v000*))
  :hints (("Goal" :in-theory (enable decode-prop$value))))

;; DECODE-GEN = (LIST GBN GAN GA)

(fn-to-module
 decode-gen (zero swap op0 op1 op2 op3)
 (declare (xargs :guard t))
 (let ((zero- (b-not zero))
       (swap- (b-not swap))
       (op0-  (b-not op0))
       (op1-  (b-not op1))
       (op2-  (b-not op2))
       (op3-  (b-not op3)))
   (let ((zero (b-not zero-))
         ;;(swap (b-not swap-))
         (op0  (b-not op0-))
         (op1  (b-not op1-))
         (op2  (b-not op2-))
         (op3  (b-not op3-)))
     (let ((out0 (b-nand3 (b-nand3 op0 op3 (b-xor op1 op2))
                          (b-nand3 op2 op3- (b-nand op1- swap-))
                          (b-nand3 op1 op2- op3-)))
           (out1 (b-nor (b-nand (b-nand4 op0 op1 op2- op3)
                                (b-nand3 op2 op3- (b-nand op1- swap-)))
                        zero))
           (out2 (b-nor (b-nand3 (b-nand3 op0 op3 (b-xor op1 op2))
                                 (b-nand3 op0 op1- op2)
                                 (b-nand3 op1 op2- op3-))
                        zero)))
       (list out0 out1 out2)))))

(defthmd decode-gen$value-zero
  (implies (decode-gen& netlist)
           (equal (se 'decode-gen (list* t nil (alu-inc-op)) sts netlist)
                  *v000*))
  :hints (("Goal" :in-theory (enable decode-gen$value))))

;; MPG == (LIST GBN GAN GA PB PAN PA M)

(defun f$mpg (zsop)
  (declare (xargs :guard (true-listp zsop)))
  (let ((zero (car zsop))
        (swap (cadr zsop))
        (op0 (caddr zsop))
        (op1 (cadddr zsop))
        (op2 (car (cddddr zsop)))
        (op3 (cadr (cddddr zsop))))
    (append (f$decode-gen zero swap op0 op1 op2 op3)
            (append (f$decode-prop zero swap op0 op1 op2 op3)
                    (list (f$decode-mode op0 op1 op2 op3))))))

(defun mpg (zsop)
  (declare (xargs :guard (true-listp zsop)))
  (let ((zero (car zsop))
        (swap (cadr zsop))
        (op0 (caddr zsop))
        (op1 (cadddr zsop))
        (op2 (car (cddddr zsop)))
        (op3 (cadr (cddddr zsop))))
    (append (decode-gen zero swap op0 op1 op2 op3)
            (append (decode-prop zero swap op0 op1 op2 op3)
                    (list (decode-mode op0 op1 op2 op3))))))

(defthm f$mpg=mpg
  (implies (bvp zsop)
           (equal (f$mpg zsop)
                  (mpg zsop)))
  :hints (("Goal" :in-theory (enable bvp))))

;; (defthm true-listp-f$mpg
;;   (true-listp (f$mpg zsop))
;;   :rule-classes :type-prescription)

(defthm len-f$mpg
  (equal (len (f$mpg zsop)) 7)
  :hints (("Goal" :in-theory (enable f$decode-gen f$decode-prop))))

(defthm bvp-mpg
  (bvp (mpg zsop))
  :hints (("Goal" :in-theory (enable decode-gen decode-prop decode-mode)))
  :rule-classes (:rewrite :type-prescription))

(defthm len-mpg
  (equal (len (mpg zsop)) 7)
  :hints (("Goal" :in-theory (enable decode-gen decode-prop))))

(defthm mpg-if-op-code
  (equal (mpg (cons a (cons b (if c d e))))
         (if c
             (mpg (cons a (cons b d)))
           (mpg (cons a (cons b e))))))

(defthmd mpg-zero
  (equal (mpg (cons t (cons nil (alu-inc-op))))
         *v1000000*))

(defconst *mpg*
  (cons
  '(mpg
    (zero swap op0 op1 op2 op3)
    (gbn gan ga pb pan pa mode)
    ()
    ((m (mode)       decode-mode (op0 op1 op2 op3))
     (p (pb pan pa)  decode-prop (zero swap op0 op1 op2 op3))
     (g (gbn gan ga) decode-gen  (zero swap op0 op1 op2 op3))))

  (append *decode-mode* *decode-prop* *decode-gen*)))

(defthmd mpg-okp
  (and (net-syntax-okp *mpg*)
       (net-arity-okp *mpg*)))

(defund mpg& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (and (netlist-hyps netlist mpg)
       (b* ((netlist (delete-to-eq 'mpg netlist)))
         (and (decode-mode& netlist)
              (decode-prop& netlist)
              (decode-gen& netlist)))))

(defthmd mpg$value
  (implies (mpg& netlist)
           (equal (se 'mpg zsop sts netlist)
                  (f$mpg zsop)))
  :hints (("Goal" :in-theory (enable se-rules
                                      mpg&
                                      f$decode-mode
                                      f$decode-prop
                                      f$decode-gen
                                      decode-mode$value
                                      decode-prop$value
                                      decode-gen$value))))

(defthmd mpg$value-zero
  (implies (mpg& netlist)
           (equal (se 'mpg (list* t nil (alu-inc-op)) sts netlist)
                  *v1000000*))
   :hints (("Goal" :in-theory (enable mpg$value))))

(in-theory (disable f$mpg mpg))

;; CARRY-IN-HELP

(defun carry-in-help (czop)
  (declare (xargs :guard (true-listp czop)))
  (let ((c   (car czop))
        ;;(z   (cadr czop))
        (op0 (caddr czop))
        (op1 (cadddr czop))
        (op2 (car (cddddr czop)))
        (op3 (cadr (cddddr czop))))
    (let ((c-   (b-not c))
          (op0- (b-not op0))
          (op1- (b-not op1))
          (op2- (b-not op2))
          (op3- (b-not op3)))
      (let ((c   (b-not c-))
            (op0 (b-not op0-))
            (op1 (b-not op1-))
            (op2 (b-not op2-))
            (op3 (b-not op3-)))

        (b-or (b-nand3 (b-nand3 op1- op2- op3-)
                       (b-nand3 op0- op1- op2)
                       (b-nand3 op0 op1 op2))
              (b-nand3 (b-nand op3 c)
                       (b-nand3 op0- op2- c)
                       (b-nand3 op0- op2 c-)))))))

(defun f$carry-in-help (czop)
  (declare (xargs :guard (true-listp czop)))
  (let ((c   (car czop))
        ;;(z   (cadr czop))
        (op0 (caddr czop))
        (op1 (cadddr czop))
        (op2 (car (cddddr czop)))
        (op3 (cadr (cddddr czop))))
    (let ((c-   (f-not c))
          (op0- (f-not op0))
          (op1- (f-not op1))
          (op2- (f-not op2))
          (op3- (f-not op3)))
      (let ((c   (f-not c-))
            (op0 (f-not op0-))
            (op1 (f-not op1-))
            (op2 (f-not op2-))
            (op3 (f-not op3-)))

        (f-or (f-nand3 (f-nand3 op1- op2- op3-)
                       (f-nand3 op0- op1- op2)
                       (f-nand3 op0 op1 op2))
              (f-nand3 (f-nand op3 c)
                       (f-nand3 op0- op2- c)
                       (f-nand3 op0- op2 c-)))))))

(defthm f$carry-in-help=carry-in-help
  (implies (bvp czop)
           (equal (f$carry-in-help czop)
                  (carry-in-help czop)))
   :hints (("Goal" :in-theory (enable bvp))))

(defconst *carry-in-help*
  '((carry-in-help
     (cin z op0in op1in op2in op3in)
     (cout)
     ()
     ((g0  (c- c)     b-nbuf  (cin))
      (g1  (op0- op0) b-nbuf  (op0in))
      (g2  (op1- op1) b-nbuf  (op1in))
      (g3  (op2- op2) b-nbuf  (op2in))
      (g4  (op3- op3) b-nbuf  (op3in))
      (g5  (s5)       b-nand3 (op1- op2- op3-))
      (g6  (s6)       b-nand3 (op0- op1- op2))
      (g7  (s7)       b-nand3 (op0 op1 op2))
      (g8  (s8)       b-nand3 (s5 s6 s7))
      (g9  (s9)       b-nand  (op3 c))
      (g10 (s10)      b-nand3 (op0- op2- c))
      (g11 (s11)      b-nand3 (op0- op2 c-))
      (g12 (s12)      b-nand3 (s9 s10 s11))
      (g13 (cout)     b-or    (s8 s12))))))

(defthmd carry-in-help-okp
  (and (net-syntax-okp *carry-in-help*)
       (net-arity-okp *carry-in-help*)))

(defthmd carry-in-help-zero
  (equal (carry-in-help (cons c (cons t (alu-inc-op))))
         t))

(defthm carry-in-help-if-op-code
  (equal (carry-in-help (cons a (cons b (if c d e))))
         (if c
             (carry-in-help (cons a (cons b d)))
           (carry-in-help (cons a (cons b e))))))

(defund carry-in-help& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (netlist-hyps netlist carry-in-help))

(defthmd carry-in-help$value
  (implies (carry-in-help& netlist)
           (equal (se 'carry-in-help czop sts netlist)
                  (list (f$carry-in-help czop))))
  :hints (("Goal" :in-theory (enable se-rules
                                      carry-in-help&
                                      f-not-f-not=f-buf))))

(defthmd carry-in-help$value-zero
  (implies (carry-in-help& netlist)
           (equal (se 'carry-in-help (list* c t (alu-inc-op)) sts netlist)
                  *v1*))
  :hints (("Goal" :in-theory (enable carry-in-help$value))))

(in-theory (disable carry-in-help f$carry-in-help))

