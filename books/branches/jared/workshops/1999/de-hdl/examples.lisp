;;;                         DE EXAMPLES

;;;  examples.lisp                         Warren A. Hunt, Jr.

;;;  This file contains some example DE circuits.

(in-package "ACL2")

(include-book "de4")

(defconst *netlist1*
        '((four-bit-counter
           (incr reset-)
           (out0 out1 out2 out3)
           (h0 h1 h2 h3)
           ((h0 (out0 carry0) one-bit-counter (incr   reset-))
            (h1 (out1 carry1) one-bit-counter (carry0 reset-))
            (h2 (out2 carry2) one-bit-counter (carry1 reset-))
            (h3 (out3 carry3) one-bit-counter (carry2 reset-))))

          (one-bit-counter
           (carry-in reset-)
           (out carry)
           (r0)
           ((r0 (out)          ff         (sum-reset))
            (r1 (sum carry)    half-adder (carry-in out))
            (r2 (sum-reset)    and        (sum reset-))))

          (three-bit-adder
           (c a0 a1 a2 b0 b1 b2)
           (sum0 sum1 sum2 carry)
           ()
           ((m0 (sum0 carry1) full-adder (a0 b0 c))
            (m1 (sum1 carry2) full-adder (a1 b1 carry1))
            (m1 (sum2 carry)  full-adder (a2 b2 carry2))))

          (full-adder
           (c a b)
           (sum carry)
           ()
           ((t0 (sum1 carry1) half-adder (a b))
            (t1 (sum  carry2) half-adder (sum1 c))
            (t2 (carry)       or         (carry1 carry2))))

          (half-adder
           (a b)
           (sum carry)
           ()
           ((g0 (sum)   xor (a b))
            (g1 (carry) and (a b))))
          ))

(defthm net-syntax-okp-netlist1
  (net-syntax-okp *netlist1*)
  :rule-classes nil)

(defthm net-arity-okp-netlist1
  (net-arity-okp  *netlist1*)
  :rule-classes nil)

(defthm sts-okp-one-bit-counter
  (sts-okp   'one-bit-counter
             '((nil))
             *netlist1*)
  :rule-classes nil)

(defthm sts-okp-four-bit-counter
  (sts-okp   'four-bit-counter
             '(((nil)) ((nil)) ((nil)) ((nil)))
             *netlist1*)
  :rule-classes nil)

(defthm de-sim-four-bit-counter
  (equal (de-sim 'four-bit-counter
                 '((  t t)
                   (nil t)
                   (  t t)
                   (  t t)
                   (nil t)
                   (  t t))
                 '(((nil))((nil))((nil))((nil)))
                 *netlist1*)
         '(((nil)) ((nil)) ((t)) ((nil))))
  :rule-classes nil)

;;;  A larger netlist.

(defconst *f74181-netlist*
        '((f74181
           (c~ a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)
           (f0 f1 f2 f3 cout~ p~ g~ a=b)
           ()
           (
            (g-w0    (w0)    not   (m))
            (g-w1    (w1)    not   (b0))
            (g-w2    (w2)    not   (b1))
            (g-w3    (w3)    not   (b2))
            (g-w4    (w4)    not   (b3))
            (g-w5    (w5)    buf   (a0))
            (g-w6    (w6)    and   (b0 s0))
            (g-w7    (w7)    and   (s1 w1))
            (g-w8    (w8)    and3  (w1 s2 a0))
            (g-w9    (w9)    and3  (a0 s3 b0))
            (g-w10   (w10)   buf   (a1))
            (g-w11   (w11)   and   (b1 s0))
            (g-w12   (w12)   and   (s1 w2))
            (g-w13   (w13)   and3  (w2 s2 a1))
            (g-w14   (w14)   and3  (a1 s3 b1))
            (g-w15   (w15)   buf   (a2))
            (g-w16   (w16)   and   (b2 s0))
            (g-w17   (w17)   and   (s1 w3))
            (g-w18   (w18)   and3  (w3 s2 a2))
            (g-w19   (w19)   and3  (a2 s3 b2))
            (g-w20   (w20)   buf   (a3))
            (g-w21   (w21)   and   (b3 s0))
            (g-w22   (w22)   and   (s1 w4))
            (g-w23   (w23)   and3  (w4 s2 a3))
            (g-w24   (w24)   and3  (a3 s3 b3))
            (g-w25   (w25)   nor3  (w5 w6 w7))
            (g-w26   (w26)   nor   (w8 w9))
            (g-w27   (w27)   nor3  (w10 w11 w12))
            (g-w28   (w28)   nor   (w13 w14))
            (g-w29   (w29)   nor3  (w15 w16 w17))
            (g-w30   (w30)   nor   (w18 w19))
            (g-w31   (w31)   nor3  (w20 w21 w22))
            (g-w32   (w32)   nor   (w23 w24))
            (g-w33   (w33)   xor   (w25 w26))
            (g-w34   (w34)   xor   (w27 w28))
            (g-w35   (w35)   xor   (w29 w30))
            (g-w36   (w36)   xor   (w31 w32))
            (g-w37   (w37)   nand  (w0 c~))
            (g-w38   (w38)   and   (w0 w25))
            (g-w39   (w39)   and3  (w0 w26 c~))
            (g-w40   (w40)   and   (w0 w27))
            (g-w41   (w41)   and3  (w0 w25 w28))
            (g-w42   (w42)   and4  (w0 w28 w26 c~))
            (g-w43   (w43)   and   (w0 w29))
            (g-w44   (w44)   and3  (w0 w27 w30))
            (g-w45   (w45)   and4  (w0 w25 w30 w28))
            (g-w46a  (w46a)  and   (w0 w30))
            (g-w46   (w46)   and4  (w46a w28 w26 c~))
            (g-w47   (w47)   nand4 (w26 w28 w30 w32))
            (g-w48a  (w48a)  and   (c~ w26))
            (g-w48   (w48)   nand4 (w48a w28 w30 w32))
            (g-w49   (w49)   and4  (w25 w28 w30 w32))
            (g-w50   (w50)   and3  (w27 w30 w32))
            (g-w51   (w51)   and   (w29 w32))
            (g-w52   (w52)   buf   (w31))
            (g-w53   (w53)   buf   (w37))
            (g-w54   (w54)   nor   (w38 w39))
            (g-w55   (w55)   nor3  (w40 w41 w42))
            (g-w56   (w56)   nor4  (w43 w44 w45 w46))
            (g-w57   (w57)   nor4  (w49 w50 w51 w52))
            (g-w58   (w58)   xor   (w53 w33))
            (g-w59   (w59)   xor   (w54 w34))
            (g-w60   (w60)   xor   (w55 w35))
            (g-w61   (w61)   xor   (w56 w36))
            (g-w62a  (w62a)  not   (w48))
            (g-w62b  (w62b)  not   (w57))
            (g-w62   (w62)   or    (w62a w62b))
            (g-w63   (w63)   and4  (w58 w59 w60 w61))
            (g-f0    (f0)    buf   (w58))
            (g-f1    (f1)    buf   (w59))
            (g-f2    (f2)    buf   (w60))
            (g-f3    (f3)    buf   (w61))
            (g-a=b   (a=b)   buf   (w63))
            (g-p~    (p~)    buf   (w47))
            (g-cout~ (cout~) buf   (w62))
            (g-g~    (g~)    buf   (w57)))
           )))

(defthm net-syntax-okp-f74181-netlist
  (net-syntax-okp *f74181-netlist*)
  :rule-classes nil)

(defthm net-arity-okp-f74181-netlist
  (net-arity-okp *f74181-netlist*)
  :rule-classes nil)
