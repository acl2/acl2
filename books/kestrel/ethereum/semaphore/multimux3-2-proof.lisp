; Ethereum Semaphore Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZKSEMAPHORE")

(include-book "kestrel/ethereum/semaphore/prime-field-abbreviations" :dir :system)
(include-book "kestrel/ethereum/semaphore/json-to-r1cs/load-circom-json" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

; (depends-on "json/multimux3-2.json")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains a proof of the MultiMux3(2) ciruit component
; (see the Circom code of Semaphore).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Load the circuit.

(acl2::load-circom-json "json/multimux3-2.json" '(baby-jubjub-prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The circuit does not constrain s0, s1, and s2 to be bits (which it could).
; (If any sk is not a bit, the circuit does not work as intended.)
; There is also an implicit assumption that
; the inputs and outputs are field elements;
; without this assumption, we can only prove MOD-equivalence.
; So we collect all of these assumptions into a predicate:
; this is a precondition of the circuit.

(define precond (s2 s1 s0
                    c00 c01 c02 c03 c04 c05 c06 c07
                    c10 c11 c12 c13 c14 c15 c16 c17
                    out0 out1)
  :returns (yes/no booleanp)
  (and (bitp s2)
       (bitp s1)
       (bitp s0)
       (pfep c00)
       (pfep c01)
       (pfep c02)
       (pfep c03)
       (pfep c04)
       (pfep c05)
       (pfep c06)
       (pfep c07)
       (pfep c10)
       (pfep c11)
       (pfep c12)
       (pfep c13)
       (pfep c14)
       (pfep c15)
       (pfep c16)
       (pfep c17)
       (pfep out0)
       (pfep out1)))

; This is the functional specification of the circuit.
; Picturing the cij inputs as a table,
; the sk inputs (k in {0, 1, 2}), viewed as bits 0, 1, and 2 of a number s,
; select a column as the outi outputs.
;
;  +-----+-----+-----+-----+-----+-----+-----+-----+    +------+
;  | c00 | c01 | c02 | c03 | c04 | c05 | c06 | c07 |    | out0 |
;  +-----+-----+-----+-----+-----+-----+-----+-----+    +------+
;  | c10 | c11 | c12 | c13 | c14 | c15 | c16 | c17 |    | out1 |
;  +-----+-----+-----+-----+-----+-----+-----+-----+    +------+

(define multimux3-2 ((s2 bitp)
                     (s1 bitp)
                     (s0 bitp)
                     (c00 pfep)
                     (c01 pfep)
                     (c02 pfep)
                     (c03 pfep)
                     (c04 pfep)
                     (c05 pfep)
                     (c06 pfep)
                     (c07 pfep)
                     (c10 pfep)
                     (c11 pfep)
                     (c12 pfep)
                     (c13 pfep)
                     (c14 pfep)
                     (c15 pfep)
                     (c16 pfep)
                     (c17 pfep))
  :returns (mv (out0 pfep :hyp :guard)
               (out1 pfep :hyp :guard))
  (b* ((s (+ (* 4 s2) (* 2 s1) s0)))
    (mv (nth s (list c00 c01 c02 c03 c04 c05 c06 c07))
        (nth s (list c10 c11 c12 c13 c14 c15 c16 c17)))))

; To state the correctness of the circuit w.r.t the function above,
; we need to turn the function above into a predicate, in the obvious way.
; The relation says that outi = cis, for i in {0, 1} and s = 4*s2+2*s1+s0.

(define spec (s2 s1 s0
                 c00 c01 c02 c03 c04 c05 c06 c07
                 c10 c11 c12 c13 c14 c15 c16 c17
                 out0 out1)
  :guard (precond s2 s1 s0
                  c00 c01 c02 c03 c04 c05 c06 c07
                  c10 c11 c12 c13 c14 c15 c16 c17
                  out0 out1)
  :returns (yes/no booleanp)
  (b* (((mv out0$ out1$) (multimux3-2 s2 s1 s0
                                      c00 c01 c02 c03 c04 c05 c06 c07
                                      c10 c11 c12 c13 c14 c15 c16 c17)))
    (and (equal out0 out0$)
         (equal out1 out1$)))
  :guard-hints (("Goal" :in-theory (enable precond))))

; To state the correctness of the circuit w.r.t. the specification above,
; we need to turn the circuit into a predicate,
; which we do via the R1CS semantics applied to the circuit obtained by
; compiling the Circom file and then converting the resulting JSON file.
; This kind of predicate definition could be automatically generated
; from just the circuit via a macro.
; Note that, unlike the mux1 circuit,
; there are auxiliary variables here, i.e. a, a0, etc.
; Thus, it is convenient to define the circuit predicate in three parts:
; - A predicate that constrains the auxiliary variables to be field elements.
;   This is just a type predicate.
; - A core predicate over all the circuit variables,
;   including the auxiliary ones.
; - A predicate for the circuit, consisting of the core predicate
;   existentially quantified over the auxiliary variables,
;   which are constrained to be field elements.

(define auxp (s10 a210.0 a21.0 a20.0 a2.0 a10.0 a1.0 a0.0 a.0
                  a210.1 a21.1 a20.1 a2.1 a10.1 a1.1 a0.1 a.1)
  :returns (yes/no booleanp)
  (and (pfep s10)
       (pfep a210.0)
       (pfep a21.0)
       (pfep a20.0)
       (pfep a2.0)
       (pfep a10.0)
       (pfep a1.0)
       (pfep a0.0)
       (pfep a.0)
       (pfep a210.1)
       (pfep a21.1)
       (pfep a20.1)
       (pfep a2.1)
       (pfep a10.1)
       (pfep a1.1)
       (pfep a0.1)
       (pfep a.1)))

(define circuit-core (s2 s1 s0
                         c00 c01 c02 c03 c04 c05 c06 c07
                         c10 c11 c12 c13 c14 c15 c16 c17
                         out0 out1
                         s10
                         a210.0 a21.0 a20.0 a2.0 a10.0 a1.0 a0.0 a.0
                         a210.1 a21.1 a20.1 a2.1 a10.1 a1.1 a0.1 a.1)
  :guard (and (precond s2 s1 s0
                       c00 c01 c02 c03 c04 c05 c06 c07
                       c10 c11 c12 c13 c14 c15 c16 c17
                       out0 out1)
              (auxp s10 a210.0 a21.0 a20.0 a2.0 a10.0 a1.0 a0.0 a.0
                    a210.1 a21.1 a20.1 a2.1 a10.1 a1.1 a0.1 a.1))
  :returns (yes/no booleanp)
  (r1cs::r1cs-holdsp (acl2::multimux3-2-make-r1cs)
                     (list (cons :|main.s[2]| s2)
                           (cons :|main.s[1]| s1)
                           (cons :|main.s[0]| s0)
                           (cons :|main.c[0][0]| c00)
                           (cons :|main.c[0][1]| c01)
                           (cons :|main.c[0][2]| c02)
                           (cons :|main.c[0][3]| c03)
                           (cons :|main.c[0][4]| c04)
                           (cons :|main.c[0][5]| c05)
                           (cons :|main.c[0][6]| c06)
                           (cons :|main.c[0][7]| c07)
                           (cons :|main.c[1][0]| c10)
                           (cons :|main.c[1][1]| c11)
                           (cons :|main.c[1][2]| c12)
                           (cons :|main.c[1][3]| c13)
                           (cons :|main.c[1][4]| c14)
                           (cons :|main.c[1][5]| c15)
                           (cons :|main.c[1][6]| c16)
                           (cons :|main.c[1][7]| c17)
                           (cons :|main.out[0]| out0)
                           (cons :|main.out[1]| out1)
                           (cons :|main.s10| s10)
                           (cons :|main.a210[0]| a210.0)
                           (cons :|main.a21[0]| a21.0)
                           (cons :|main.a20[0]| a20.0)
                           (cons :|main.a2[0]| a2.0)
                           (cons :|main.a10[0]| a10.0)
                           (cons :|main.a1[0]| a1.0)
                           (cons :|main.a0[0]| a0.0)
                           (cons :|main.a[0]| a.0)
                           (cons :|main.a210[1]| a210.1)
                           (cons :|main.a21[1]| a21.1)
                           (cons :|main.a20[1]| a20.1)
                           (cons :|main.a2[1]| a2.1)
                           (cons :|main.a10[1]| a10.1)
                           (cons :|main.a1[1]| a1.1)
                           (cons :|main.a0[1]| a0.1)
                           (cons :|main.a[1]| a.1)))
  :guard-hints (("Goal" :in-theory (e/d (precond auxp r1cs::r1cs-valuationp)
                                        ((:e baby-jubjub-prime))))))

(define-sk circuit (s2 s1 s0
                       c00 c01 c02 c03 c04 c05 c06 c07
                       c10 c11 c12 c13 c14 c15 c16 c17
                       out0 out1)
  :guard (precond s2 s1 s0
                  c00 c01 c02 c03 c04 c05 c06 c07
                  c10 c11 c12 c13 c14 c15 c16 c17
                  out0 out1)
  :returns (yes/no booleanp)
  (exists (s10 a210.0 a21.0 a20.0 a2.0 a10.0 a1.0 a0.0 a.0
               a210.1 a21.1 a20.1 a2.1 a10.1 a1.1 a0.1 a.1)
          (and (auxp s10
                     a210.0 a21.0 a20.0 a2.0 a10.0 a1.0 a0.0 a.0
                     a210.1 a21.1 a20.1 a2.1 a10.1 a1.1 a0.1 a.1)
               (circuit-core s2 s1 s0
                             c00 c01 c02 c03 c04 c05 c06 c07
                             c10 c11 c12 c13 c14 c15 c16 c17
                             out0 out1
                             s10
                             a210.0 a21.0 a20.0 a2.0 a10.0 a1.0 a0.0 a.0
                             a210.1 a21.1 a20.1 a2.1 a10.1 a1.1 a0.1 a.1))))

; We start by proving that the circuit implements the specification
; (if the circuit has solutions).
; This is the proof direction that never requires any witness finding.
; We start by showing that the core predicate,
; which includes the auxiliary variables,
; implies the specification;
; this is the core of this proof direction,
; as proving the theorem for the existentially quantified predicate
; is straightfoward (see below).
;
; The proof is by 8 cases on S0, S1, and S2,
; which are obtained by expanding BITP.
;
; We also need to disable the rule that turns x + x into 2 * x,
; because that interferes with the normalization strategy
; embodied by the bind-free rules included in this book.
; The README.txt of the prime fields library lists
; two alternative sets of books to deal with equalities of sums:
; here we use the bind-free alternative;
; the other one does not work here.

(defruled circuit-core-implies-spec
  (implies (and (precond s2 s1 s0
                         c00 c01 c02 c03 c04 c05 c06 c07
                         c10 c11 c12 c13 c14 c15 c16 c17
                         out0 out1)
                (auxp s10
                      a210.0 a21.0 a20.0 a2.0 a10.0 a1.0 a0.0 a.0
                      a210.1 a21.1 a20.1 a2.1 a10.1 a1.1 a0.1 a.1)
                (circuit-core s2 s1 s0
                              c00 c01 c02 c03 c04 c05 c06 c07
                              c10 c11 c12 c13 c14 c15 c16 c17
                              out0 out1
                              s10
                              a210.0 a21.0 a20.0 a2.0 a10.0 a1.0 a0.0 a.0
                              a210.1 a21.1 a20.1 a2.1 a10.1 a1.1 a0.1 a.1))
           (spec s2 s1 s0
                 c00 c01 c02 c03 c04 c05 c06 c07
                 c10 c11 c12 c13 c14 c15 c16 c17
                 out0 out1))
  :enable (precond
           auxp
           circuit-core
           r1cs::r1cs-holdsp
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           spec
           multimux3-2
           (:e baby-jubjub-prime))
  :disable (pfield::add-of-add-same)
  :prep-books ((include-book "kestrel/prime-fields/bind-free-rules" :dir :system)))

; With the proof for the core circuit predicate in hand,
; the proof for the existentially quantified predicate is mechanical:
; we just instantiate the theorem for the core circuit
; with the witnesses for the DEFUN-SK (this is standard for DEFUN-SK).

(defruled circuit-implies-spec
  (implies (and (precond s2 s1 s0
                         c00 c01 c02 c03 c04 c05 c06 c07
                         c10 c11 c12 c13 c14 c15 c16 c17
                         out0 out1)
                (circuit s2 s1 s0
                         c00 c01 c02 c03 c04 c05 c06 c07
                         c10 c11 c12 c13 c14 c15 c16 c17
                         out0 out1))
           (spec s2 s1 s0
                 c00 c01 c02 c03 c04 c05 c06 c07
                 c10 c11 c12 c13 c14 c15 c16 c17
                 out0 out1))
  :enable circuit
  :use (:instance circuit-core-implies-spec
        (s10 (mv-nth 0 (circuit-witness s2 s1 s0
                                        c00 c01 c02 c03 c04 c05 c06 c07
                                        c10 c11 c12 c13 c14 c15 c16 c17
                                        out0 out1)))
        (a210.0 (mv-nth 1 (circuit-witness s2 s1 s0
                                           c00 c01 c02 c03 c04 c05 c06 c07
                                           c10 c11 c12 c13 c14 c15 c16 c17
                                           out0 out1)))
        (a21.0 (mv-nth 2 (circuit-witness s2 s1 s0
                                          c00 c01 c02 c03 c04 c05 c06 c07
                                          c10 c11 c12 c13 c14 c15 c16 c17
                                          out0 out1)))
        (a20.0 (mv-nth 3 (circuit-witness s2 s1 s0
                                          c00 c01 c02 c03 c04 c05 c06 c07
                                          c10 c11 c12 c13 c14 c15 c16 c17
                                          out0 out1)))
        (a2.0 (mv-nth 4 (circuit-witness s2 s1 s0
                                         c00 c01 c02 c03 c04 c05 c06 c07
                                         c10 c11 c12 c13 c14 c15 c16 c17
                                         out0 out1)))
        (a10.0 (mv-nth 5 (circuit-witness s2 s1 s0
                                          c00 c01 c02 c03 c04 c05 c06 c07
                                          c10 c11 c12 c13 c14 c15 c16 c17
                                          out0 out1)))
        (a1.0 (mv-nth 6 (circuit-witness s2 s1 s0
                                         c00 c01 c02 c03 c04 c05 c06 c07
                                         c10 c11 c12 c13 c14 c15 c16 c17
                                         out0 out1)))
        (a0.0 (mv-nth 7 (circuit-witness s2 s1 s0
                                         c00 c01 c02 c03 c04 c05 c06 c07
                                         c10 c11 c12 c13 c14 c15 c16 c17
                                         out0 out1)))
        (a.0 (mv-nth 8 (circuit-witness s2 s1 s0
                                        c00 c01 c02 c03 c04 c05 c06 c07
                                        c10 c11 c12 c13 c14 c15 c16 c17
                                        out0 out1)))
        (a210.1 (mv-nth 9 (circuit-witness s2 s1 s0
                                           c00 c01 c02 c03 c04 c05 c06 c07
                                           c10 c11 c12 c13 c14 c15 c16 c17
                                           out0 out1)))
        (a21.1 (mv-nth 10 (circuit-witness s2 s1 s0
                                           c00 c01 c02 c03 c04 c05 c06 c07
                                           c10 c11 c12 c13 c14 c15 c16 c17
                                           out0 out1)))
        (a20.1 (mv-nth 11 (circuit-witness s2 s1 s0
                                           c00 c01 c02 c03 c04 c05 c06 c07
                                           c10 c11 c12 c13 c14 c15 c16 c17
                                           out0 out1)))
        (a2.1 (mv-nth 12 (circuit-witness s2 s1 s0
                                          c00 c01 c02 c03 c04 c05 c06 c07
                                          c10 c11 c12 c13 c14 c15 c16 c17
                                          out0 out1)))
        (a10.1 (mv-nth 13 (circuit-witness s2 s1 s0
                                           c00 c01 c02 c03 c04 c05 c06 c07
                                           c10 c11 c12 c13 c14 c15 c16 c17
                                           out0 out1)))
        (a1.1 (mv-nth 14 (circuit-witness s2 s1 s0
                                          c00 c01 c02 c03 c04 c05 c06 c07
                                          c10 c11 c12 c13 c14 c15 c16 c17
                                          out0 out1)))
        (a0.1 (mv-nth 15 (circuit-witness s2 s1 s0
                                          c00 c01 c02 c03 c04 c05 c06 c07
                                          c10 c11 c12 c13 c14 c15 c16 c17
                                          out0 out1)))
        (a.1 (mv-nth 16 (circuit-witness s2 s1 s0
                                         c00 c01 c02 c03 c04 c05 c06 c07
                                         c10 c11 c12 c13 c14 c15 c16 c17
                                         out0 out1)))))

; Next, we prove that the circuit has solutions,
; at least for the inputs and outputs that satisfy the specification
; (which are all the cases in which we need the circuit to have solutions).
; This is the proof direction that requires witness finding.
; Looking at the Circom code, the witness is straightforward:
; we simply write the Circom equations, which define each auxiliary variable.

(defun s10 (s1 s0)
  (pfmul s1 s0))

(defun a210.0 (s10 c00 c01 c02 c03 c04 c05 c06 c07)
  (pfmul (pfaddall c07
                   (pfneg c06)
                   (pfneg c05)
                   c04
                   (pfneg c03)
                   c02
                   c01
                   (pfneg c00))
         s10))

(defun a21.0 (s1 c00 c02 c04 c06)
  (pfmul (pfaddall c06
                   (pfneg c04)
                   (pfneg c02)
                   c00)
         s1))

(defun a20.0 (s0 c00 c01 c04 c05)
  (pfmul (pfaddall c05
                   (pfneg c04)
                   (pfneg c01)
                   c00)
         s0))

(defun a2.0 (c00 c04)
  (pfadd c04
         (pfneg c00)))

(defun a10.0 (s10 c00 c01 c02 c03)
  (pfmul (pfaddall c03
                   (pfneg c02)
                   (pfneg c01)
                   c00)
         s10))

(defun a1.0 (s1 c00 c02)
  (pfmul (pfadd c02
                (pfneg c00))
         s1))

(defun a0.0 (s0 c00 c01)
  (pfmul (pfadd c01
                (pfneg c00))
         s0))

(defun a.0 (c00)
  c00)

(defun a210.1 (s10 c10 c11 c12 c13 c14 c15 c16 c17)
  (pfmul (pfaddall c17
                   (pfneg c16)
                   (pfneg c15)
                   c14
                   (pfneg c13)
                   c12
                   c11
                   (pfneg c10))
         s10))

(defun a21.1 (s1 c10 c12 c14 c16)
  (pfmul (pfaddall c16
                   (pfneg c14)
                   (pfneg c12)
                   c10)
         s1))

(defun a20.1 (s0 c10 c11 c14 c15)
  (pfmul (pfaddall c15
                   (pfneg c14)
                   (pfneg c11)
                   c10)
         s0))

(defun a2.1 (c10 c14)
  (pfadd c14
         (pfneg c10)))

(defun a10.1 (s10 c10 c11 c12 c13)
  (pfmul (pfaddall c13
                   (pfneg c12)
                   (pfneg c11)
                   c10)
         s10))

(defun a1.1 (s1 c10 c12)
  (pfmul (pfadd c12
                (pfneg c10))
         s1))

(defun a0.1 (s0 c10 c11)
  (pfmul (pfadd c11
                (pfneg c10))
         s0))

(defun a.1 (c10)
  c10)

; The proof is straightforward, by 8 cases on S0, S1, and S2.
; We just need to enable the R1CS semantic functions.
; We use the bind-free rules (see README.txt in the prime fields library),
; but also the alternative rules (listed in the README.txt) work here.

(defruled spec-implies-circuit-core
  (implies (and (precond s2 s1 s0
                         c00 c01 c02 c03 c04 c05 c06 c07
                         c10 c11 c12 c13 c14 c15 c16 c17
                         out0 out1)
                (spec s2 s1 s0
                      c00 c01 c02 c03 c04 c05 c06 c07
                      c10 c11 c12 c13 c14 c15 c16 c17
                      out0 out1))
           (b* ((s10 (s10 s1 s0))
                (a210.0 (a210.0 s10 c00 c01 c02 c03 c04 c05 c06 c07))
                (a21.0 (a21.0 s1 c00 c02 c04 c06))
                (a20.0 (a20.0 s0 c00 c01 c04 c05))
                (a2.0 (a2.0 c00 c04))
                (a10.0 (a10.0 s10 c00 c01 c02 c03))
                (a1.0 (a1.0 s1 c00 c02))
                (a0.0 (a0.0 s0 c00 c01))
                (a.0 (a.0 c00))
                (a210.1 (a210.1 s10 c10 c11 c12 c13 c14 c15 c16 c17))
                (a21.1 (a21.1 s1 c10 c12 c14 c16))
                (a20.1 (a20.1 s0 c10 c11 c14 c15))
                (a2.1 (a2.1 c10 c14))
                (a10.1 (a10.1 s10 c10 c11 c12 c13))
                (a1.1 (a1.1 s1 c10 c12))
                (a0.1 (a0.1 s0 c10 c11))
                (a.1 (a.1 c10)))
             (circuit-core s2 s1 s0
                           c00 c01 c02 c03 c04 c05 c06 c07
                           c10 c11 c12 c13 c14 c15 c16 c17
                           out0 out1
                           s10
                           a210.0 a21.0 a20.0 a2.0 a10.0 a1.0 a0.0 a.0
                           a210.1 a21.1 a20.1 a2.1 a10.1 a1.1 a0.1 a.1)))
  :enable (precond
           spec
           multimux3-2
           circuit-core
           r1cs::r1cs-holdsp
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           (:e baby-jubjub-prime))
  :prep-books ((include-book "kestrel/prime-fields/bind-free-rules" :dir :system)))

; In order to use the theorem just proved
; to prove that the existentially quantified circuit predicate has solutions,
; we need to establish the AUXP hypothesis of CIRCUIT-SUFF,
; which we do as follows.
; That is, under the precondition,
; the witnesses are all field elements.

(defruled auxp-when-precond
  (implies (precond s2 s1 s0
                    c00 c01 c02 c03 c04 c05 c06 c07
                    c10 c11 c12 c13 c14 c15 c16 c17
                    out0 out1)
           (b* ((s10 (s10 s1 s0))
                (a210.0 (a210.0 s10 c00 c01 c02 c03 c04 c05 c06 c07))
                (a21.0 (a21.0 s1 c00 c02 c04 c06))
                (a20.0 (a20.0 s0 c00 c01 c04 c05))
                (a2.0 (a2.0 c00 c04))
                (a10.0 (a10.0 s10 c00 c01 c02 c03))
                (a1.0 (a1.0 s1 c00 c02))
                (a0.0 (a0.0 s0 c00 c01))
                (a.0 (a.0 c00))
                (a210.1 (a210.1 s10 c10 c11 c12 c13 c14 c15 c16 c17))
                (a21.1 (a21.1 s1 c10 c12 c14 c16))
                (a20.1 (a20.1 s0 c10 c11 c14 c15))
                (a2.1 (a2.1 c10 c14))
                (a10.1 (a10.1 s10 c10 c11 c12 c13))
                (a1.1 (a1.1 s1 c10 c12))
                (a0.1 (a0.1 s0 c10 c11))
                (a.1 (a.1 c10)))
             (auxp s10
                   a210.0 a21.0 a20.0 a2.0 a10.0 a1.0 a0.0 a.0
                   a210.1 a21.1 a20.1 a2.1 a10.1 a1.1 a0.1 a.1)))
  :enable (precond auxp))

; Given the proof for the core circuit predicate above,
; the proof for the existentially quantified circuit predicate is mechanical.

(defruled spec-implies-circuit
  (implies (and (precond s2 s1 s0
                         c00 c01 c02 c03 c04 c05 c06 c07
                         c10 c11 c12 c13 c14 c15 c16 c17
                         out0 out1)
                (spec s2 s1 s0
                      c00 c01 c02 c03 c04 c05 c06 c07
                      c10 c11 c12 c13 c14 c15 c16 c17
                      out0 out1))
           (circuit s2 s1 s0
                    c00 c01 c02 c03 c04 c05 c06 c07
                    c10 c11 c12 c13 c14 c15 c16 c17
                    out0 out1))
  :enable (spec-implies-circuit-core
           auxp-when-precond)
  :disable (s10
            a210.0 a21.0 a20.0 a2.0 a10.0 a1.0 a0.0 a.0
            a210.1 a21.1 a20.1 a2.1 a10.1 a1.1 a0.1 a.1)
  :use (:instance circuit-suff
        (s10 (s10 s1 s0))
        (a210.0 (a210.0 (s10 s1 s0) c00 c01 c02 c03 c04 c05 c06 c07))
        (a21.0 (a21.0 s1 c00 c02 c04 c06))
        (a20.0 (a20.0 s0 c00 c01 c04 c05))
        (a2.0 (a2.0 c00 c04))
        (a10.0 (a10.0 (s10 s1 s0) c00 c01 c02 c03))
        (a1.0 (a1.0 s1 c00 c02))
        (a0.0 (a0.0 s0 c00 c01))
        (a.0 (a.0 c00))
        (a210.1 (a210.1 (s10 s1 s0) c10 c11 c12 c13 c14 c15 c16 c17))
        (a21.1 (a21.1 s1 c10 c12 c14 c16))
        (a20.1 (a20.1 s0 c10 c11 c14 c15))
        (a2.1 (a2.1 c10 c14))
        (a10.1 (a10.1 (s10 s1 s0) c10 c11 c12 c13))
        (a1.1 (a1.1 s1 c10 c12))
        (a0.1 (a0.1 s0 c10 c11))
        (a.1 (a.1 c10))))

; Given that we have proved both directions of the equivalence,
; we can easily show that, under the precondition,
; the circuit is equivalent to the specification.

(defruled circuit-is-spec
  (implies (precond s2 s1 s0
                    c00 c01 c02 c03 c04 c05 c06 c07
                    c10 c11 c12 c13 c14 c15 c16 c17
                    out0 out1)
           (equal (circuit s2 s1 s0
                           c00 c01 c02 c03 c04 c05 c06 c07
                           c10 c11 c12 c13 c14 c15 c16 c17
                           out0 out1)
                  (spec s2 s1 s0
                        c00 c01 c02 c03 c04 c05 c06 c07
                        c10 c11 c12 c13 c14 c15 c16 c17
                        out0 out1)))
  :use (circuit-implies-spec spec-implies-circuit))
