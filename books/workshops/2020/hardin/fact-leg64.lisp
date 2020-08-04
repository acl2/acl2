; Copyright (C) 2020 David S. Hardin
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Based on demo-fact.lisp
; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Adapted by Matt Kaufmann from J Moore's file, basic-demo.lsp.

(in-package "RTL")

; -----------------------------------------------------------------
; Demo of Def-Semantics and Def-Projection

; NOTE: See the following included book, demo-fact-preamble, for important
; comments pertaining to this demo.

(include-book "fact-leg64-preamble")

(set-verify-guards-eagerness 0) ; local to the book above

(in-theory (enable leg64step do_inst nextinst do_ldr do_str do_add do_addi do_cmp do_cmpi do_const do_mul do_sub do_subi do_b do_beq do_bne do_blo do_bls do_bhi do_bhs do_bmi do_bpl do_halt do_nop))

;; The following instructions are not used in the fact program, and
;; are somewhat expensive to reason about, so disable them
;; (in-theory (disable do_ASR do_LSL do_LSR))

(DEFTHM SEM-0-CORRECT-AUX-1
  (IMPLIES
       (AND (EQUAL (AG 0 (AG 'REGS S)) 1)
            (FACT-ROUTINE-LOADEDP S)
            (INTEGERP (AG 1 (AG 'REGS S)))
            (<= 0 (AG 1 (AG 'REGS S)))
            (< (AG 1 (AG 'REGS S))
               18446744073709551616)
            (EQUAL (AG 'PC S) 0))
       (EQUAL (LEG64STEPN S 5)
              (AS 'C
                  1
                  (AS 'N
                      0
                      (AS 'V
                          0
                          (AS 'Z
                              0
                              (AS 'PC
                                  0
                                  (AS 'OP1
                                      251
                                      (AS 'OP2
                                          0
                                          (AS 'OP3
                                              0
                                              (AS 'REGS
                                                  (AS 0 0 (AG 'REGS S))
                                                  (AS 'OPCODE 16 S))))))))))))
  :INSTRUCTIONS (:PROMOTE (:DIVE 1)
                          (:REWRITE LEG64STEPN)
                          :S (:REWRITE LEG64STEPN)
                          :S (:REWRITE LEG64STEPN)
                          :S (:REWRITE LEG64STEPN)
                          :S (:REWRITE LEG64STEPN)
                          :TOP
                          :S :BASH))

(DEFTHM SEM-0-CORRECT-AUX-2
 (IMPLIES
  (AND
   (INTEGERP C0)
   (<= 0 C0)
   (FACT-ROUTINE-LOADEDP S)
   (INTEGERP (AG 0 (AG 'REGS S)))
   (<= 1 (AG 0 (AG 'REGS S)))
   (< (AG 0 (AG 'REGS S))
      18446744073709551616)
   (INTEGERP (AG 1 (AG 'REGS S)))
   (<= 0 (AG 1 (AG 'REGS S)))
   (< (AG 1 (AG 'REGS S))
      18446744073709551616)
   (NOT (EQUAL (LOGAND 9223372036854775808 (AG 0 (AG 'REGS S)))
               9223372036854775808))
   (EQUAL
    (LEG64STEPN
     (AS
        'C
        1
        (AS 'N
            0
            (AS 'V
                0
                (AS 'Z
                    0
                    (AS 'PC
                        0
                        (AS 'OP1
                            251
                            (AS 'OP2
                                0
                                (AS 'OP3
                                    0
                                    (AS 'REGS
                                        (AS 0 (+ -1 (AG 0 (AG 'REGS S)))
                                            (AS 1
                                                (BITS (* (AG 0 (AG 'REGS S))
                                                         (AG 1 (AG 'REGS S)))
                                                      63 0)
                                                (AG 'REGS S)))
                                        (AS 'OPCODE 16 S))))))))))
     C0)
    S0)
   (EQUAL (AG 'PC S) 0))
  (EQUAL (LEG64STEPN S (+ 5 C0)) S0))
 :INSTRUCTIONS (:PROMOTE (:DIVE 1)
                         (:REWRITE LEG64STEPN-PLUS--THM)
                         (:DIVE 1)
                         (:REWRITE LEG64STEPN)
                         :S (:REWRITE LEG64STEPN)
                         :S (:REWRITE LEG64STEPN)
                         :S (:REWRITE LEG64STEPN)
                         :S (:REWRITE LEG64STEPN)
                         :S
                         :TOP :BASH))

(DEFTHM SEM-0-CORRECT-AUX-3
 (IMPLIES
  (AND
   (INTEGERP C0)
   (<= 0 C0)
   (FACT-ROUTINE-LOADEDP S)
   (INTEGERP (AG 0 (AG 'REGS S)))
   (<= 1 (AG 0 (AG 'REGS S)))
   (< (AG 0 (AG 'REGS S))
      18446744073709551616)
   (INTEGERP (AG 1 (AG 'REGS S)))
   (<= 0 (AG 1 (AG 'REGS S)))
   (< (AG 1 (AG 'REGS S))
      18446744073709551616)
   (EQUAL (LOGAND 9223372036854775808 (AG 0 (AG 'REGS S)))
          9223372036854775808)
   (EQUAL
    (LEG64STEPN
     (AS
        'C
        0
        (AS 'N
            1
            (AS 'V
                0
                (AS 'Z
                    0
                    (AS 'PC
                        0
                        (AS 'OP1
                            251
                            (AS 'OP2
                                0
                                (AS 'OP3
                                    0
                                    (AS 'REGS
                                        (AS 0 (+ -1 (AG 0 (AG 'REGS S)))
                                            (AS 1
                                                (BITS (* (AG 0 (AG 'REGS S))
                                                         (AG 1 (AG 'REGS S)))
                                                      63 0)
                                                (AG 'REGS S)))
                                        (AS 'OPCODE 16 S))))))))))
     C0)
    S0)
   (EQUAL (AG 'PC S) 0))
  (EQUAL (LEG64STEPN S (+ 5 C0)) S0))
 :INSTRUCTIONS (:PROMOTE (:DIVE 1)
                         (:REWRITE LEG64STEPN-PLUS--THM)
                         (:DIVE 1)
                         (:REWRITE LEG64STEPN)
                         :S (:REWRITE LEG64STEPN)
                         :S (:REWRITE LEG64STEPN)
                         :S (:REWRITE LEG64STEPN)
                         :S (:REWRITE LEG64STEPN)
                         :S
                         :TOP :BASH))

; Matt K. addition, to prevent the def-semantics form below from failing in
; ACL2(p) with waterfall-parallelism enabled:
(set-waterfall-parallelism nil)

; Here is the command that causes Codewalker to explore our program and
; create a semantic function, named SEM-0, since the initial pc is 0.

(def-semantics
  :init-pc 0
  :focus-regionp nil
  :root-name nil
  :hyps+ ((fact-routine-loadedp s)  ;;(equal (ag 'CMEM s) *program1*)
;;        (unsigned-byte-p 10 (ag 'pc s))
          (integerp (ag 0 (ag 'REGS s)))
          (>= (ag 0 (ag 'REGS s)) 1)
;;          (<= (ag 0 (ag 'REGS s)) 20)
          (< (ag 0 (ag 'REGS s)) 18446744073709551616)
          (integerp (ag 1 (ag 'REGS s)))
          (<= 0 (ag 1 (ag 'REGS s)))
          (< (ag 1 (ag 'REGS s)) 18446744073709551616)
          (< (ag 'PC s) (len (ag 'CMEM s)))
;;          (<= (len (ag 'REGS s)) 256)
          )
  :annotations nil
;;  :annotations ((clk-0 (declare (xargs :measure (clk-0-measure s))))
;;                (sem-0 (declare (xargs :measure (clk-0-measure s)))))
  )

;; ??? The following def-projection fails, but it emits a candidate fn1-loop
;; (see below) that can easily be modified to eliminate all mentions of
;; state s.  Add a simple :measure, and it can be admitted into ACL2.
;;
;; ??? If you issue an (in-theory (enable fact-routine-loadedp)) before
;; executing this, the def

;; (def-projection
;;   :new-fn FN1-LOOP
;;   :projector (ag 1 (ag 'regs s))
;;   :old-fn ACL2::SEM-0
;;   :hyps+ nil ;; ((fact-routine-loadedp s))
;; )

;; ??? Failed def-projection emits this function.  We easily remove
;; the remaining reference to the state vector, S

(DEFUN FN1-LOOP (PC ACL2::REGS0 ACL2::REGS1)
  (declare (xargs :measure (nfix ACL2::REGS0)))
 (IF
  (IF (NATP PC)
      (IF (NATP ACL2::REGS0)
          (NATP ACL2::REGS1)
          'NIL)
      'NIL)
  ;;(IF
   ;;(FACT-ROUTINE-LOADEDP S)
   (IF
    (INTEGERP ACL2::REGS0)
    (IF
     (< ACL2::REGS0 '1)
     ACL2::REGS1
     (IF
      (< ACL2::REGS0 '18446744073709551616)
      (IF
       (INTEGERP ACL2::REGS1)
       (IF
        (< ACL2::REGS1 '0)
        ACL2::REGS1
        (IF
         (< ACL2::REGS1 '18446744073709551616)
         (IF
           (ACL2-NUMBERP PC)
           (IF (< PC '7)
               (IF (EQUAL (BINARY-LOGAND '9223372036854775808
                                         ACL2::REGS0)
                          '9223372036854775808)
                   (FN1-LOOP '0
                             (IF (ACL2-NUMBERP ACL2::REGS0)
                                 (BINARY-+ '-1 ACL2::REGS0)
                                 '-1)
                             (IF (ACL2-NUMBERP ACL2::REGS1)
                                 (IF (ACL2-NUMBERP ACL2::REGS0)
                                     (BITS (BINARY-* ACL2::REGS0 ACL2::REGS1)
                                           '63
                                           '0)
                                     '0)
                                 '0))
                   (FN1-LOOP '0
                             (IF (ACL2-NUMBERP ACL2::REGS0)
                                 (BINARY-+ '-1 ACL2::REGS0)
                                 '-1)
                             (IF (ACL2-NUMBERP ACL2::REGS1)
                                 (IF (ACL2-NUMBERP ACL2::REGS0)
                                     (BITS (BINARY-* ACL2::REGS0 ACL2::REGS1)
                                           '63
                                           '0)
                                     '0)
                                 '0)))
               ACL2::REGS1)
           (IF (EQUAL (BINARY-LOGAND '9223372036854775808
                                     ACL2::REGS0)
                      '9223372036854775808)
               (FN1-LOOP '0
                         (IF (ACL2-NUMBERP ACL2::REGS0)
                             (BINARY-+ '-1 ACL2::REGS0)
                             '-1)
                         (IF (ACL2-NUMBERP ACL2::REGS1)
                             (IF (ACL2-NUMBERP ACL2::REGS0)
                                 (BITS (BINARY-* ACL2::REGS0 ACL2::REGS1)
                                       '63
                                       '0)
                                 '0)
                             '0))
               (FN1-LOOP '0
                         (IF (ACL2-NUMBERP ACL2::REGS0)
                             (BINARY-+ '-1 ACL2::REGS0)
                             '-1)
                         (IF (ACL2-NUMBERP ACL2::REGS1)
                             (IF (ACL2-NUMBERP ACL2::REGS0)
                                 (BITS (BINARY-* ACL2::REGS0 ACL2::REGS1)
                                       '63
                                       '0)
                                 '0)
                             '0))))
         ACL2::REGS1))
       ACL2::REGS1)
      ACL2::REGS1))
    ACL2::REGS1)
;;   ACL2::REGS1)
  '0))


(defun ! (n)
  (if (zp n)
      1
      (* n (! (- n 1)))))


(defthm fn1-loop-is-!-gen
  (implies (and (natp r0) (natp r1) (< r0 (expt 2 64))
                (< r1 (expt 2 64)))
           (equal (fn1-loop 0 r0 r1)
                  (bits (* r1 (! r0)) 63 0))))

(defun fn1 (r0)
    (fn1-loop 0 r0 1))

(defthm fn1-is-!
  (implies (and (natp r0) (< r0 (expt 2 64)))
           (equal (fn1 r0)
                  (bits (! r0) 63 0))))

; And because of all we know, we can immediately relate it to the
; result of running the code:


(defthm reg-1-of-program1-is-n!
  (implies
  (AND (FACT-ROUTINE-LOADEDP S)
       (INTEGERP (AG 0 (AG 'REGS S)))
       (< 0 (AG 0 (AG 'REGS S)))
       (< (AG 0 (AG 'REGS S)) (expt 2 64))
       (INTEGERP (AG 1 (AG 'REGS S)))
       (<= 0 (AG 1 (AG 'REGS S)))
       (< (AG 1 (AG 'REGS S)) (expt 2 64))
       (EQUAL (AG 'PC S) 0))
   (equal (ag 1 (ag 'regs (leg64stepn s (acl2::clk-0 s))))
          (bits (* (ag 1 (ag 'regs s)) (! (ag 0 (ag 'regs s)))) 63 0))))
