; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Shilpi Goel         <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "app-view/user-level-memory-utils" :dir :proof-utils :ttags :all)
(local (include-book "centaur/gl/gl" :dir :system))

(set-irrelevant-formals-ok t)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

;; (1) Specification: defining the expected inputs and the desired
;; output, f:

(defun ok-inputs (n x86)
  (declare (xargs :stobjs (x86)))
  (and (x86p x86)
       (natp n)
       (< n 13)))

(defun f (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      1
    (* n (f (- n 1)))))

;; ======================================================================

;; (2) Algorithm:

(defun fact-algorithm-simple (n a)
  (declare (xargs :guard (and (natp n)
                              (natp a))))
  (if (posp n)
      (let* ((a (* a n))
             (n (- n 1)))
        (if (not (equal n 0))
            (fact-algorithm-simple n a)
          a))
    1))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (local (in-theory (e/d (loghead logbitp logapp logext) ())))

  (defthm loghead-and-n32-to-i32-lemma
    (implies (and (integerp n)
                  (< 0 n))
             (< (loghead 32 (+ -1 (logext 32 n))) n))))

(defun fact-algorithm (n a)
  (declare (xargs :guard (and (n32p n) (n32p a))))
  (if (posp n)
      (let* ((a (n32 (* (n32-to-i32 a) (n32-to-i32 n))))
             (n (n32 (- (n32-to-i32 n) 1))))
        (if (not (equal n 0))
            (fact-algorithm n a)
          a))
    1))

(deflabel DEFN_fact-algorithm)

(defthm-unsigned-byte-p n32p-fact-algorithm
  :hyp (and (n32p n)
            (n32p a))
  :bound 32
  :concl (fact-algorithm n a)
  :gen-linear t
  :gen-type t)

(defthmd fact-algorithm-and-fact-algorithm-simple
  (implies (and (natp n)
                (< n 13))
           (equal (fact-algorithm n 1)
                  (fact-algorithm-simple n 1)))
  :hints (("Goal" :cases ((equal n 0)
                          (equal n 1)
                          (equal n 2)
                          (equal n 3)
                          (equal n 4)
                          (equal n 5)
                          (equal n 6)
                          (equal n 7)
                          (equal n 8)
                          (equal n 9)
                          (equal n 10)
                          (equal n 11)
                          (equal n 12)))))

;; ======================================================================

;; (3) Prove that the algorithm satisfies the specification: first
;; prove that helper is appropriately related to f and then that
;; fn is f on ok-inputs.

(defthm fact-algorithm-simple-and-f-1
 (implies (and (natp n)
                (posp n)
                (natp a))
           (equal (fact-algorithm-simple n a)
                  (* a (f n)))))

(defthm fact-algorithm-simple-and-f
  (implies (natp n)
           (equal (fact-algorithm-simple n 1)
                  (f n))))

(defthm fact-algorithm-and-f
  (implies (and (natp n)
                (< n 13))
           (equal (fact-algorithm n 1)
                  (f n)))
  :hints (("Goal" :use ((:instance fact-algorithm-and-fact-algorithm-simple)))))

(in-theory (disable fact-algorithm-simple-and-f-1
                    fact-algorithm-simple-and-f
                    fact-algorithm-and-f))

;; ======================================================================

;; (4) X86 program (make sure the algorithm, helper and fn, accurately
;; represents this program).

;; (defconst *factorial-binary*

;;   ;; edi: <n>: input to the factorial sub-routine

;;   (list
;;    ;; Section: <factorial_recursive>

;;    ;; ||Cutpoint:BEGIN||
;;    (cons #x4005f0 #x85) ;; test %edi,%edi
;;    (cons #x4005f1 #xff) ;;
;;    (cons #x4005f2 #xb8) ;; mov $0x1,%eax
;;    (cons #x4005f3 #x01) ;;
;;    (cons #x4005f4 #x00) ;;
;;    (cons #x4005f5 #x00) ;;
;;    (cons #x4005f6 #x00) ;;
;;    (cons #x4005f7 #x74) ;; je 400608 <factorial_recursive+0x18>
;;    (cons #x4005f8 #x0f) ;;
;;    (cons #x4005f9 #x0f) ;; nopl 0x0(%rax)
;;    (cons #x4005fa #x1f) ;;
;;    (cons #x4005fb #x80) ;;
;;    (cons #x4005fc #x00) ;;
;;    (cons #x4005fd #x00) ;;
;;    (cons #x4005fe #x00) ;;
;;    (cons #x4005ff #x00) ;;

;;    ;; ||Cutpoint:LOOP-INV||
;;    (cons #x400600 #x0f) ;; imul %edi,%eax
;;    (cons #x400601 #xaf) ;;
;;    (cons #x400602 #xc7) ;;
;;    (cons #x400603 #x83) ;; sub $0x1,%edi
;;    (cons #x400604 #xef) ;;
;;    (cons #x400605 #x01) ;;
;;    (cons #x400606 #x75) ;; jne 400600 <factorial_recursive+0x10>
;;    (cons #x400607 #xf8) ;;

;;    ;; ||Cutpoint:HALT||
;;    (cons #x400608 #xd6) ;; fake hlt (0xd6 is an illegal opcode)

;;    ))

(defconst *factorial_recursive*

    ;; ||Cutpoint:BEGIN||

  '(#x85 #xff                          ;;  test %edi,%edi
    #xb8 #x01 #x00 #x00 #x00           ;;  mov $0x1,%eax
    #x74 #x0f                          ;;  je <factorial_recursive+0x18>
    #x0f #x1f #x80 #x00 #x00 #x00 #x00 ;;  nopl 0x0(%rax)

    ;; ||Cutpoint:LOOP-INV||

    #x0f #xaf #xc7                     ;;  imul %edi,%eax
    #x83 #xef #x01                     ;;  sub $0x1,%edi
    #x75 #xf8                          ;;  jne ;;  <factorial_recursive+0x10>

    ;; ||Cutpoint:HALT||

    #xd6                               ;; Fake Halt (0xd6 is an illegal opcode)
))

;; The Fake Halt above could be a retq --- in order to reason about that, we'd
;; have needed preconditions about the stack being well-formed.  So we skip
;; that for now in order to keep this program proof simple.

;; ======================================================================

;; (5) Assertions at cutpoints:

(defn begin (n0 n)
  ;; Pre-condition
  (and (n32p n0)
       (n32p n)
       (equal n0 n)))

(defun loop-inv (n0 n a0 a)
  (declare (xargs :guard (and (n32p n0)
                              (n32p n)
                              (n32p a0)
                              (n32p a))))
  ;; Loop Invariant
  ;; See: (loop-inv 4 1 1 24) and (loop-inv 4 1 1 6)
  (and (n32p n0)
       (n32p n)
       ;; n and a are the values of edi and eax (resp.) just before
       ;; the imul instruction.
       (n32p a0)
       (n32p a)
       (< 0 n0)
       (equal
        (fact-algorithm n0 a0)
        (if (equal (n32 (- (n32-to-i32 n) 1)) 0)
            (n32 (* (n32-to-i32 a) (n32-to-i32 n)))
          (fact-algorithm (n32 (- (n32-to-i32 n) 1))
                          (n32 (* (n32-to-i32 a) (n32-to-i32 n))))))))

(deflabel DEFN_loop-inv)

(defun halt (n0 a)
  (declare (xargs :guard (and (n32p n0)
                              (n32p a))))
  ;; Post-Condition
  ;; a is the value of eax just before the fake halt instruction.
  (and (n32p n0)
       (equal (fact-algorithm n0 1) a)))

(defund halt-spec (n0 a)
  (declare (xargs :guard (and (n32p n0)
                              (n32p a))))
  ;; Post-Condition
  ;; a is the value of eax just before the fake halt instruction.
  (equal (f n0) a))

(defthmd halt-and-halt-spec
  (implies (and (natp n0)
                (< n0 13)
                (n32p a))
           (equal (halt n0 a)
                  (halt-spec n0 a)))
  :hints (("Goal" :in-theory (e/d (fact-algorithm-and-f
                                   halt-spec)
                                  ()))))

;; ======================================================================

;; (6) Verification Conditions:

(defthm Begin-To-Halt
  (implies (and (begin n0 n)
                (equal n0 0))
           (halt n0 1)))

(defthm Begin-To-Loop-Inv
  (implies (and (begin n0 n)
                (not (equal n 0)))
           (loop-inv n0 n 1 1)))

(defthm Loop-Inv-To-Loop-Inv
  (implies (and (loop-inv n0 n a0 a)
                (< 0 n0)
                (not (equal (n32 (- (n32-to-i32 n) 1)) 0)))
           (loop-inv n0
                     (n32 (- (n32-to-i32 n) 1))
                     a0
                     (n32 (* (n32-to-i32 a) (n32-to-i32 n))))))


(local
 (def-gl-thm Loop-Inv-to-Halt-helper
   :hyp (and (equal (n32 (- (n32-to-i32 n) 1))  0)
             (n32p n)
             (n32p a))
   :concl (equal (n32 (* (n32-to-i32 a) (n32-to-i32 n)))
                 a)
   :g-bindings
   `((n   (:g-number ,(increasing-list 0 2 33)))
     (a   (:g-number ,(increasing-list 1 2 33))))))

(defthm Loop-Inv-To-Halt
  (implies (and (loop-inv n0 n a0 a)
                (equal a0 1)
                (equal (n32 (- (n32-to-i32 n) 1)) 0))
           (halt n0 a))
  :hints (("Goal"
           :in-theory (e/d ()
                           (Loop-Inv-to-Halt-helper))
           :use ((:instance Loop-Inv-to-Halt-helper)))))

(deflabel THM_Loop-Inv-To-Halt)

;; ======================================================================

;; (7) Attaching assertions to the code:

(defun assertions (n0 addr x86)
  (declare (xargs :stobjs (x86)
                  :guard (and (n32p n0)
                              (canonical-address-p addr))
                  :guard-hints (("Goal" :in-theory
                                 (e/d
                                  (canonical-address-p signed-byte-p)
                                  ())))))
  (let* ((n (rr32 *rdi* x86))
         (a (rr32 *rax* x86)))

    (if (equal (rip x86) addr) ;; Poised to execute BEGIN
        (and (begin n0 n)
             (not (ms x86))
             (not (fault x86))
             (64-bit-modep x86)
             (app-view x86)
             ;; Program is in the memory
             (canonical-address-p addr)
             (canonical-address-p (+ addr (len *factorial_recursive*)))
             (program-at addr *factorial_recursive* x86))

      (if (equal (rip x86) (+ 16 addr)) ;; Posied to execute LOOP-INV
          (and (loop-inv n0 n 1 a)
               (not (ms x86))
               (not (fault x86))
               (64-bit-modep x86)
               (app-view x86)
               ;; Program is in the memory
               (canonical-address-p addr)
               (canonical-address-p (+ addr (len *factorial_recursive*)))
               (program-at addr *factorial_recursive* x86))

        (if (equal (rip x86) (+ 25 addr)) ;; Already executed fake HALT
            (and (halt n0 a)
                 (64-bit-modep x86)
                 (app-view x86)
                 (fault x86) ;; d6 is "fake" halt -- it causes a #UD.
                 (not (ms x86))
                 ;; Program is in the memory
                 (canonical-address-p addr)
                 (canonical-address-p (+ addr (len *factorial_recursive*)))
                 (program-at addr *factorial_recursive* x86))

          nil)))))

;; ======================================================================

;; (8) Defining the Invariant:

(include-book "misc/defpun" :dir :system)

(ACL2::defpun Inv (n0 addr x86)
  ;; Do not use a :stobjs declaration in a defpun.
  (if (or (equal (rip x86) addr)
          (equal (rip x86) (+ 16 addr))
          (equal (rip x86) (+ 25 addr)))
      (assertions n0 addr x86)
    (Inv n0 addr (x86-fetch-decode-execute x86))))

;; ======================================================================

;; (9) Proving properties of Inv:

(defthm Inv-opener
  (implies (not (or (equal (rip x86) addr)
                    (equal (rip x86) (+ 16 addr))
                    (equal (rip x86) (+ 25 addr))))
           (equal (Inv n0 addr x86)
                  (Inv n0 addr (x86-fetch-decode-execute x86)))))

(in-theory (e/d () (begin loop-inv halt)))

;; Proof of Inv-Inv-x86-Fetch-Decode-Execute generates "cluttered"
;; verification conditions as proof obligations.

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm logand-n-n=0->n=0
   (implies (natp n)
            (equal (logand n n) n))))

(defthm val-of-n0-when-loop-inv
  (implies (loop-inv n0 n a0 a)
           (< 0 n0))
  :hints (("Goal" :in-theory (e/d (loop-inv)
                                  ())))
  :rule-classes :forward-chaining)

(defthm loghead--1-is-zero
  (equal (loghead -1 x) 0))

(local
 (defthm begin-crock
   (implies (begin n0 0)
            (equal n0 0))
   :hints (("Goal" :in-theory (e/d (begin) ())))
   :rule-classes :forward-chaining))

(local (in-theory (e/d (signed-byte-p) ())))

(defthm canonical-address-p-fwd-chain
  (implies (canonical-address-p addr)
           (signed-byte-p 48 addr))
  :hints (("Goal" :in-theory (e/d (canonical-address-p)
                                  ())))
  :rule-classes :forward-chaining)

(defthm loop-inv-to-loop-inv-or-halt
  (implies (and (x86p x86)
                (not (equal (rip x86) addr))
                (equal addr (- (rip x86) 16))
                (loop-inv n0
                          (loghead 32 (rgfi *rdi* x86))
                          1
                          (loghead 32 (rgfi *rax* x86)))
                (not (ms x86))
                (not (fault x86))
                (64-bit-modep x86)
                (app-view x86)
                (canonical-address-p addr)
                (canonical-address-p (+ 25 addr))
                (program-at addr *factorial_recursive* x86))
           (inv n0 addr (x86-fetch-decode-execute x86)))
  :hints (("Goal"
           :in-theory (e/d* (check-instruction-length
                             rflag-RoWs-enables)
                            (get-prefixes-opener-lemma-group-1-prefix
                             get-prefixes-opener-lemma-group-2-prefix
                             get-prefixes-opener-lemma-group-3-prefix
                             get-prefixes-opener-lemma-group-4-prefix))
           :cases ((equal (n32 (- (n32-to-i32 (n32 (rgfi *rdi* x86))) 1)) 0)))
          ("Subgoal 2"
           :in-theory (e/d*
                       (instruction-decoding-and-spec-rules
                        rflag-RoWs-enables
                        x86-operation-mode

                        gpr-and-spec-4
                        jcc/cmovcc/setcc-spec
                        imul-spec
                        imul-spec-32
                        gpr-sub-spec-4

                        one-byte-opcode-execute
                        two-byte-opcode-execute
                        !rgfi-size
                        x86-operand-to-reg/mem
                        check-instruction-length
                        wr64
                        wr32
                        rr32
                        rr64
                        rml32
                        rml64
                        wml32
                        x86-operand-from-modr/m-and-sib-bytes
                        riml-size
                        riml32
                        riml08
                        two-byte-opcode-decode-and-execute
                        x86-effective-addr-when-64-bit-modep
                        x86-effective-addr-32/64
                        subset-p
                        ;; Flags
                        write-user-rflags
                        zf-spec
                        pf-spec32
                        sub-af-spec32
                        n32-to-i32
                        riml08
                        rr32)
                       (create-canonical-address-list
                        (create-canonical-address-list)
                        Loop-Inv-To-Loop-Inv
                        (:linear bitops::logior-<-0-linear-2)
                        (:rewrite acl2::ifix-when-not-integerp)
                        (:linear bitops::logior-<-0-linear-1)
                        get-prefixes-opener-lemma-group-1-prefix
                        get-prefixes-opener-lemma-group-2-prefix
                        get-prefixes-opener-lemma-group-3-prefix
                        get-prefixes-opener-lemma-group-4-prefix))
           :use ((:instance Loop-Inv-To-Loop-Inv
                            (n0 n0)
                            (n (loghead 32 (rgfi *rdi* x86)))
                            (a0 1)
                            (a (loghead 32 (rgfi *rax* x86))))))
          ("Subgoal 1"
           :in-theory (e/d*
                       (instruction-decoding-and-spec-rules
                        rflag-RoWs-enables
                        x86-operation-mode

                        gpr-and-spec-4
                        jcc/cmovcc/setcc-spec
                        imul-spec
                        imul-spec-32
                        gpr-sub-spec-4

                        one-byte-opcode-execute
                        !rgfi-size
                        x86-operand-to-reg/mem
                        wr64
                        wr32
                        rr32
                        rr64
                        rml32
                        rml64
                        wml32
                        x86-operand-from-modr/m-and-sib-bytes
                        check-instruction-length
                        riml-size
                        riml32
                        riml08
                        two-byte-opcode-decode-and-execute
                        x86-effective-addr-when-64-bit-modep
                        x86-effective-addr-32/64
                        subset-p
                        ;; Flags
                        write-user-rflags
                        zf-spec
                        pf-spec32
                        sub-af-spec32
                        n32-to-i32
                        rr32)
                       (create-canonical-address-list
                        (create-canonical-address-list)
                        Loop-Inv-To-Halt
                        Loop-Inv-to-Halt-helper
                        get-prefixes-opener-lemma-group-1-prefix
                        get-prefixes-opener-lemma-group-2-prefix
                        get-prefixes-opener-lemma-group-3-prefix
                        get-prefixes-opener-lemma-group-4-prefix
                        (:linear bitops::logior-<-0-linear-2)
                        (:rewrite acl2::ifix-when-not-integerp)
                        (:linear bitops::logior-<-0-linear-1)))
           :use ((:instance Loop-Inv-to-Halt-helper
                            (n (loghead 32 (rgfi *rdi* x86)))
                            (a (loghead 32 (rgfi *rax* x86))))
                 (:instance Loop-Inv-To-Halt
                            (n0 n0)
                            (n (loghead 32 (rgfi *rdi* x86)))
                            (a0 1)
                            (a (loghead 32 (rgfi *rax* x86))))))))

(defthm Inv-Inv-x86-Fetch-Decode-Execute
  (implies (and (x86p x86)
                (Inv n0 addr x86))
           (Inv n0 addr (x86-fetch-decode-execute x86)))
  :hints (("Goal" :in-theory
           (e/d*
            (instruction-decoding-and-spec-rules
             rflag-RoWs-enables
             x86-operation-mode

             gpr-and-spec-4
             jcc/cmovcc/setcc-spec

             one-byte-opcode-execute
             !rgfi-size
             x86-operand-to-reg/mem
             wr64
             wr32
             rr32
             rr64
             rme-size
             rime-size
             rml32
             rml64
             wml32
             x86-operand-from-modr/m-and-sib-bytes
             check-instruction-length
             riml-size
             riml32
             riml08
             two-byte-opcode-decode-and-execute
             x86-effective-addr-when-64-bit-modep
             x86-effective-addr-32/64
             subset-p
             ;; Flags
             write-user-rflags
             zf-spec
             pf-spec32)
            ()))
          ("Subgoal 2"
           :in-theory (e/d (x86-fetch-decode-execute
                            rr32)
                           ()))))

(deflabel THM_Inv-Inv-x86-Fetch-Decode-Execute)

(defthmd inv-x86-run-and-x86-fetch-decode-and-execute-commutative
  (implies (and (natp k)
                (x86p x86)
                (not (ms x86))
                (not (fault x86)))
           (equal (inv n0 addr (x86-run k (x86-fetch-decode-execute x86)))
                  (inv n0 addr (x86-fetch-decode-execute (x86-run k x86)))))
  :hints (("Goal" :in-theory (e/d (x86-run-and-x86-fetch-decode-and-execute-commutative)
                                  ((:meta acl2::mv-nth-cons-meta))))))

(defthm Inv-Inv-x86-run
  (implies (and (x86p x86)
                (Inv n0 addr x86))
           (Inv n0 addr (x86-run k x86)))
  :hints (("Goal" :induct (x86-run k x86)
           :in-theory (e/d (x86-run
                            inv-x86-run-and-x86-fetch-decode-and-execute-commutative)
                           (assertions
                            (:rewrite x86-fetch-decode-execute-opener)
                            (:rewrite get-prefixes-opener-lemma-no-prefix-byte)
                            (:meta acl2::mv-nth-cons-meta))))))

;; ======================================================================

;; (10) Program (Partial) Correctness:

;; Suppose the initial x86 state has RIP = #x4005f0, program
;; *factorial_recursive* loaded into the memory, and satisfies the
;; pre-condition "Begin".  Let a run from this state take the RIP to
;; #x400609.  Then this resulting state will satisfy "Halt".

(defthmd partial-correctness-of-fact-recursive-effects-helper
  (implies (and (x86p x86)
                (equal (rip x86) addr)
                (assertions n0 addr x86) ;; (Begin n0 n)
                (equal (rip (x86-run k x86)) (+ 25 addr)))
           ;; (Halt n0 a)
           (assertions n0 addr (x86-run k x86)))
  :hints (("Goal" :in-theory (e/d ()
                                  (assertions
                                   Inv-Inv-x86-run))
           :use ((:instance Inv-Inv-x86-run)))))

(defthm partial-correctness-of-fact-recursive-effects
  (implies (and (x86p x86)
                (64-bit-modep x86)
                (app-view x86)
                (equal (rip x86) addr)
                (and (begin n0 (rr32 *rdi* x86))
                     (not (ms x86))
                     (not (fault x86))
                     (canonical-address-p addr)
                     (canonical-address-p
                      (+ addr (len
                               *factorial_recursive*))))
                (program-at addr *factorial_recursive* x86)
                (equal x86-after-run (x86-run k x86))
                (equal (rip x86-after-run) (+ 25 addr)))
           (and (halt n0 (rr32 *rax* x86-after-run))
                (fault x86-after-run)
                (not (ms x86-after-run))
                (program-at addr *factorial_recursive* x86-after-run)))
  :hints (("Goal"
           :use ((:instance partial-correctness-of-fact-recursive-effects-helper)))))

(defthm partial-correctness-of-fact-recursive
  (implies (and (ok-inputs n0 x86)
                (64-bit-modep x86)
                (app-view x86)
                (equal (rip x86) addr)
                (and (begin n0 (rr32 *rdi* x86))
                     (not (ms x86))
                     (not (fault x86))
                     (canonical-address-p addr)
                     (canonical-address-p
                      (+ addr (len
                               *factorial_recursive*)))
                     (program-at addr *factorial_recursive* x86))
                (equal x86-after-run (x86-run k x86))
                (equal (rip x86-after-run) (+ 25 addr)))
           (and (halt-spec n0 (rr32 *rax* x86-after-run))
                (fault x86-after-run)
                (not (ms x86-after-run))
                (program-at addr *factorial_recursive* x86-after-run)))
  :hints (("Goal"
           :in-theory (e/d (halt-and-halt-spec) ())
           :use ((:instance partial-correctness-of-fact-recursive-effects)))))

;; ======================================================================
