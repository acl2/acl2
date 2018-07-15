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

;; ===================================================================

(in-package "X86ISA")
(include-book "x86" :ttags :all :dir :machine)
(include-book "tools/mv-nth" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

;; ======================================================================

(defsection proof-utilities
  :parents (x86isa)
  :short "Basic utilities for x86 machine-code proofs"
  )

(defsection debugging-code-proofs
  :parents (proof-utilities x86isa)
  )

;; ======================================================================
;; Some useful arithmetic theorems, currently placed here because
;; they've yet to find a good home:

(defthm loghead-unequal
  (implies (and (signed-byte-p x a)
                (signed-byte-p x b)
                (not (equal a b)))
           (equal (equal (loghead x a) (loghead x b)) nil))
  :hints
  (("Goal" :in-theory
    (e/d* (acl2::ihsext-inductions acl2::ihsext-recursive-redefs)
          (signed-byte-p)))))

(defthm putting-logior-loghead-ash-logtail-together
  (implies (and (syntaxp (quotep n))
                (unsigned-byte-p (* 2 n) x))
           (equal (logior (loghead n x)
                          (ash (logtail n x) n))
                  x))
  :hints (("Goal" :in-theory
           (e/d (loghead logtail logior-expt-to-plus-quotep)
                ()))))

;; ======================================================================

;; Adding untranslate patterns for readability while doing code
;; proofs: for example, (rgfi 0 x86) will show up as (rgfi *rax* x86).

(include-book "misc/untranslate-patterns" :dir :system)

;; General-Purpose Registers:

(defun x86-fn-untranslate (fn-prefix args-match indices names)
  (declare (xargs :guard (and (equal (len indices) (len names))
                              (true-listp args-match)
                              (nat-listp indices)
                              (true-listp names)
                              (true-listp fn-prefix))))

  (if (mbt (and (true-listp fn-prefix)
                (equal (len indices) (len names))))

      (if (endp indices)
          nil
        (cons
         `(acl2::add-untranslate-pattern-function
           (,@fn-prefix (quote ,(car indices)) ,@args-match)
           (,@fn-prefix ,(car names) ,@args-match))
         (x86-fn-untranslate
          fn-prefix args-match (cdr indices) (cdr names))))

    nil))


;; General-Purpose Registers:

(make-event
 (cons
  'progn
  (x86-fn-untranslate
   '(XR ':RGF)
   '(?x)
   (gl-int 0 1 16)
   '(*RAX* *RCX* *RDX* *RBX* *RSP* *RBP* *RSI* *RDI*
           *R8*  *R9*  *R10* *R11* *R12* *R13* *R14* *R15*))))

(make-event
 (cons
  'progn
  (x86-fn-untranslate
   '(XW ':RGF)
   '(?v ?x)
   (gl-int 0 1 16)
   '(*RAX* *RCX* *RDX* *RBX* *RSP* *RBP* *RSI* *RDI*
           *R8*  *R9*  *R10* *R11* *R12* *R13* *R14* *R15*))))

;; Segment Registers:

(make-event
 (cons
  'progn
  (x86-fn-untranslate
   '(XR ':seg)
   '(?x)
   (gl-int 0 1 6)
   '(*ES* *CS* *SS* *DS* *FS* *GS*))))

(make-event
 (cons
  'progn
  (x86-fn-untranslate
   '(XW ':seg)
   '(?v ?x)
   (gl-int 0 1 6)
   '(*ES* *CS* *SS* *DS* *FS* *GS*))))

;; Control Registers:

(make-event
 (cons
  'progn
  (x86-fn-untranslate
   '(XR ':ctr)
   '(?x)
   (gl-int 0 1 17)
   '(*CR0* *CR1* *CR2* *CR3* *CR4* *CR5* *CR6* *CR7*
           *CR8* *CR9*  *CR10* *CR11* *CR12* *CR13* *CR14* *CR15*
           *XCR0*))))

(make-event
 (cons
  'progn
  (x86-fn-untranslate
   '(XW ':ctr)
   '(?v ?x)
   (gl-int 0 1 17)
   '(*CR0* *CR1* *CR2* *CR3* *CR4* *CR5* *CR6* *CR7*
           *CR8* *CR9*  *CR10* *CR11* *CR12* *CR13* *CR14* *CR15*
           *XCR0*))))


;; Model-Specific Registers:

(make-event
 (cons
  'progn
  (x86-fn-untranslate
   '(XR ':msr)
   '(?x)
   ;; Note that in case of MSRs, the indices 0 through 7 are actually
   ;; the values of the constants *IA32_EFER-IDX*, *IA32_FS_BASE-IDX*,
   ;; and so on.

   ;; The following constants without the -IDX suffix correspond to
   ;; the correct register addresses, as specified by the Intel
   ;; manuals. See define-model-specific-registers in
   ;; portcullis/shart-dot-constants.lisp for details.
   (gl-int 0 1 7)
   '(*IA32_EFER-IDX* *IA32_FS_BASE-IDX* *IA32_GS_BASE-IDX* *IA32_KERNEL_GS_BASE-IDX*
                     *IA32_STAR-IDX* *IA32_LSTAR-IDX* *IA32_FMASK-IDX*))))

(make-event
 (cons
  'progn
  (x86-fn-untranslate
   '(XW ':msr)
   '(?v ?x)
   (gl-int 0 1 7)
   '(*IA32_EFER-IDX* *IA32_FS_BASE-IDX* *IA32_GS_BASE-IDX* *IA32_KERNEL_GS_BASE-IDX*
                     *IA32_STAR-IDX* *IA32_LSTAR-IDX* *IA32_FMASK-IDX*))))

;; Flags:

(make-event
 (cons
  'progn
  (x86-fn-untranslate
   '(flgi)
   '(?x)
   '(0 2 4 6 7 8 9 10 11 12 14 16 17 18 19 20 21)
   '(*CF* *PF* *AF* *ZF* *SF* *TF* *IF* *DF* *OF*
          *IOPL* *NT* *RF* *VM* *AC* *VIF* *VIP* *ID*))))


(make-event
 (cons
  'progn
  (x86-fn-untranslate
   '(!flgi)
   '(?v ?x)
   '(0 2 4 6 7 8 9 10 11 12 14 16 17 18 19 20 21)
   '(*CF* *PF* *AF* *ZF* *SF* *TF* *IF* *DF* *OF*
          *IOPL* *NT* *RF* *VM* *AC* *VIF* *VIP* *ID*))))

(acl2::optimize-untranslate-patterns)

;; ======================================================================
