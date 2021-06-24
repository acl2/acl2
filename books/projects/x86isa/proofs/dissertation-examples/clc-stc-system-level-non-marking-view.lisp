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

(include-book "sys-view/non-marking-view-top" :dir :proof-utils :ttags :all)

(include-book "centaur/bitops/ihs-extensions" :dir :system)
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

;; ======================================================================

(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::use-trivial-ancestors-check))

(defconst *program*
  '(#xf8 ;; CLC
    #xf9 ;; STC
    ))

(defun-nx preconditions (x86)
  (and
   ;; The x86 state is well-formed.
   (x86p x86)
   ;; The model is operating in 64-bit mode.
   (64-bit-modep x86)
   ;; The model is operating in the system-level non-marking view.
   (not (app-view x86))
   (not (marking-view x86))
   ;; The program is located at linear addresses ranging from (rip
   ;; x86) to (+ -1 (len *program*) (rip x86)).
   (program-at (rip x86) *program* x86)
   ;; No error encountered when translating the programs linear
   ;; addresses to physical addresses.
   (not (mv-nth 0 (las-to-pas (len *program*) (rip x86) :x x86)))
   ;; The addresses where the program is located are canonical.
   (canonical-address-p (rip x86))
   (canonical-address-p (+ (len *program*) (rip x86)))
   ;; The initial state is error-free.
   (equal (ms x86) nil)
   (equal (fault x86) nil)))

;; (acl2::why x86-fetch-decode-execute-opener)
;; (acl2::why get-prefixes-opener-lemma-no-prefix-byte)
;; (acl2::why many-reads-with-rb-from-program-at-in-non-marking-view)

(defthm program-effects-1
  (implies (preconditions x86)
           (equal (x86-run 1 x86)
                  (!rip (+ 1 (rip x86)) (!flgi :cf 0 x86))))
  :hints (("Goal" :in-theory (e/d* (x86-cmc/clc/stc/cld/std
                                    x86-operation-mode
                                    rflag-RoWs-enables)
                                   ()))))

(defthm program-effects-2
  (implies (preconditions x86)
           (equal (x86-run 2 x86)
                  (!rip (+ 2 (xr :rip nil x86)) (!flgi :cf 1 x86))))
  :hints (("Goal" :in-theory (e/d* (x86-cmc/clc/stc/cld/std
                                    x86-operation-mode
                                    las-to-pas
                                    rflag-RoWs-enables)
                                   ()))))

;; ======================================================================
