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

(include-book "../../machine/x86"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

(defsection initialize-x86-state
  :parents (program-execution)
  :short "Initializing the x86 state for concrete program execution"

  :long "<p>The utilities in this section are meant to be used to
 initialize the x86 state when doing concrete execution or when
 bit-blasting using GL.  These are not intended for doing proofs using
 rewriting.  For utilities that help in code proofs, see the libraries
 in directory @('x86isa/proofs/utilities').</p>")

;; ======================================================================

(define n64p-byte-alistp (alst)
  :enabled t
  :parents (initialize-x86-state)
  :short "Recognizer for a list of pairs of up to 64-bit wide linear address and byte"

  (if (atom alst)
      (equal alst nil)
    (if (atom (car alst))
        nil
      (let ((addr (caar alst))
            (byte (cdar alst))
            (rest (cdr  alst)))
        (and (n64p addr)
             (n08p byte)
             (n64p-byte-alistp rest)))))
  ///

  (defthm n64p-byte-alistp-fwd-chain-to-alistp
    (implies (n64p-byte-alistp alst)
             (alistp alst))
    :rule-classes :forward-chaining))

(define load-program-into-memory
  ((n64-bytes-lst "Required to be a @(see n64p-byte-alistp)")
   x86)

  :guard (n64p-byte-alistp n64-bytes-lst)

  :parents (initialize-x86-state)

  :short "Loading a program into the model's memory"

  :long "<p>@('load-program-into-memory') expects a program
  represented in the form of a @('n64p-byte-alistp'), and loads that
  program, byte-by-byte, into the model's memory. Obviously, this
  function is not efficient, but the speed with which we load a
  program into the memory has not yet proved to be a deal-breaker in
  our experiments so far.</p>

 <p><b>Note on dealing with linear addresses emitted by GCC/LLVM:</b></p>

 <p>GCC and LLVM might not always output addresses satisfying our
 definition of @(see canonical-address-p) \(i.e., essentially
 @('i48p')\).  These tools will output 64-bit addresses.  Therefore,
 this function needs to be able to take a 64-bit address, check if it
 is canonical in the \"real\" world, and if so, convert it into a
 canonical address in our world.</p>

 <code>
 if (canonical-address-p (n64-to-i64 address))
     address = (n64-to-i64 address)
 else
     error!
 </code>"


  (cond ((endp n64-bytes-lst) (mv nil x86))
        (t
         (b* ((n64-addr (caar n64-bytes-lst))
              (byte (cdar n64-bytes-lst))
              ((mv flg addr)
               (let ((i48-addr (n64-to-i64 n64-addr)))
                 (if (canonical-address-p i48-addr)
                     (mv nil i48-addr)
                   (mv t n64-addr))))
              ((when flg)
               (mv (cons 'load-program-into-memory 'non-canonical-address) x86))
              ((mv flg x86) (wml08 addr byte x86))
              ((when flg)
               (mv (cons 'load-program-into-memory 'wml08-error) x86)))
           (load-program-into-memory (cdr n64-bytes-lst) x86))))

  ///

  (defthm x86p-mv-nth-1-load-program-into-memory
    (implies (x86p x86)
             (x86p (mv-nth 1 (load-program-into-memory n64-program-lst x86))))))

;; ======================================================================

(define rgfi-alistp (alst)
  :parents (initialize-x86-state)
  :short "Recognizer for pairs of general-purpose register indices and
  values"
  :long "<p>Note that the register values are required to be @('n64p'), as
  opposed to @('i64p') (which is what is required for @('!rgfi')).</p>"

  :enabled t
  (if (atom alst)
      (equal alst nil)
    (if (atom (car alst))
        nil
      (let ((index (caar alst))
            (value (cdar alst))
            (rest  (cdr  alst)))
        (and (natp index)
             (< index *64-bit-general-purpose-registers-len*)
             (unsigned-byte-p 64 value)
             (rgfi-alistp rest))))))

(define !rgfi-from-alist (rgf-alist x86)
  :guard (rgfi-alistp rgf-alist)
  :parents (initialize-x86-state)
  :short "Update general-purpose registers as dictated by
  @('rgf-alist'), which is required to be a @('rgfi-alistp')."

  (cond ((endp rgf-alist) x86)
        (t (let ((x86 (!rgfi (caar rgf-alist) (n64-to-i64 (cdar rgf-alist)) x86)))
             (!rgfi-from-alist (cdr rgf-alist) x86))))

  ///

  (defthm x86p-!rgfi-from-alist
    (implies (and (rgfi-alistp rgf-alist)
                  (x86p x86))
             (x86p (!rgfi-from-alist rgf-alist x86)))))

(define ctri-alistp (alst)
  :parents (initialize-x86-state)
  :short "Recognizer for pairs of control register indices and values"
  :long "<p>Note that the register values are required to be @('n64p') </p>"

  :enabled t
  (if (atom alst)
      (equal alst nil)
    (if (atom (car alst))
        nil
      (let ((index (caar alst))
            (value (cdar alst))
            (rest  (cdr  alst)))
        (and (natp index)
             (< index *control-register-names-len*)
             (unsigned-byte-p 64 value)
             (ctri-alistp rest))))))

(define !ctri-from-alist (ctr-alist x86)
  :parents (initialize-x86-state)
  :short "Update control registers as dictated by @('ctr-alist'),
  which is required to be a @('ctri-alistp')."

  :guard (ctri-alistp ctr-alist)
  (cond ((endp ctr-alist) x86)
        (t (let ((x86 (!ctri (caar ctr-alist) (cdar ctr-alist) x86)))
             (!ctri-from-alist (cdr ctr-alist) x86))))
  ///

  (defthm x86p-!ctri-from-alist
    (implies (and (ctri-alistp ctr-alist)
                  (x86p x86))
             (x86p (!ctri-from-alist ctr-alist x86)))))

(define msri-alistp (alst)
  :parents (initialize-x86-state)
  :short "Recognizer for pairs of model-specific register indices and
  values"
  :long "<p>Note that the register values are required to be @('n64p') </p>"
  :enabled t

  (if (atom alst)
      (equal alst nil)
    (if (atom (car alst))
        nil
      (let ((index (caar alst))
            (value (cdar alst))
            (rest  (cdr  alst)))
        (and (natp index)
             (< index *model-specific-register-names-len*)
             (unsigned-byte-p 64 value)
             (msri-alistp rest))))))

(define !msri-from-alist (msr-alist x86)

  :parents (initialize-x86-state)
  :short "Update model-specific registers as dictated by
  @('msr-alist'), which is required to be a @('msri-alistp')."

  :guard (msri-alistp msr-alist)

  (cond ((endp msr-alist) x86)
        (t (let ((x86 (!msri (caar msr-alist) (cdar msr-alist) x86)))
             (!msri-from-alist (cdr msr-alist) x86))))

  ///

  (defthm x86p-!msri-from-alist
    (implies (and (msri-alistp alist)
                  (x86p x86))
             (x86p (!msri-from-alist alist x86)))))

(define seg-visiblei-alistp (alst)
  :parents (initialize-x86-state)
  :short "Recognizer for pairs of segment register indices and
          values for the visible portions of the registers"
  :long "<p>Note that the register values are required to be @('n16p') </p>"
  :enabled t

  (if (atom alst)
      (equal alst nil)
    (if (atom (car alst))
        nil
      (let ((index (caar alst))
            (value (cdar alst))
            (rest  (cdr  alst)))
        (and (natp index)
             (< index *segment-register-names-len*)
             (unsigned-byte-p 16 value)
             (seg-visiblei-alistp rest))))))

(define !seg-visiblei-from-alist (seg-visible-alist x86)

  :parents (initialize-x86-state)
  :short "Update visible portion of segment registers as dictated by
  @('seg-visible-alist'), which is required to be a @('seg-visiblei-alistp')."

  :guard (seg-visiblei-alistp seg-visible-alist)

  (cond ((endp seg-visible-alist) x86)
        (t (let ((x86 (!seg-visiblei (caar seg-visible-alist)
                                     (cdar seg-visible-alist)
                                     x86)))
             (!seg-visiblei-from-alist (cdr seg-visible-alist) x86))))

  ///

  (defthm x86p-!seg-visiblei-from-alist
    (implies (and (seg-visiblei-alistp alist)
                  (x86p x86))
             (x86p (!seg-visiblei-from-alist alist x86)))))

(define seg-hiddeni-alistp (alst)
  :parents (initialize-x86-state)
  :short "Recognizer for pairs of segment register indices and
          values for the hidden portions of the registers"
  :long "<p>Note that the register values are required to be @('n112p') </p>"
  :enabled t

  (if (atom alst)
      (equal alst nil)
    (if (atom (car alst))
        nil
      (let ((index (caar alst))
            (value (cdar alst))
            (rest  (cdr  alst)))
        (and (natp index)
             (< index *segment-register-names-len*)
             (unsigned-byte-p 112 value)
             (seg-hiddeni-alistp rest))))))

(define !seg-hiddeni-from-alist (seg-hidden-alist x86)

  :parents (initialize-x86-state)
  :short "Update hidden portion of segment registers as dictated by
  @('seg-hidden-alist'), which is required to be a @('seg-hiddeni-alistp')."

  :guard (seg-hiddeni-alistp seg-hidden-alist)

  (cond ((endp seg-hidden-alist) x86)
        (t (let ((x86 (!seg-hiddeni (caar seg-hidden-alist)
                                    (cdar seg-hidden-alist)
                                    x86)))
             (!seg-hiddeni-from-alist (cdr seg-hidden-alist) x86))))

  ///

  (defthm x86p-!seg-hiddeni-from-alist
    (implies (and (seg-hiddeni-alistp alist)
                  (x86p x86))
             (x86p (!seg-hiddeni-from-alist alist x86)))))

;; ======================================================================

(define init-x86-state
  (status start-addr halt-addr
          gprs ctrs msrs seg-visibles seg-hiddens flags mem x86)

  :parents (initialize-x86-state)
  :short "A convenient function to populate the x86 state's
  instruction pointer, registers, and memory"
  :guard (and (canonical-address-p start-addr)
              (canonical-address-p halt-addr)
              (rgfi-alistp gprs)
              (ctri-alistp ctrs)
              (msri-alistp msrs)
              (seg-visiblei-alistp seg-visibles)
              (seg-hiddeni-alistp seg-hiddens)
              (n64p flags)
              (n64p-byte-alistp mem))

  :prepwork ((local (include-book "arithmetic-5/top" :dir :system)))
  :returns (mv flg
               (x86 x86p :hyp :guard))

  (b* ((x86 (!ms status x86))
       (x86 (!fault status x86))
       (x86 (!rip start-addr x86))
       ((mv flg0 x86)
        (load-program-into-memory mem x86))
       ((when flg0)
        (mv (cons 'load-program-into-memory flg0) x86))
       ((mv flg1 x86)
        (wml08 halt-addr #xF4 x86)) ;; "Fake" halt address
       ((when flg1)
        (mv (cons 'halt-addr flg0) x86))
       (x86 (!rgfi-from-alist gprs x86)) ;; General-Purpose Registers
       (x86 (!msri-from-alist msrs x86)) ;; Model-Specific Registers
       (x86 (!ctri-from-alist ctrs x86)) ;; Control Registers
       (x86 (!seg-visiblei-from-alist seg-visibles x86)) ;; Segment ...
       (x86 (!seg-hiddeni-from-alist seg-hiddens x86)) ;; ... Registers
       (x86 (!rflags (n32 flags) x86)))  ;; Initial Flags
    (mv nil x86)))

;; ======================================================================

(define init-x86-state-64 (status
                           (start-addr canonical-address-p)
                           (halt-addr canonical-address-p)
                           (gprs rgfi-alistp)
                           (ctrs ctri-alistp)
                           (msrs msri-alistp)
                           (seg-visibles seg-visiblei-alistp)
                           (seg-hiddens seg-hiddeni-alistp)
                           (flags n64p)
                           (mem n64p-byte-alistp)
                           x86)
  :returns (mv flg
               (x86 x86p :hyp :guard))
  :parents (initialize-x86-state)
  :short "A variant of @(tsee init-x86-state) that ensures 64-bit mode"
  :long
  "<p>
   After calling @(tsee init-x86-state),
   this function updates @('x86') to ensure that @(tsee 64-bit-modep) holds.
   It does so by setting IA32_EFER.LMA and CS.L to 1.
   </p>
   <p>
   The resulting state does not necessarily satisfy expected invariants
   for 64-bit mode,
   but that is also the case with @(tsee init-x86-state).
   </p>
   <p>
   In alternative, one can use just @(tsee init-x86-state)
   with appropriate model-specific and hidden segment register alists.
   But we find this function convenient for now.
   </p>"
  (b* (((mv flg x86)
        (init-x86-state status start-addr halt-addr gprs ctrs msrs
                        seg-visibles seg-hiddens flags mem x86))
       ((when flg) (mv t x86))
       ;; set IA32_EFER.LMA to 1:
       (ia32_efer (n12 (xr :msr *ia32_efer-idx* x86)))
       (ia32_efer (!ia32_efer-slice :ia32_efer-lma 1 ia32_efer))
       (x86 (xw :msr *ia32_efer-idx* (n64 ia32_efer) x86))
       ;; set CS.L to 1:
       (cs-hidden (xr :seg-hidden *cs* x86))
       (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden))
       (cs-attr (!code-segment-descriptor-attributes-layout-slice :l 1 cs-attr))
       (cs-hidden (!hidden-seg-reg-layout-slice :attr cs-attr cs-hidden))
       (x86 (xw :seg-hidden *cs* cs-hidden x86)))
    (mv nil x86))
  ///

  (defrule 64-bit-modep-of-init-x86-state-64
    (b* (((mv flg x86-new) (init-x86-state-64 status start-addr halt-addr
                                              gprs ctrs msrs
                                              seg-visibles seg-hiddens
                                              flags mem x86)))
      (implies (not flg)
               (64-bit-modep x86-new)))
    :enable (64-bit-modep)))

;; ======================================================================
